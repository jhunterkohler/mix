use std::cmp::Ordering;
use std::error;
use std::fmt;
use std::hash::Hash;
use std::ops::Neg;

use crate::asm::{
    Instruction, InstructionIndex, InvalidInstructionError, Op, OpCode,
    Program,
};
use crate::dev::DeviceList;
use crate::dev::DeviceUnit;
use crate::emu::bus::MemMoveError;
use crate::emu::bus::{StartInputError, StartOutputError};
use crate::mem::{MemoryAddress, MemoryRange};
use crate::num::{self, Byte, FieldSpec, LocationCounter, Short, Word};

mod breakpoints;
mod bus;
mod machine;
mod register;

pub use breakpoints::*;
pub use machine::*;
pub use register::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EmulatorErrorKind {
    InvalidInstruction(InvalidInstructionError),
    IndexingOverflow,
    LoadIndexOverflow,
    IncIndexOverflow,
    NegativeShift,
    LocationOutOfBounds,
    LoadMemoryOutOfBounds(Short),
    StoreMemoryOutOfBounds(Short),
    LoadMemoryConflict(DeviceUnit, MemoryAddress),
    StoreMemoryConflict(DeviceUnit, MemoryAddress),
    DeviceOutputUnsupported,
    DeviceOutputOutOfBounds(DeviceUnit, Short),
    DeviceOutputConflict(DeviceUnit, MemoryRange),
    DeviceInputUnsupported,
    DeviceInputOutOfBounds(DeviceUnit, Short),
    DeviceInputConflict(DeviceUnit, MemoryRange),
    MoveSrcOutOfBounds(Short, Byte),
    MoveDestOutOfBounds(Short, Byte),
    MoveSrcConflict(DeviceUnit, MemoryRange),
    MoveDestConflict(DeviceUnit, MemoryRange),
    NoDevice(DeviceUnit),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EmulatorError {
    kind: EmulatorErrorKind,
}

impl EmulatorError {
    pub fn kind(&self) -> &EmulatorErrorKind {
        &self.kind
    }

    pub fn into_kind(self) -> EmulatorErrorKind {
        self.kind
    }
}

impl fmt::Display for EmulatorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl error::Error for EmulatorError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum StopReason {
    Halt,
    Breakpoint,
}

#[derive(Debug)]
pub struct Emulator {
    machine: Machine,
    clock: u64,
    bm: BreakpointManager,
    /// Raw loaded instruction.
    inst: Instruction,
    /// Location of current instruction.
    inst_location: MemoryAddress,
    /// The address field of the current address after indexing.
    inst_indexed_address: Short,
}

impl Emulator {
    pub fn new(devices: Option<DeviceList>) -> Self {
        Self {
            machine: Machine::new(devices),
            clock: 0,
            bm: Default::default(),
            inst: Default::default(),
            inst_location: Default::default(),
            inst_indexed_address: Default::default(),
        }
    }

    pub fn machine(&self) -> &Machine {
        &self.machine
    }

    pub fn machine_mut(&mut self) -> &mut Machine {
        &mut self.machine
    }

    pub fn clock(&self) -> u64 {
        self.clock
    }

    pub fn load_program(&mut self, program: &Program) {
        todo!();
    }

    pub fn add_breakpoint<C>(
        &mut self,
        kind: BreakpointKind,
        condition: C,
    ) -> BreakpointId
    where
        C: Into<Box<dyn BreakpointCondition>>,
    {
        self.bm.add_breakpoint(kind, condition.into())
    }

    pub fn remove_breakpoint(&mut self, id: BreakpointId) {
        self.bm.remove_breakpoint(id);
    }

    pub fn clear_breakpoints(&mut self) {
        self.bm.clear_breakpoints();
    }

    pub fn get_breakpoint(
        &self,
        id: BreakpointId,
    ) -> Option<BreakpointRef<'_>> {
        self.bm.get_breakpoint(id)
    }

    pub fn breakpoints(&self) -> impl Iterator<Item = BreakpointRef<'_>> {
        self.bm.breakpoints()
    }

    pub fn active_breakpoints(
        &self,
    ) -> impl Iterator<Item = BreakpointRef<'_>> {
        self.bm.active_breakpoints()
    }

    pub fn enable_breakpoint(&mut self, id: BreakpointId) {
        self.bm.set_is_enabled(id, true);
    }

    pub fn disable_breakpoint(&mut self, id: BreakpointId) {
        self.bm.set_is_enabled(id, false);
    }

    pub fn step(&mut self) -> Result<Option<StopReason>, EmulatorError> {
        if let Some(reason) = self.pre_step() {
            return Ok(Some(reason));
        }

        self.do_step()
    }

    pub fn run(&mut self) -> Result<StopReason, EmulatorError> {
        if let Some(reason) = self.pre_step() {
            return Ok(reason);
        }

        loop {
            if let Some(reason) = self.do_step()? {
                return Ok(reason);
            }
        }
    }

    fn pre_step(&mut self) -> Option<StopReason> {
        // Update tracking maps if breakpoint changes happened.
        if self.bm.needs_tracking_update() {
            self.bm.update_tracking();
        }

        // The breakpoint manager now remembers the last generation of active
        // to avoid duplicate breaking.
        self.bm.bump_active_breakpoints();

        // Track location after bumping active to not break repeatedly.
        self.bm.track_location(&self.machine, self.machine.location());

        if self.bm.has_active() { Some(StopReason::Breakpoint) } else { None }
    }

    fn do_step(&mut self) -> Result<Option<StopReason>, EmulatorError> {
        self.do_step_inner().map_err(|kind| EmulatorError { kind })
    }

    fn do_step_inner(
        &mut self,
    ) -> Result<Option<StopReason>, EmulatorErrorKind> {
        // Load instruction to execute
        self.inst_location = MemoryAddress::try_from(self.machine.location())
            .map_err(|_| EmulatorErrorKind::LocationOutOfBounds)?;

        let inst_word = self.try_mem_read(self.inst_location, None)?;
        self.inst = Instruction::try_from(inst_word)
            .map_err(|e| EmulatorErrorKind::InvalidInstruction(e))?;

        // Perform indexing. Must always do this to catch overflow errors.
        self.inst_indexed_address = self.try_indexing()?;

        // Ensure that we count 'base' execution time even if error occurs once
        // the operation begins.
        self.clock += self.inst.op().execution_time();

        // Dispatch op.
        self.dispatch_op()?;

        if self.inst.op() == Op::HLT {
            Ok(Some(StopReason::Halt))
        } else if self.bm.has_active() {
            Ok(Some(StopReason::Breakpoint))
        } else {
            Ok(None)
        }
    }

    /// Dispatch current operation.
    fn dispatch_op(&mut self) -> Result<(), EmulatorErrorKind> {
        use Instruction::*;

        match self.inst {
            NOP { .. } => {}
            ADD { field, .. } => self.op_add_sub(field, false)?,
            FADD { .. } => self.op_fadd_fsub(false)?,
            SUB { field, .. } => self.op_add_sub(field, true)?,
            FSUB { .. } => self.op_fadd_fsub(true)?,
            MUL { field, .. } => self.op_mul(field)?,
            FMUL { .. } => self.op_fmul()?,
            DIV { field, .. } => self.op_div(field)?,
            FDIV { .. } => self.op_fdiv()?,
            NUM { .. } => self.op_num(),
            CHAR { .. } => self.op_char(),
            HLT { .. } => {}
            FLOT { .. } => self.op_flot()?,
            FIX { .. } => self.op_fix()?,
            SLA { .. } => self.op_shift_a(num::machine::sla)?,
            SRA { .. } => self.op_shift_a(num::machine::sra)?,
            SLAX { .. } => self.op_shift_ax(num::machine::slax)?,
            SRAX { .. } => self.op_shift_ax(num::machine::srax)?,
            SLC { .. } => self.op_shift_ax(num::machine::slc)?,
            SRC { .. } => self.op_shift_ax(num::machine::src)?,
            SLB { .. } => self.op_shift_ax(num::machine::slb)?,
            SRB { .. } => self.op_shift_ax(num::machine::srb)?,
            MOVE { field, .. } => self.op_move(field)?,
            LDA { field, .. } => {
                self.op_load_word(field, WordReg::A, false)?
            }
            LD1 { field, .. } => {
                self.op_load_index(field, IndexReg::I1, false)?
            }
            LD2 { field, .. } => {
                self.op_load_index(field, IndexReg::I2, false)?
            }
            LD3 { field, .. } => {
                self.op_load_index(field, IndexReg::I3, false)?
            }
            LD4 { field, .. } => {
                self.op_load_index(field, IndexReg::I4, false)?
            }
            LD5 { field, .. } => {
                self.op_load_index(field, IndexReg::I5, false)?
            }
            LD6 { field, .. } => {
                self.op_load_index(field, IndexReg::I6, false)?
            }
            LDX { field, .. } => {
                self.op_load_word(field, WordReg::X, false)?
            }
            LDAN { field, .. } => {
                self.op_load_word(field, WordReg::A, true)?
            }
            LD1N { field, .. } => {
                self.op_load_index(field, IndexReg::I1, true)?
            }
            LD2N { field, .. } => {
                self.op_load_index(field, IndexReg::I2, true)?
            }
            LD3N { field, .. } => {
                self.op_load_index(field, IndexReg::I3, true)?
            }
            LD4N { field, .. } => {
                self.op_load_index(field, IndexReg::I4, true)?
            }
            LD5N { field, .. } => {
                self.op_load_index(field, IndexReg::I5, true)?
            }
            LD6N { field, .. } => {
                self.op_load_index(field, IndexReg::I6, true)?
            }
            LDXN { field, .. } => {
                self.op_load_word(field, WordReg::X, true)?
            }
            STA { field, .. } => self.op_store_word(field, WordReg::A)?,
            ST1 { field, .. } => self.op_store_index(field, IndexReg::I1)?,
            ST2 { field, .. } => self.op_store_index(field, IndexReg::I2)?,
            ST3 { field, .. } => self.op_store_index(field, IndexReg::I3)?,
            ST4 { field, .. } => self.op_store_index(field, IndexReg::I4)?,
            ST5 { field, .. } => self.op_store_index(field, IndexReg::I5)?,
            ST6 { field, .. } => self.op_store_index(field, IndexReg::I6)?,
            STX { field, .. } => self.op_store_word(field, WordReg::X)?,
            STJ { field, .. } => self.op_stj(field)?,
            STZ { field, .. } => self.op_stz(field)?,
            JBUS { field, .. } => self.op_jump_ready(field, false)?,
            IOC { field, .. } => self.op_ioc(field)?,
            IN { field, .. } => self.op_in(field)?,
            OUT { field, .. } => self.op_out(field)?,
            JRED { field, .. } => self.op_jump_ready(field, true)?,
            JMP { .. } => self.jump_for_inst(),
            JSJ { .. } => self.op_jsj(),
            JOV { .. } => self.op_jump_overflow(true),
            JNOV { .. } => self.op_jump_overflow(false),
            JL { .. } => self.op_jump_cmp_cond(Ordering::is_lt),
            JE { .. } => self.op_jump_cmp_cond(Ordering::is_eq),
            JG { .. } => self.op_jump_cmp_cond(Ordering::is_gt),
            JGE { .. } => self.op_jump_cmp_cond(Ordering::is_ge),
            JNE { .. } => self.op_jump_cmp_cond(Ordering::is_ne),
            JLE { .. } => self.op_jump_cmp_cond(Ordering::is_le),
            JAN { .. } => {
                self.op_jump_word(WordReg::A, Word::is_negative, false)
            }
            JAZ { .. } => self.op_jump_word(WordReg::A, Word::is_zero, false),
            JAP { .. } => {
                self.op_jump_word(WordReg::A, Word::is_positive, false)
            }
            JANN { .. } => {
                self.op_jump_word(WordReg::A, Word::is_negative, true)
            }
            JANZ { .. } => self.op_jump_word(WordReg::A, Word::is_zero, true),
            JANP { .. } => {
                self.op_jump_word(WordReg::A, Word::is_positive, true)
            }
            JAE { .. } => self.op_jump_word(WordReg::A, Word::is_even, false),
            JAO { .. } => self.op_jump_word(WordReg::A, Word::is_even, true),
            J1N { .. } => {
                self.op_jump_index(IndexReg::I1, Short::is_negative, false)
            }
            J1Z { .. } => {
                self.op_jump_index(IndexReg::I1, Short::is_zero, false)
            }
            J1P { .. } => {
                self.op_jump_index(IndexReg::I1, Short::is_positive, false)
            }
            J1NN { .. } => {
                self.op_jump_index(IndexReg::I1, Short::is_negative, true)
            }
            J1NZ { .. } => {
                self.op_jump_index(IndexReg::I1, Short::is_zero, true)
            }
            J1NP { .. } => {
                self.op_jump_index(IndexReg::I1, Short::is_positive, true)
            }
            J2N { .. } => {
                self.op_jump_index(IndexReg::I2, Short::is_negative, false)
            }
            J2Z { .. } => {
                self.op_jump_index(IndexReg::I2, Short::is_zero, false)
            }
            J2P { .. } => {
                self.op_jump_index(IndexReg::I2, Short::is_positive, false)
            }
            J2NN { .. } => {
                self.op_jump_index(IndexReg::I2, Short::is_negative, true)
            }
            J2NZ { .. } => {
                self.op_jump_index(IndexReg::I2, Short::is_zero, true)
            }
            J2NP { .. } => {
                self.op_jump_index(IndexReg::I2, Short::is_positive, true)
            }
            J3N { .. } => {
                self.op_jump_index(IndexReg::I3, Short::is_negative, false)
            }
            J3Z { .. } => {
                self.op_jump_index(IndexReg::I3, Short::is_zero, false)
            }
            J3P { .. } => {
                self.op_jump_index(IndexReg::I3, Short::is_positive, false)
            }
            J3NN { .. } => {
                self.op_jump_index(IndexReg::I3, Short::is_negative, true)
            }
            J3NZ { .. } => {
                self.op_jump_index(IndexReg::I3, Short::is_zero, true)
            }
            J3NP { .. } => {
                self.op_jump_index(IndexReg::I3, Short::is_positive, true)
            }
            J4N { .. } => {
                self.op_jump_index(IndexReg::I4, Short::is_negative, false)
            }
            J4Z { .. } => {
                self.op_jump_index(IndexReg::I4, Short::is_zero, false)
            }
            J4P { .. } => {
                self.op_jump_index(IndexReg::I4, Short::is_positive, false)
            }
            J4NN { .. } => {
                self.op_jump_index(IndexReg::I4, Short::is_negative, true)
            }
            J4NZ { .. } => {
                self.op_jump_index(IndexReg::I4, Short::is_zero, true)
            }
            J4NP { .. } => {
                self.op_jump_index(IndexReg::I4, Short::is_positive, true)
            }
            J5N { .. } => {
                self.op_jump_index(IndexReg::I5, Short::is_negative, false)
            }
            J5Z { .. } => {
                self.op_jump_index(IndexReg::I5, Short::is_zero, false)
            }
            J5P { .. } => {
                self.op_jump_index(IndexReg::I5, Short::is_positive, false)
            }
            J5NN { .. } => {
                self.op_jump_index(IndexReg::I5, Short::is_negative, true)
            }
            J5NZ { .. } => {
                self.op_jump_index(IndexReg::I5, Short::is_zero, true)
            }
            J5NP { .. } => {
                self.op_jump_index(IndexReg::I5, Short::is_positive, true)
            }
            J6N { .. } => {
                self.op_jump_index(IndexReg::I6, Short::is_negative, false)
            }
            J6Z { .. } => {
                self.op_jump_index(IndexReg::I6, Short::is_zero, false)
            }
            J6P { .. } => {
                self.op_jump_index(IndexReg::I6, Short::is_positive, false)
            }
            J6NN { .. } => {
                self.op_jump_index(IndexReg::I6, Short::is_negative, true)
            }
            J6NZ { .. } => {
                self.op_jump_index(IndexReg::I6, Short::is_zero, true)
            }
            J6NP { .. } => {
                self.op_jump_index(IndexReg::I6, Short::is_positive, true)
            }
            JXN { .. } => {
                self.op_jump_word(WordReg::X, Word::is_negative, false)
            }
            JXZ { .. } => self.op_jump_word(WordReg::X, Word::is_zero, false),
            JXP { .. } => {
                self.op_jump_word(WordReg::X, Word::is_positive, false)
            }
            JXNN { .. } => {
                self.op_jump_word(WordReg::X, Word::is_negative, true)
            }
            JXNZ { .. } => self.op_jump_word(WordReg::X, Word::is_zero, true),
            JXNP { .. } => {
                self.op_jump_word(WordReg::X, Word::is_positive, true)
            }
            JXE { .. } => self.op_jump_word(WordReg::X, Word::is_even, false),
            JXO { .. } => self.op_jump_word(WordReg::X, Word::is_even, true),
            INCA { .. } => self.op_inc_dec_word(WordReg::A, false),
            DECA { .. } => self.op_inc_dec_word(WordReg::A, true),
            ENTA { .. } => self.op_ent_word(WordReg::A, false),
            ENNA { .. } => self.op_ent_word(WordReg::A, true),
            INC1 { .. } => self.op_inc_dec_index(IndexReg::I1, false)?,
            DEC1 { .. } => self.op_inc_dec_index(IndexReg::I1, true)?,
            ENT1 { .. } => self.op_ent_index(IndexReg::I1, false),
            ENN1 { .. } => self.op_ent_index(IndexReg::I1, true),
            INC2 { .. } => self.op_inc_dec_index(IndexReg::I2, false)?,
            DEC2 { .. } => self.op_inc_dec_index(IndexReg::I2, true)?,
            ENT2 { .. } => self.op_ent_index(IndexReg::I2, false),
            ENN2 { .. } => self.op_ent_index(IndexReg::I2, true),
            INC3 { .. } => self.op_inc_dec_index(IndexReg::I3, false)?,
            DEC3 { .. } => self.op_inc_dec_index(IndexReg::I3, true)?,
            ENT3 { .. } => self.op_ent_index(IndexReg::I3, false),
            ENN3 { .. } => self.op_ent_index(IndexReg::I3, true),
            INC4 { .. } => self.op_inc_dec_index(IndexReg::I4, false)?,
            DEC4 { .. } => self.op_inc_dec_index(IndexReg::I4, true)?,
            ENT4 { .. } => self.op_ent_index(IndexReg::I4, false),
            ENN4 { .. } => self.op_ent_index(IndexReg::I4, true),
            INC5 { .. } => self.op_inc_dec_index(IndexReg::I5, false)?,
            DEC5 { .. } => self.op_inc_dec_index(IndexReg::I5, true)?,
            ENT5 { .. } => self.op_ent_index(IndexReg::I5, false),
            ENN5 { .. } => self.op_ent_index(IndexReg::I5, true),
            INC6 { .. } => self.op_inc_dec_index(IndexReg::I6, false)?,
            DEC6 { .. } => self.op_inc_dec_index(IndexReg::I6, true)?,
            ENT6 { .. } => self.op_ent_index(IndexReg::I6, false),
            ENN6 { .. } => self.op_ent_index(IndexReg::I6, true),
            INCX { .. } => self.op_inc_dec_word(WordReg::A, false),
            DECX { .. } => self.op_inc_dec_word(WordReg::A, true),
            ENTX { .. } => self.op_ent_word(WordReg::X, false),
            ENNX { .. } => self.op_ent_word(WordReg::X, true),
            CMPA { field, .. } => self.op_cmp_word(field, WordReg::A)?,
            FCMP { .. } => self.op_fcmp()?,
            CMP1 { field, .. } => self.op_cmp_index(field, IndexReg::I1)?,
            CMP2 { field, .. } => self.op_cmp_index(field, IndexReg::I2)?,
            CMP3 { field, .. } => self.op_cmp_index(field, IndexReg::I3)?,
            CMP4 { field, .. } => self.op_cmp_index(field, IndexReg::I4)?,
            CMP5 { field, .. } => self.op_cmp_index(field, IndexReg::I5)?,
            CMP6 { field, .. } => self.op_cmp_index(field, IndexReg::I6)?,
            CMPX { field, .. } => self.op_cmp_word(field, WordReg::X)?,
        }

        Ok(())
    }

    fn maybe_set_overflow_toggle(&mut self, do_set: bool) {
        if do_set {
            self.machine.set_overflow_toggle(true);
        }
    }

    fn reg_a(&self) -> Word {
        self.machine.registers().reg_a()
    }

    fn reg_x(&self) -> Word {
        self.machine.registers().reg_x()
    }

    fn reg_j(&self) -> LocationCounter {
        self.machine.registers().reg_j()
    }

    fn word_reg(&self, reg: WordReg) -> Word {
        self.machine.registers().word_reg(reg)
    }

    fn index_reg(&self, reg: IndexReg) -> Short {
        self.machine.registers().index_reg(reg)
    }

    fn set_reg_a(&mut self, value: Word) {
        self.machine.registers_mut().set_reg_a(value);
    }

    fn set_reg_x(&mut self, value: Word) {
        self.machine.registers_mut().set_reg_x(value);
    }

    fn set_reg_j(&mut self, value: LocationCounter) {
        self.machine.registers_mut().set_reg_j(value);
    }

    fn set_word_reg(&mut self, reg: WordReg, value: Word) {
        self.machine.registers_mut().set_word_reg(reg, value);
    }

    fn set_index_reg(&mut self, reg: IndexReg, value: Short) {
        self.machine.registers_mut().set_index_reg(reg, value);
    }

    fn try_mem_read(
        &mut self,
        address: MemoryAddress,
        field_spec: impl Into<Option<FieldSpec>>,
    ) -> Result<Word, EmulatorErrorKind> {
        let word =
            self.machine.bus().try_mem_read(address, field_spec).map_err(
                |e| EmulatorErrorKind::LoadMemoryConflict(e.unit, address),
            )?;

        self.bm.track_mem_load(&self.machine, address);
        Ok(word)
    }

    fn try_mem_write(
        &mut self,
        address: MemoryAddress,
        value: Word,
        field_spec: impl Into<Option<FieldSpec>>,
    ) -> Result<(), EmulatorErrorKind> {
        self.machine
            .bus_mut()
            .try_mem_write(address, value, field_spec)
            .map_err(|e| {
                EmulatorErrorKind::StoreMemoryConflict(e.unit, address)
            })?;

        self.bm.track_mem_store(&self.machine, address);
        Ok(())
    }

    fn try_indexing(&mut self) -> Result<Short, EmulatorErrorKind> {
        if let Some(reg) = match self.inst.index() {
            InstructionIndex::None => None,
            InstructionIndex::I1 => Some(IndexReg::I1),
            InstructionIndex::I2 => Some(IndexReg::I2),
            InstructionIndex::I3 => Some(IndexReg::I3),
            InstructionIndex::I4 => Some(IndexReg::I4),
            InstructionIndex::I5 => Some(IndexReg::I5),
            InstructionIndex::I6 => Some(IndexReg::I6),
        } {
            self.inst
                .address()
                .checked_add(self.index_reg(reg))
                .ok_or(EmulatorErrorKind::IndexingOverflow)
        } else {
            Ok(self.inst.address())
        }
    }

    fn try_load_for_inst(
        &mut self,
        field: impl Into<Option<FieldSpec>>,
    ) -> Result<Word, EmulatorErrorKind> {
        let address = self.inst_indexed_address;
        let address = MemoryAddress::try_from(address)
            .map_err(|_| EmulatorErrorKind::LoadMemoryOutOfBounds(address))?;

        self.try_mem_read(address, field)
    }

    fn try_store_for_inst(
        &mut self,
        value: Word,
        field: impl Into<Option<FieldSpec>>,
    ) -> Result<(), EmulatorErrorKind> {
        let address = self.inst_indexed_address;
        let address = MemoryAddress::try_from(address)
            .map_err(|_| EmulatorErrorKind::StoreMemoryOutOfBounds(address))?;

        self.try_mem_write(address, value, field)
    }

    fn try_get_shift_bytes_for_inst(&self) -> Result<u32, EmulatorErrorKind> {
        debug_assert!(self.inst.opcode() == OpCode::Shift);

        let bytes = self.inst_indexed_address.to_i16();
        if bytes >= 0 {
            Ok(bytes as u32)
        } else {
            Err(EmulatorErrorKind::NegativeShift)
        }
    }

    fn jump_for_inst(&mut self) {
        self.set_reg_j(LocationCounter::location_after(self.inst_location));
        self.machine.set_location(self.inst_indexed_address);
    }

    fn op_add_sub(
        &mut self,
        field: FieldSpec,
        is_sub: bool,
    ) -> Result<(), EmulatorErrorKind> {
        let ra = self.reg_a();
        let v = cond_neg(self.try_load_for_inst(field)?, is_sub);
        let (new_ra, overflow) = num::machine::add(ra, v);

        self.set_reg_a(new_ra);
        self.maybe_set_overflow_toggle(overflow);

        Ok(())
    }

    fn op_mul(&mut self, field: FieldSpec) -> Result<(), EmulatorErrorKind> {
        let ra = self.reg_a();
        let v = self.try_load_for_inst(field)?;
        let (new_ra, new_rx) = num::machine::mul(ra, v);

        self.set_reg_a(new_ra);
        self.set_reg_x(new_rx);

        Ok(())
    }

    fn op_div(&mut self, field: FieldSpec) -> Result<(), EmulatorErrorKind> {
        let ra = self.reg_a();
        let rx = self.reg_x();
        let v = self.try_load_for_inst(field)?;
        let (new_ra, new_rx, overflow) = num::machine::div(ra, rx, v);

        self.set_reg_a(new_ra);
        self.set_reg_x(new_rx);
        self.maybe_set_overflow_toggle(overflow);

        Ok(())
    }

    fn op_num(&mut self) {
        let new_ra = num::machine::num(self.reg_a(), self.reg_x());
        self.set_reg_a(new_ra);
    }

    fn op_char(&mut self) {
        let (new_ra, new_rx) = num::machine::char(self.reg_a(), self.reg_x());
        self.set_reg_a(new_ra);
        self.set_reg_x(new_rx);
    }

    fn op_fadd_fsub(&mut self, is_sub: bool) -> Result<(), EmulatorErrorKind> {
        let ra = self.reg_a();
        let v = cond_neg(self.try_load_for_inst(None)?, is_sub);
        let (new_ra, overflow) = num::machine::fadd(ra, v);

        self.set_reg_a(new_ra);
        self.maybe_set_overflow_toggle(overflow);

        Ok(())
    }

    fn op_fmul(&mut self) -> Result<(), EmulatorErrorKind> {
        let ra = self.reg_a();
        let v = self.try_load_for_inst(None)?;
        let (new_ra, overflow) = num::machine::fmul(ra, v);

        self.set_reg_a(new_ra);
        self.maybe_set_overflow_toggle(overflow);

        Ok(())
    }

    fn op_fdiv(&mut self) -> Result<(), EmulatorErrorKind> {
        let ra = self.reg_a();
        let v = self.try_load_for_inst(None)?;
        let (new_ra, overflow) = num::machine::fdiv(ra, v);

        self.set_reg_a(new_ra);
        self.maybe_set_overflow_toggle(overflow);

        Ok(())
    }

    fn op_flot(&mut self) -> Result<(), EmulatorErrorKind> {
        let ra = self.reg_a();
        let (new_ra, overflow) = num::machine::flot(ra);

        self.set_reg_a(new_ra);
        self.maybe_set_overflow_toggle(overflow);

        Ok(())
    }

    fn op_fix(&mut self) -> Result<(), EmulatorErrorKind> {
        let ra = self.reg_a();
        let (new_ra, overflow) = num::machine::fix(ra);

        self.set_reg_a(new_ra);
        self.maybe_set_overflow_toggle(overflow);

        Ok(())
    }

    fn op_fcmp(&mut self) -> Result<(), EmulatorErrorKind> {
        let ra = self.reg_a();
        let v = self.try_load_for_inst(None)?;
        let epsilon = self.try_mem_read(MemoryAddress::MIN, None)?;
        let ind = num::machine::fcmp(ra, v, epsilon);

        self.machine.set_comparison_indicator(ind);

        Ok(())
    }

    fn op_shift_a(
        &mut self,
        shift: fn(Word, u32) -> Word,
    ) -> Result<(), EmulatorErrorKind> {
        let ra = self.reg_a();
        let bytes = self.try_get_shift_bytes_for_inst()?;
        let new_ra = shift(ra, bytes);

        self.set_reg_a(new_ra);

        Ok(())
    }

    fn op_shift_ax(
        &mut self,
        shift: fn(Word, Word, u32) -> (Word, Word),
    ) -> Result<(), EmulatorErrorKind> {
        let ra = self.reg_a();
        let rx = self.reg_x();
        let bytes = self.try_get_shift_bytes_for_inst()?;
        let (new_ra, new_rx) = shift(ra, rx, bytes);

        self.set_reg_a(new_ra);
        self.set_reg_x(new_rx);

        Ok(())
    }

    fn op_move(&mut self, field: Byte) -> Result<(), EmulatorErrorKind> {
        let len = field.to_u8().into();
        let read_start = self.inst_indexed_address;
        let read_range = MemoryRange::from_short_len(read_start, len)
            .ok_or(EmulatorErrorKind::MoveSrcOutOfBounds(read_start, field))?;

        let write_start = self.machine.registers().reg_i1();
        let write_range =
            MemoryRange::from_short_len(write_start, len).ok_or(
                EmulatorErrorKind::MoveDestOutOfBounds(write_start, field),
            )?;

        self.machine.bus_mut().try_mem_move(read_range, write_range).map_err(
            |e| match e {
                MemMoveError::ReadConflict(unit) => {
                    EmulatorErrorKind::MoveSrcConflict(unit, read_range)
                }
                MemMoveError::WriteConflict(unit) => {
                    EmulatorErrorKind::MoveDestConflict(unit, write_range)
                }
            },
        )?;

        Ok(())
    }

    fn op_load_word(
        &mut self,
        field: FieldSpec,
        reg: WordReg,
        negate: bool,
    ) -> Result<(), EmulatorErrorKind> {
        let value = cond_neg(self.try_load_for_inst(field)?, negate);
        self.set_word_reg(reg, value);
        Ok(())
    }

    fn op_load_index(
        &mut self,
        field: FieldSpec,
        reg: IndexReg,
        negate: bool,
    ) -> Result<(), EmulatorErrorKind> {
        let value = cond_neg(self.try_load_for_inst(field)?, negate);
        let short_value = Short::try_from(value)
            .map_err(|_| EmulatorErrorKind::LoadIndexOverflow)?;
        self.set_index_reg(reg, short_value);
        Ok(())
    }

    fn op_store_word(
        &mut self,
        field: FieldSpec,
        reg: WordReg,
    ) -> Result<(), EmulatorErrorKind> {
        let value = self.word_reg(reg);
        self.try_store_for_inst(value, field)
    }

    fn op_store_index(
        &mut self,
        field: FieldSpec,
        reg: IndexReg,
    ) -> Result<(), EmulatorErrorKind> {
        let value = self.index_reg(reg);
        self.try_store_for_inst(value.into(), field)
    }

    fn op_stj(&mut self, field: FieldSpec) -> Result<(), EmulatorErrorKind> {
        let value = self.reg_j();
        self.try_store_for_inst(value.into(), field)
    }

    fn op_stz(&mut self, field: FieldSpec) -> Result<(), EmulatorErrorKind> {
        self.try_store_for_inst(Word::POS_ZERO, field)
    }

    fn ent_value_for_inst(&self, negate: bool) -> Short {
        let mut value = self.inst_indexed_address;

        if value.is_zero() {
            value = value.with_sign(self.inst.sign());
        }

        cond_neg(value, negate)
    }

    fn op_ent_word(&mut self, reg: WordReg, negate: bool) {
        self.set_word_reg(reg, self.ent_value_for_inst(negate).into());
    }

    fn op_ent_index(&mut self, reg: IndexReg, negate: bool) {
        self.set_index_reg(reg, self.ent_value_for_inst(negate));
    }

    fn op_inc_dec_word(&mut self, reg: WordReg, is_dec: bool) {
        let rhs = cond_neg(self.inst_indexed_address, is_dec);
        let (value, overflow) = self.word_reg(reg).overflowing_add(rhs.into());

        self.maybe_set_overflow_toggle(overflow);
        self.set_word_reg(reg, value);
    }

    fn op_inc_dec_index(
        &mut self,
        reg: IndexReg,
        is_dec: bool,
    ) -> Result<(), EmulatorErrorKind> {
        let rhs = cond_neg(self.inst_indexed_address, is_dec);
        let (value, overflow) = self.index_reg(reg).overflowing_add(rhs);

        if overflow {
            return Err(EmulatorErrorKind::IncIndexOverflow);
        }

        self.set_index_reg(reg, value);
        Ok(())
    }

    fn op_cmp_word(
        &mut self,
        field: FieldSpec,
        reg: WordReg,
    ) -> Result<(), EmulatorErrorKind> {
        let lhs = self.word_reg(reg).with_load(field);
        let rhs = self.try_load_for_inst(field)?;

        self.machine.set_comparison_indicator(lhs.cmp(&rhs));
        Ok(())
    }

    fn op_cmp_index(
        &mut self,
        field: FieldSpec,
        reg: IndexReg,
    ) -> Result<(), EmulatorErrorKind> {
        let lhs = Word::from(self.index_reg(reg)).with_load(field);
        let rhs = self.try_load_for_inst(field)?;

        self.machine.set_comparison_indicator(lhs.cmp(&rhs));
        Ok(())
    }

    fn op_jsj(&mut self) {
        self.machine.set_location(self.inst_indexed_address);
    }

    fn op_jump_overflow(&mut self, overflow_cond: bool) {
        if self.machine.overflow_toggle() == overflow_cond {
            self.jump_for_inst();
        }

        self.machine.set_overflow_toggle(false);
    }

    fn op_jump_cmp_cond(&mut self, cond: fn(Ordering) -> bool) {
        if cond(self.machine.comparison_indicator()) {
            self.jump_for_inst();
        }
    }

    fn op_jump_word(
        &mut self,
        reg: WordReg,
        cond: fn(Word) -> bool,
        negate: bool,
    ) {
        if cond(self.word_reg(reg)) != negate {
            self.jump_for_inst();
        }
    }

    fn op_jump_index(
        &mut self,
        reg: IndexReg,
        cond: fn(Short) -> bool,
        negate: bool,
    ) {
        if cond(self.index_reg(reg)) != negate {
            self.jump_for_inst();
        }
    }

    fn op_jump_ready(
        &mut self,
        unit: DeviceUnit,
        on_ready: bool,
    ) -> Result<(), EmulatorErrorKind> {
        let is_ready = self
            .machine
            .bus()
            .is_device_ready(unit)
            .map_err(|_| EmulatorErrorKind::NoDevice(unit))?;

        if is_ready == on_ready {
            self.jump_for_inst();
        }

        Ok(())
    }

    fn op_ioc(&mut self, unit: DeviceUnit) -> Result<(), EmulatorErrorKind> {
        let arg = self.inst_indexed_address;
        let block = self.reg_x();

        self.machine
            .bus_mut()
            .start_ioc(unit, arg, block)
            .map_err(|_| EmulatorErrorKind::NoDevice(unit))?;

        self.bm.track_io_control(&self.machine, unit);

        Ok(())
    }

    fn op_in(&mut self, unit: DeviceUnit) -> Result<(), EmulatorErrorKind> {
        let block = self.reg_x();
        let start = self.inst_indexed_address;
        let range =
            MemoryRange::from_short_len(start, unit.kind().block_size())
                .ok_or(EmulatorErrorKind::DeviceInputOutOfBounds(
                    unit, start,
                ))?;

        self.machine.bus_mut().start_input(unit, range, block).map_err(
            |e| match e {
                StartInputError::NoDevice => EmulatorErrorKind::NoDevice(unit),
                StartInputError::WriteConflict(other_unit) => {
                    EmulatorErrorKind::DeviceInputConflict(other_unit, range)
                }
            },
        )?;

        self.bm.track_io_input(&self.machine, unit);

        Ok(())
    }

    fn op_out(&mut self, unit: DeviceUnit) -> Result<(), EmulatorErrorKind> {
        let block = self.reg_x();
        let start = self.inst_indexed_address;
        let oob = || EmulatorErrorKind::DeviceOutputOutOfBounds(unit, start);
        let address = MemoryAddress::try_from(start).map_err(|_| oob())?;
        let range =
            MemoryRange::from_address_len(address, unit.kind().block_size())
                .ok_or_else(oob)?;

        self.machine.bus_mut().start_output(unit, range, block).map_err(
            |e| match e {
                StartOutputError::NoDevice => {
                    EmulatorErrorKind::NoDevice(unit)
                }
                StartOutputError::ReadConflict(other_unit) => {
                    EmulatorErrorKind::DeviceOutputConflict(other_unit, range)
                }
            },
        )?;

        self.bm.track_io_output(&self.machine, unit);

        Ok(())
    }
}

fn cond_neg<T: Neg<Output = T>>(value: T, negate: bool) -> T {
    if negate { -value } else { value }
}
