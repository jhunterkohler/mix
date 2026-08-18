use std::cmp::Ordering;
use std::error;
use std::fmt;
use std::hash::Hash;
use std::ops::Neg;

use crate::asm::Instruction;
use crate::asm::InstructionIndex;
use crate::asm::InvalidInstructionError;
use crate::asm::Op;
use crate::asm::OpCode;
use crate::asm::OpFieldKind;
use crate::asm::Program;
use crate::num;
use crate::num::FieldSpec;
use crate::num::LocationCounter;
use crate::num::Word;
use crate::num::{MemoryAddress, Short};

mod breakpoints;
mod dev;
mod machine;
mod memory;
mod register;

pub use breakpoints::*;
pub use dev::*;
pub use machine::*;
pub use memory::*;
pub use register::*;

#[derive(Debug)]
pub enum ErrorKind {
    WrongDeviceKind(DeviceUnit),
    DeviceError(dev::DeviceError),
    InvalidInstruction(InvalidInstructionError),
    LocationOutOfBounds,
    ReadOutOfBounds(Short),
    WriteOutOfBounds(Short),
    IndexingOverflow,
    NegativeShift,
    LoadIndexOverflow,
    IncIndexOverflow,
}

#[derive(Debug)]
pub struct Error {
    location: Short,
    kind: ErrorKind,
}

impl Error {
    pub fn location(&self) -> Short {
        self.location
    }

    pub fn kind(&self) -> &ErrorKind {
        &self.kind
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum StopReason {
    Halt,
    Breakpoint,
}

#[derive(Debug, Default)]
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
    pub fn new() -> Self {
        todo!();
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

    pub fn load(&mut self, program: &Program) {
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

    pub fn step(&mut self) -> Result<Option<StopReason>> {
        if let Some(reason) = self.pre_step() {
            return Ok(Some(reason));
        }

        self.do_step()
    }

    pub fn run(&mut self) -> Result<StopReason> {
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
        let location = self.machine.location();
        self.track().location(location);

        if self.bm.has_active() { Some(StopReason::Breakpoint) } else { None }
    }

    fn do_step(&mut self) -> Result<Option<StopReason>> {
        // Load instruction to execute
        self.inst_location = MemoryAddress::try_from(self.machine.location())
            .map_err(|_| self.make_error(ErrorKind::LocationOutOfBounds))?;

        let inst_word = self.mem_read_word(self.inst_location);
        self.inst = Instruction::try_from(inst_word)
            .map_err(|e| self.make_error(ErrorKind::InvalidInstruction(e)))?;

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

    #[rustfmt::skip]
    fn dispatch_op(&mut self) -> Result<()> {
        // Dispatch operation.
        match self.inst.op() {
            Op::NOP => {}
            Op::ADD => self.op_add_sub(false)?,
            Op::FADD => self.op_fadd_fsub(false)?,
            Op::SUB => self.op_add_sub(true)?,
            Op::FSUB => self.op_fadd_fsub(true)?,
            Op::MUL => self.op_mul()?,
            Op::FMUL => self.op_fmul()?,
            Op::DIV => self.op_div()?,
            Op::FDIV => self.op_fdiv()?,
            Op::NUM => self.op_num(),
            Op::CHAR => self.op_char(),
            Op::HLT => {}
            Op::FLOT => self.op_flot()?,
            Op::FIX => self.op_fix()?,
            Op::SLA => self.op_shift_a(num::machine::sla)?,
            Op::SRA => self.op_shift_a(num::machine::sra)?,
            Op::SLAX => self.op_shift_ax(num::machine::slax)?,
            Op::SRAX => self.op_shift_ax(num::machine::srax)?,
            Op::SLC => self.op_shift_ax(num::machine::slc)?,
            Op::SRC => self.op_shift_ax(num::machine::src)?,
            Op::SLB => self.op_shift_ax(num::machine::slb)?,
            Op::SRB => self.op_shift_ax(num::machine::srb)?,
            Op::MOVE => self.op_move()?,
            Op::LDA => self.op_load_word(WordReg::A, false)?,
            Op::LD1 => self.op_load_index(IndexReg::I1, false)?,
            Op::LD2 => self.op_load_index(IndexReg::I2, false)?,
            Op::LD3 => self.op_load_index(IndexReg::I3, false)?,
            Op::LD4 => self.op_load_index(IndexReg::I4, false)?,
            Op::LD5 => self.op_load_index(IndexReg::I5, false)?,
            Op::LD6 => self.op_load_index(IndexReg::I6, false)?,
            Op::LDX => self.op_load_word(WordReg::X, false)?,
            Op::LDAN => self.op_load_word(WordReg::A, true)?,
            Op::LD1N => self.op_load_index(IndexReg::I1, true)?,
            Op::LD2N => self.op_load_index(IndexReg::I2, true)?,
            Op::LD3N => self.op_load_index(IndexReg::I3, true)?,
            Op::LD4N => self.op_load_index(IndexReg::I4, true)?,
            Op::LD5N => self.op_load_index(IndexReg::I5, true)?,
            Op::LD6N => self.op_load_index(IndexReg::I6, true)?,
            Op::LDXN => self.op_load_word(WordReg::X, true)?,
            Op::STA => self.op_store_word(WordReg::A)?,
            Op::ST1 => self.op_store_index(IndexReg::I1)?,
            Op::ST2 => self.op_store_index(IndexReg::I2)?,
            Op::ST3 => self.op_store_index(IndexReg::I3)?,
            Op::ST4 => self.op_store_index(IndexReg::I4)?,
            Op::ST5 => self.op_store_index(IndexReg::I5)?,
            Op::ST6 => self.op_store_index(IndexReg::I6)?,
            Op::STX => self.op_store_word(WordReg::X)?,
            Op::STJ => self.op_stj()?,
            Op::STZ => self.op_stz()?,
            Op::JBUS => self.op_jump_ready(false)?,
            Op::IOC => self.op_ioc()?,
            Op::IN => self.op_in()?,
            Op::OUT => self.op_out()?,
            Op::JRED => self.op_jump_ready(true)?,
            Op::JMP => self.jump_for_inst(),
            Op::JSJ => self.op_jsj(),
            Op::JOV => self.op_jump_overflow(true),
            Op::JNOV => self.op_jump_overflow(false),
            Op::JL => self.op_jump_cmp_cond(Ordering::is_lt),
            Op::JE => self.op_jump_cmp_cond(Ordering::is_eq),
            Op::JG => self.op_jump_cmp_cond(Ordering::is_gt),
            Op::JGE => self.op_jump_cmp_cond(Ordering::is_ge),
            Op::JNE => self.op_jump_cmp_cond(Ordering::is_ne),
            Op::JLE => self.op_jump_cmp_cond(Ordering::is_le),
            Op::JAN => self.op_jump_word(WordReg::A, Word::is_negative, false),
            Op::JAZ => self.op_jump_word(WordReg::A, Word::is_zero, false),
            Op::JAP => self.op_jump_word(WordReg::A, Word::is_positive, false),
            Op::JANN => self.op_jump_word(WordReg::A, Word::is_negative, true),
            Op::JANZ => self.op_jump_word(WordReg::A, Word::is_zero, true),
            Op::JANP => self.op_jump_word(WordReg::A, Word::is_positive, true),
            Op::JAE => self.op_jump_word(WordReg::A, Word::is_even, false),
            Op::JAO => self.op_jump_word(WordReg::A, Word::is_even, true),
            Op::J1N => self.op_jump_index(IndexReg::I1, Short::is_negative, false),
            Op::J1Z => self.op_jump_index(IndexReg::I1, Short::is_zero, false),
            Op::J1P => self.op_jump_index(IndexReg::I1, Short::is_positive, false),
            Op::J1NN => self.op_jump_index(IndexReg::I1, Short::is_negative, true),
            Op::J1NZ => self.op_jump_index(IndexReg::I1, Short::is_zero, true),
            Op::J1NP => self.op_jump_index(IndexReg::I1, Short::is_positive, true),
            Op::J2N => self.op_jump_index(IndexReg::I2, Short::is_negative, false),
            Op::J2Z => self.op_jump_index(IndexReg::I2, Short::is_zero, false),
            Op::J2P => self.op_jump_index(IndexReg::I2, Short::is_positive, false),
            Op::J2NN => self.op_jump_index(IndexReg::I2, Short::is_negative, true),
            Op::J2NZ => self.op_jump_index(IndexReg::I2, Short::is_zero, true),
            Op::J2NP => self.op_jump_index(IndexReg::I2, Short::is_positive, true),
            Op::J3N => self.op_jump_index(IndexReg::I3, Short::is_negative, false),
            Op::J3Z => self.op_jump_index(IndexReg::I3, Short::is_zero, false),
            Op::J3P => self.op_jump_index(IndexReg::I3, Short::is_positive, false),
            Op::J3NN => self.op_jump_index(IndexReg::I3, Short::is_negative, true),
            Op::J3NZ => self.op_jump_index(IndexReg::I3, Short::is_zero, true),
            Op::J3NP => self.op_jump_index(IndexReg::I3, Short::is_positive, true),
            Op::J4N => self.op_jump_index(IndexReg::I4, Short::is_negative, false),
            Op::J4Z => self.op_jump_index(IndexReg::I4, Short::is_zero, false),
            Op::J4P => self.op_jump_index(IndexReg::I4, Short::is_positive, false),
            Op::J4NN => self.op_jump_index(IndexReg::I4, Short::is_negative, true),
            Op::J4NZ => self.op_jump_index(IndexReg::I4, Short::is_zero, true),
            Op::J4NP => self.op_jump_index(IndexReg::I4, Short::is_positive, true),
            Op::J5N => self.op_jump_index(IndexReg::I5, Short::is_negative, false),
            Op::J5Z => self.op_jump_index(IndexReg::I5, Short::is_zero, false),
            Op::J5P => self.op_jump_index(IndexReg::I5, Short::is_positive, false),
            Op::J5NN => self.op_jump_index(IndexReg::I5, Short::is_negative, true),
            Op::J5NZ => self.op_jump_index(IndexReg::I5, Short::is_zero, true),
            Op::J5NP => self.op_jump_index(IndexReg::I5, Short::is_positive, true),
            Op::J6N => self.op_jump_index(IndexReg::I6, Short::is_negative, false),
            Op::J6Z => self.op_jump_index(IndexReg::I6, Short::is_zero, false),
            Op::J6P => self.op_jump_index(IndexReg::I6, Short::is_positive, false),
            Op::J6NN => self.op_jump_index(IndexReg::I6, Short::is_negative, true),
            Op::J6NZ => self.op_jump_index(IndexReg::I6, Short::is_zero, true),
            Op::J6NP => self.op_jump_index(IndexReg::I6, Short::is_positive, true),
            Op::JXN => self.op_jump_word(WordReg::X, Word::is_negative, false),
            Op::JXZ => self.op_jump_word(WordReg::X, Word::is_zero, false),
            Op::JXP => self.op_jump_word(WordReg::X, Word::is_positive, false),
            Op::JXNN => self.op_jump_word(WordReg::X, Word::is_negative, true),
            Op::JXNZ => self.op_jump_word(WordReg::X, Word::is_zero, true),
            Op::JXNP => self.op_jump_word(WordReg::X, Word::is_positive, true),
            Op::JXE => self.op_jump_word(WordReg::X, Word::is_even, false),
            Op::JXO => self.op_jump_word(WordReg::X, Word::is_even, true),
            Op::INCA => self.op_inc_dec_word(WordReg::A, false),
            Op::DECA => self.op_inc_dec_word(WordReg::A, true),
            Op::ENTA => self.op_ent_word(WordReg::A, false),
            Op::ENNA => self.op_ent_word(WordReg::A, true),
            Op::INC1 => self.op_inc_dec_index(IndexReg::I1, false)?,
            Op::DEC1 => self.op_inc_dec_index(IndexReg::I1, true)?,
            Op::ENT1 => self.op_ent_index(IndexReg::I1, false),
            Op::ENN1 => self.op_ent_index(IndexReg::I1, true),
            Op::INC2 => self.op_inc_dec_index(IndexReg::I2, false)?,
            Op::DEC2 => self.op_inc_dec_index(IndexReg::I2, true)?,
            Op::ENT2 => self.op_ent_index(IndexReg::I2, false),
            Op::ENN2 => self.op_ent_index(IndexReg::I2, true),
            Op::INC3 => self.op_inc_dec_index(IndexReg::I3, false)?,
            Op::DEC3 => self.op_inc_dec_index(IndexReg::I3, true)?,
            Op::ENT3 => self.op_ent_index(IndexReg::I3, false),
            Op::ENN3 => self.op_ent_index(IndexReg::I3, true),
            Op::INC4 => self.op_inc_dec_index(IndexReg::I4, false)?,
            Op::DEC4 => self.op_inc_dec_index(IndexReg::I4, true)?,
            Op::ENT4 => self.op_ent_index(IndexReg::I4, false),
            Op::ENN4 => self.op_ent_index(IndexReg::I4, true),
            Op::INC5 => self.op_inc_dec_index(IndexReg::I5, false)?,
            Op::DEC5 => self.op_inc_dec_index(IndexReg::I5, true)?,
            Op::ENT5 => self.op_ent_index(IndexReg::I5, false),
            Op::ENN5 => self.op_ent_index(IndexReg::I5, true),
            Op::INC6 => self.op_inc_dec_index(IndexReg::I6, false)?,
            Op::DEC6 => self.op_inc_dec_index(IndexReg::I6, true)?,
            Op::ENT6 => self.op_ent_index(IndexReg::I6, false),
            Op::ENN6 => self.op_ent_index(IndexReg::I6, true),
            Op::INCX => self.op_inc_dec_word(WordReg::A, false),
            Op::DECX => self.op_inc_dec_word(WordReg::A, true),
            Op::ENTX => self.op_ent_word(WordReg::X, false),
            Op::ENNX => self.op_ent_word(WordReg::X, true),
            Op::CMPA => self.op_cmp_word(WordReg::A)?,
            Op::FCMP => self.op_fcmp()?,
            Op::CMP1 => self.op_cmp_index(IndexReg::I1)?,
            Op::CMP2 => self.op_cmp_index(IndexReg::I2)?,
            Op::CMP3 => self.op_cmp_index(IndexReg::I3)?,
            Op::CMP4 => self.op_cmp_index(IndexReg::I4)?,
            Op::CMP5 => self.op_cmp_index(IndexReg::I5)?,
            Op::CMP6 => self.op_cmp_index(IndexReg::I6)?,
            Op::CMPX => self.op_cmp_word(WordReg::X)?,
        }

        Ok(())
    }

    fn track(&mut self) -> Track<'_> {
        self.bm.track(&self.machine)
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

    fn mem_read_word(&mut self, address: MemoryAddress) -> Word {
        self.track().mem_read(address);
        self.machine.memory()[address]
    }

    fn try_indexing(&mut self) -> Result<Short> {
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
                .ok_or_else(|| self.make_error(ErrorKind::IndexingOverflow))
        } else {
            Ok(self.inst.address())
        }
    }

    fn try_load_for_inst(&mut self) -> Result<Word> {
        debug_assert!(self.inst.op().field_kind() == OpFieldKind::Word);

        let field_spec = FieldSpec::try_from(self.inst.field()).unwrap();
        let address = MemoryAddress::try_from(self.inst_indexed_address)
            .map_err(|_| {
                self.make_error(ErrorKind::ReadOutOfBounds(
                    self.inst_indexed_address,
                ))
            })?;

        self.track().mem_read(address);
        let value = self.machine.memory().load(address, field_spec);

        Ok(value)
    }

    fn try_store_for_inst(&mut self, value: Word) -> Result<()> {
        debug_assert!(self.inst.op().field_kind() == OpFieldKind::Word);

        let field_spec = FieldSpec::try_from(self.inst.field()).unwrap();
        let address = MemoryAddress::try_from(self.inst_indexed_address)
            .map_err(|_| {
                self.make_error(ErrorKind::WriteOutOfBounds(
                    self.inst_indexed_address,
                ))
            })?;

        self.track().mem_write(address);
        self.machine.memory_mut().store(address, value, field_spec);

        Ok(())
    }

    fn get_shift_bytes_for_inst(&self) -> Result<u32> {
        debug_assert!(self.inst.op().opcode() == OpCode::Shift);

        let bytes = self.inst_indexed_address.to_i16();
        if bytes >= 0 {
            Ok(bytes as u32)
        } else {
            Err(self.make_error(ErrorKind::NegativeShift))
        }
    }

    fn jump_for_inst(&mut self) {
        self.set_reg_j(LocationCounter::location_after(self.inst_location));
        self.machine.set_location(self.inst_indexed_address);
    }

    fn make_error(&self, kind: ErrorKind) -> Error {
        Error { location: self.machine.location(), kind }
    }

    fn op_add_sub(&mut self, is_sub: bool) -> Result<()> {
        let ra = self.reg_a();
        let v = cond_neg(self.try_load_for_inst()?, is_sub);
        let (new_ra, overflow) = num::machine::add(ra, v);

        self.set_reg_a(new_ra);
        self.maybe_set_overflow_toggle(overflow);

        Ok(())
    }

    fn op_mul(&mut self) -> Result<()> {
        let ra = self.reg_a();
        let v = self.try_load_for_inst()?;
        let (new_ra, new_rx) = num::machine::mul(ra, v);

        self.set_reg_a(new_ra);
        self.set_reg_x(new_rx);

        Ok(())
    }

    fn op_div(&mut self) -> Result<()> {
        let ra = self.reg_a();
        let rx = self.reg_x();
        let v = self.try_load_for_inst()?;
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

    fn op_fadd_fsub(&mut self, is_sub: bool) -> Result<()> {
        todo!();
    }

    fn op_fmul(&mut self) -> Result<()> {
        todo!()
    }

    fn op_fdiv(&mut self) -> Result<()> {
        todo!()
    }

    fn op_flot(&mut self) -> Result<()> {
        todo!()
    }

    fn op_fix(&mut self) -> Result<()> {
        todo!()
    }

    fn op_fcmp(&mut self) -> Result<()> {
        todo!();
    }

    fn op_shift_a(&mut self, shift: fn(Word, u32) -> Word) -> Result<()> {
        let ra = self.reg_a();
        let bytes = self.get_shift_bytes_for_inst()?;
        let new_ra = shift(ra, bytes);

        self.set_reg_a(new_ra);

        Ok(())
    }

    fn op_shift_ax(
        &mut self,
        shift: fn(Word, Word, u32) -> (Word, Word),
    ) -> Result<()> {
        let ra = self.reg_a();
        let rx = self.reg_x();
        let bytes = self.get_shift_bytes_for_inst()?;
        let (new_ra, new_rx) = shift(ra, rx, bytes);

        self.set_reg_a(new_ra);
        self.set_reg_x(new_rx);

        Ok(())
    }

    fn op_move(&self) -> Result<()> {
        todo!();
    }

    fn op_load_word(&mut self, reg: WordReg, negate: bool) -> Result<()> {
        let value = cond_neg(self.try_load_for_inst()?, negate);
        self.set_word_reg(reg, value);
        Ok(())
    }

    fn op_load_index(&mut self, reg: IndexReg, negate: bool) -> Result<()> {
        let value = cond_neg(self.try_load_for_inst()?, negate);
        let short_value = Short::try_from(value)
            .map_err(|_| self.make_error(ErrorKind::LoadIndexOverflow))?;
        self.set_index_reg(reg, short_value);
        Ok(())
    }

    fn op_store_word(&mut self, reg: WordReg) -> Result<()> {
        let value = self.word_reg(reg);
        self.try_store_for_inst(value)
    }

    fn op_store_index(&mut self, reg: IndexReg) -> Result<()> {
        let value = self.index_reg(reg);
        self.try_store_for_inst(value.into())
    }

    fn op_stj(&mut self) -> Result<()> {
        let value = self.reg_j();
        self.try_store_for_inst(value.into())
    }

    fn op_stz(&mut self) -> Result<()> {
        self.try_store_for_inst(Word::POS_ZERO)
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

    fn op_inc_dec_index(&mut self, reg: IndexReg, is_dec: bool) -> Result<()> {
        let rhs = cond_neg(self.inst_indexed_address, is_dec);
        let (value, overflow) = self.index_reg(reg).overflowing_add(rhs);

        if overflow {
            return Err(self.make_error(ErrorKind::IncIndexOverflow));
        }

        self.set_index_reg(reg, value);
        Ok(())
    }

    fn op_cmp_word(&mut self, reg: WordReg) -> Result<()> {
        let field_spec = FieldSpec::try_from(self.inst.field()).unwrap();
        let lhs = self.word_reg(reg).with_load(field_spec);
        let rhs = self.try_load_for_inst()?;

        self.machine.set_comparison_indicator(lhs.cmp(&rhs));
        Ok(())
    }

    fn op_cmp_index(&mut self, reg: IndexReg) -> Result<()> {
        let field_spec = FieldSpec::try_from(self.inst.field()).unwrap();
        let lhs = Word::from(self.index_reg(reg)).with_load(field_spec);
        let rhs = self.try_load_for_inst()?;

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

    // fn op_jump_ready(&mut self, on_ready: bool) {
    //     self.op_read
    // }
}

fn cond_neg<T: Neg<Output = T>>(value: T, negate: bool) -> T {
    if negate { -value } else { value }
}
