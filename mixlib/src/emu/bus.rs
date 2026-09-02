use arrayvec::ArrayVec;

use crate::dev::{Device, DeviceList, DeviceUnit};
use crate::mem::{Memory, MemoryAddress, MemoryRange};
use crate::num::{FieldSpec, Short, Word};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum DeviceOpKind {
    Control,
    Input(MemoryRange),
    Output(MemoryRange),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct DeviceOp {
    unit: DeviceUnit,
    kind: DeviceOpKind,
}

#[derive(Debug, Default)]
struct DeviceOpList {
    inner: ArrayVec<DeviceOp, { DeviceUnit::MAX.to_usize() + 1 }>,
}

impl DeviceOpList {
    fn unit_pos(&self, unit: DeviceUnit) -> Option<usize> {
        self.inner.iter().position(|op| op.unit == unit)
    }

    fn unit_pos_op(&self, unit: DeviceUnit) -> Option<(usize, DeviceOp)> {
        let pos = self.unit_pos(unit)?;
        let op = self.inner[pos];
        Some((pos, op))
    }

    fn remove_pos(&mut self, pos: usize) {
        self.inner.swap_remove(pos);
    }

    fn remove_unit(&mut self, unit: DeviceUnit) {
        if let Some(pos) = self.unit_pos(unit) {
            self.remove_pos(pos);
        }
    }

    fn add_op(&mut self, op: DeviceOp) {
        self.inner.push(op)
    }

    fn iter(&self) -> impl Iterator<Item = DeviceOp> {
        self.inner.iter().copied()
    }
}

pub struct NoDeviceError;

pub struct ReadConflictError {
    pub unit: DeviceUnit,
}

pub struct WriteConflictError {
    pub unit: DeviceUnit,
}

pub enum StartInputError {
    NoDevice,
    WriteConflict(DeviceUnit),
}

impl From<NoDeviceError> for StartInputError {
    fn from(_value: NoDeviceError) -> Self {
        StartInputError::NoDevice
    }
}

impl From<WriteConflictError> for StartInputError {
    fn from(value: WriteConflictError) -> Self {
        StartInputError::WriteConflict(value.unit)
    }
}

pub enum StartOutputError {
    NoDevice,
    ReadConflict(DeviceUnit),
}

impl From<NoDeviceError> for StartOutputError {
    fn from(_value: NoDeviceError) -> Self {
        StartOutputError::NoDevice
    }
}

impl From<ReadConflictError> for StartOutputError {
    fn from(value: ReadConflictError) -> Self {
        StartOutputError::ReadConflict(value.unit)
    }
}

pub enum MemMoveError {
    ReadConflict(DeviceUnit),
    WriteConflict(DeviceUnit),
}

impl From<ReadConflictError> for MemMoveError {
    fn from(value: ReadConflictError) -> Self {
        MemMoveError::ReadConflict(value.unit)
    }
}

impl From<WriteConflictError> for MemMoveError {
    fn from(value: WriteConflictError) -> Self {
        MemMoveError::WriteConflict(value.unit)
    }
}

#[derive(Debug, Default)]
pub struct Bus {
    devices: DeviceList,
    device_ops: DeviceOpList,
    memory: Memory,
}

impl Bus {
    pub fn new(devices: Option<DeviceList>) -> Self {
        Self {
            devices: devices.unwrap_or_default(),
            device_ops: Default::default(),
            memory: Memory::default(),
        }
    }

    pub fn memory(&self) -> &Memory {
        &self.memory
    }

    pub fn memory_mut(&mut self) -> &mut Memory {
        &mut self.memory
    }

    pub fn get_device(&self, unit: DeviceUnit) -> Option<&dyn Device> {
        self.devices.get(unit)
    }

    pub fn get_device_mut(
        &mut self,
        unit: DeviceUnit,
    ) -> Option<&mut dyn Device> {
        self.devices.get_mut(unit)
    }

    pub fn take_device(
        &mut self,
        unit: DeviceUnit,
    ) -> Option<Box<dyn Device>> {
        self.device_ops.remove_unit(unit);
        self.devices.take(unit)
    }

    pub fn replace_device(
        &mut self,
        unit: DeviceUnit,
        dev: Box<dyn Device>,
    ) -> Result<Option<Box<dyn Device>>, Box<dyn Device>> {
        self.device_ops.remove_unit(unit);
        self.devices.replace(unit, dev)
    }

    pub fn is_device_ready(
        &self,
        unit: DeviceUnit,
    ) -> Result<bool, NoDeviceError> {
        Ok(self.devices.get(unit).ok_or(NoDeviceError)?.is_ready())
    }

    pub fn start_ioc(
        &mut self,
        unit: DeviceUnit,
        arg: Short,
        block: Word,
    ) -> Result<(), NoDeviceError> {
        self.wait(unit)?;

        unsafe {
            let dev = self.devices.get_mut(unit).unwrap();
            dev.control(arg, block)
        }

        self.device_ops.add_op(DeviceOp { unit, kind: DeviceOpKind::Control });
        Ok(())
    }

    pub fn start_input(
        &mut self,
        unit: DeviceUnit,
        range: MemoryRange,
        block: Word,
    ) -> Result<(), StartInputError> {
        self.wait(unit)?;
        self.check_write(range)?;

        unsafe {
            let dev = self.devices.get_mut(unit).unwrap_unchecked();
            dev.input(block);
        }

        self.device_ops
            .add_op(DeviceOp { unit, kind: DeviceOpKind::Input(range) });
        Ok(())
    }

    pub fn start_output(
        &mut self,
        unit: DeviceUnit,
        range: MemoryRange,
        block: Word,
    ) -> Result<(), StartOutputError> {
        self.wait(unit)?;
        self.check_read(range)?;

        unsafe {
            let dev = self.devices.get_mut(unit).unwrap_unchecked();
            dev.buf_mut().copy_from_slice(&self.memory[range]);
            dev.output(block);
        }

        self.device_ops
            .add_op(DeviceOp { unit, kind: DeviceOpKind::Output(range) });
        Ok(())
    }

    pub fn wait(&mut self, unit: DeviceUnit) -> Result<(), NoDeviceError> {
        let dev = self.devices.get_mut(unit).ok_or(NoDeviceError)?;
        dev.wait();

        if let Some((pos, op)) = self.device_ops.unit_pos_op(unit) {
            if let DeviceOpKind::Input(range) = op.kind {
                self.memory[range].copy_from_slice(unsafe { dev.buf() });
            }

            self.device_ops.remove_pos(pos);
        }

        Ok(())
    }

    pub fn try_mem_read(
        &self,
        address: MemoryAddress,
        field_spec: impl Into<Option<FieldSpec>>,
    ) -> Result<Word, ReadConflictError> {
        self.check_read(address)?;
        Ok(self.memory.load(address, field_spec))
    }

    pub fn try_mem_write(
        &mut self,
        address: MemoryAddress,
        value: Word,
        field_spec: impl Into<Option<FieldSpec>>,
    ) -> Result<(), WriteConflictError> {
        self.check_write(address)?;
        Ok(self.memory.store(address, value, field_spec))
    }

    pub fn try_mem_move(
        &mut self,
        src: MemoryRange,
        dest: MemoryRange,
    ) -> Result<(), MemMoveError> {
        self.check_read(src)?;
        self.check_write(dest)?;

        self.memory
            .as_mut_slice()
            .copy_within(src.to_range_usize(), dest.start.to_usize());

        Ok(())
    }

    pub fn reset(&mut self) {
        todo!();
    }

    fn check_read(
        &self,
        range: impl Into<MemoryRange>,
    ) -> Result<(), ReadConflictError> {
        let r1 = range.into();

        for op in self.device_ops.iter() {
            match op.kind {
                DeviceOpKind::Output(r2)
                    if r1.is_overlapping(&r2)
                        && self
                            .devices
                            .get(op.unit)
                            .is_some_and(|dev| !dev.is_ready()) =>
                {
                    return Err(ReadConflictError { unit: op.unit });
                }
                _ => {}
            }
        }

        Ok(())
    }

    fn check_write(
        &self,
        range: impl Into<MemoryRange>,
    ) -> Result<(), WriteConflictError> {
        let r1 = range.into();

        for op in self.device_ops.iter() {
            match op.kind {
                DeviceOpKind::Input(r2) | DeviceOpKind::Output(r2)
                    if r1.is_overlapping(&r2)
                        && self
                            .devices
                            .get(op.unit)
                            .is_some_and(|dev| !dev.is_ready()) =>
                {
                    return Err(WriteConflictError { unit: op.unit });
                }
                _ => {}
            }
        }

        Ok(())
    }
}
