use arrayvec::ArrayVec;

use crate::dev::{Device, DeviceList, DeviceUnit};
use crate::mem::{Memory, MemoryAddress, MemoryRange};
use crate::num::{FieldSpec, Short, Word};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InvalidDeviceOpError {
    OutputUnsupported,
    InputUnsupported,
    BlockOutOfBounds,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DeviceOpKind {
    Control(Short),
    Input(MemoryAddress),
    Output(MemoryAddress),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DeviceOp {
    unit: DeviceUnit,
    kind: DeviceOpKind,
}

impl DeviceOp {
    pub fn try_new(
        unit: DeviceUnit,
        kind: DeviceOpKind,
    ) -> Result<Self, InvalidDeviceOpError> {
        match kind {
            DeviceOpKind::Input(start) | DeviceOpKind::Output(start)
                if MemoryRange::try_new(start, unit.kind().block_size())
                    .is_err() =>
            {
                Err(InvalidDeviceOpError::BlockOutOfBounds)
            }
            DeviceOpKind::Input(_) if !unit.kind().supports_input() => {
                Err(InvalidDeviceOpError::InputUnsupported)
            }
            DeviceOpKind::Output(_) if !unit.kind().supports_output() => {
                Err(InvalidDeviceOpError::OutputUnsupported)
            }
            _ => Ok(DeviceOp { unit, kind }),
        }
    }

    pub fn unit(&self) -> DeviceUnit {
        self.unit
    }

    pub fn kind(&self) -> DeviceOpKind {
        self.kind
    }

    pub fn range(&self) -> MemoryRange {
        match self.kind() {
            DeviceOpKind::Control(_) => unsafe {
                MemoryRange::new_unchecked(MemoryAddress::MIN, 0)
            },
            DeviceOpKind::Input(base) => unsafe {
                MemoryRange::new_unchecked(base, self.unit.kind().block_size())
            },
            DeviceOpKind::Output(base) => unsafe {
                MemoryRange::new_unchecked(base, self.unit.kind().block_size())
            },
        }
    }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NoDeviceError;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StartOpError {
    NoDevice,
    MemoryAccess(MemoryAccessError),
}

impl From<NoDeviceError> for StartOpError {
    fn from(_value: NoDeviceError) -> Self {
        StartOpError::NoDevice
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MemoryAccessError {
    ReadConflict(DeviceUnit),
    WriteConflict(DeviceUnit),
}

#[derive(Debug, Default)]
pub struct Bus {
    devices: DeviceList,
    device_ops: DeviceOpList,
    memory: Memory,
}

impl Bus {
    pub fn new() -> Self {
        Default::default()
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

    pub fn start_device_op(
        &mut self,
        memory: &mut Memory,
        op: DeviceOp,
        block: Word,
    ) -> Result<(), StartOpError> {
        let (dev, ops) = self.make_ready(memory, op.unit)?;

        unsafe {
            match op.kind() {
                DeviceOpKind::Control(arg) => dev.control(arg, block),
                DeviceOpKind::Input(_) => {
                    dev.buf_mut().copy_from_slice(&memory[op.range()]);
                    dev.input(block);
                }
                DeviceOpKind::Output(_) => {
                    dev.output(block);
                }
            }
        }

        ops.add_op(op);
        Ok(())
    }

    // pub fn wait(
    //     &mut self,
    //     memory: &mut Memory,
    //     unit: DeviceUnit,
    // ) -> Result<(), NoDeviceError> {
    //     self.make_ready(memory, unit)?;
    //     Ok(())
    // }

    // pub fn wait_all(&mut self, memory: &mut Memory) {
    //     for unit in DeviceUnit::iter() {
    //         self.wait(memory, unit);
    //     }
    // }

    // pub fn wait_and_ignore(
    //     &mut self,
    //     unit: DeviceUnit,
    // ) -> Result<(), NoDeviceError> {
    //     let dev = self.devices.get_mut(unit).ok_or(NoDeviceError(()))?;
    //     dev.wait();
    //     self.ops.remove_unit(unit);
    //     Ok(())
    // }

    // pub fn wait_and_ignore_all(&mut self) {
    //     for unit in DeviceUnit::iter() {
    //         self.wait_and_ignore(unit);
    //     }
    // }

    pub fn try_mem_read(
        &self,
        address: MemoryAddress,
        field_spec: impl Into<Option<FieldSpec>>,
    ) -> Result<Word, MemoryAccessError> {
        self.check_read(address)?;
        Ok(self.memory.load(address, field_spec))
    }

    pub fn try_mem_write(
        &mut self,
        address: MemoryAddress,
        value: Word,
        field_spec: impl Into<Option<FieldSpec>>,
    ) -> Result<(), MemoryAccessError> {
        self.check_write(address)?;
        Ok(self.memory.store(address, value, field_spec))
    }

    fn make_ready(
        &mut self,
        memory: &mut Memory,
        unit: DeviceUnit,
    ) -> Result<(&mut dyn Device, &mut DeviceOpList), NoDeviceError> {
        let dev = self.devices.get_mut(unit).ok_or(NoDeviceError)?;
        dev.wait();

        if let Some((pos, op)) = self.device_ops.unit_pos_op(unit) {
            if let DeviceOpKind::Input(start) = op.kind() {
                let range =
                    MemoryRange::try_new(start, op.unit().kind().block_size())
                        .unwrap();

                memory[range].copy_from_slice(unsafe { dev.buf() });
            }

            self.device_ops.remove_pos(pos);
        }

        Ok((dev, &mut self.device_ops))
    }

    fn check_read(
        &self,
        range: impl Into<MemoryRange>,
    ) -> Result<(), MemoryAccessError> {
        let range = range.into();

        for op in self.device_ops.iter() {
            match op.kind() {
                DeviceOpKind::Output(_)
                    if op.range().is_overlapping(&range) =>
                {
                    return Err(MemoryAccessError::ReadConflict(op.unit()));
                }
                _ => {}
            }
        }

        Ok(())
    }

    fn check_write(
        &self,
        range: impl Into<MemoryRange>,
    ) -> Result<(), MemoryAccessError> {
        let range = range.into();

        for op in self.device_ops.iter() {
            match op.kind() {
                DeviceOpKind::Input(_) | DeviceOpKind::Output(_)
                    if op.range().is_overlapping(&range) =>
                {
                    return Err(MemoryAccessError::WriteConflict(op.unit()));
                }
                _ => {}
            }
        }

        Ok(())
    }
}
