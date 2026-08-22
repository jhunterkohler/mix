use std::cmp::Ordering;

use crate::asm::Program;
use crate::dev::{Device, DeviceList, DeviceUnit};
use crate::emu::MachineRegisters;
use crate::emu::bus::Bus;
use crate::mem::Memory;
use crate::num::Short;

#[derive(Debug)]
pub struct Machine {
    registers: MachineRegisters,
    overflow_toggle: bool,
    comparison_indicator: Ordering,
    bus: Bus,
    location: Short,
}

impl Machine {
    pub fn new(devices: Option<DeviceList>) -> Machine {
        Machine {
            registers: Default::default(),
            overflow_toggle: Default::default(),
            comparison_indicator: Ordering::Equal,
            bus: Bus::new(devices),
            location: Default::default(),
        }
    }

    pub fn registers(&self) -> &MachineRegisters {
        &self.registers
    }

    pub fn registers_mut(&mut self) -> &mut MachineRegisters {
        &mut self.registers
    }

    pub(crate) fn bus(&self) -> &Bus {
        &self.bus
    }

    pub(crate) fn bus_mut(&mut self) -> &mut Bus {
        &mut self.bus
    }

    pub fn memory(&self) -> &Memory {
        self.bus.memory()
    }

    pub fn memory_mut(&mut self) -> &mut Memory {
        self.bus.memory_mut()
    }

    pub fn comparison_indicator(&self) -> Ordering {
        self.comparison_indicator
    }

    pub fn set_comparison_indicator(&mut self, new_value: Ordering) {
        self.comparison_indicator = new_value;
    }

    pub fn overflow_toggle(&self) -> bool {
        self.overflow_toggle
    }

    pub fn set_overflow_toggle(&mut self, new_value: bool) {
        self.overflow_toggle = new_value;
    }

    pub fn location(&self) -> Short {
        self.location
    }

    pub fn set_location(&mut self, new_value: Short) {
        self.location = new_value;
    }

    pub fn reset(&mut self) {
        self.registers.reset();
        self.overflow_toggle = false;
        self.comparison_indicator = Ordering::Equal;
        self.bus.reset();
        self.location = Short::POS_ZERO;
    }

    pub fn load_program(&mut self, program: &Program) {
        self.reset();
        self.location = program.entry_point().into();

        for section in program.sections() {
            self.memory_mut()[section.range()].copy_from_slice(section.data());
        }
    }

    pub fn get_device(&self, unit: DeviceUnit) -> Option<&dyn Device> {
        self.bus.get_device(unit)
    }

    pub fn get_device_mut(
        &mut self,
        unit: DeviceUnit,
    ) -> Option<&mut dyn Device> {
        self.bus.get_device_mut(unit)
    }

    pub fn take_device(
        &mut self,
        unit: DeviceUnit,
    ) -> Option<Box<dyn Device>> {
        self.bus.take_device(unit)
    }

    pub fn replace_device(
        &mut self,
        unit: DeviceUnit,
        dev: Box<dyn Device>,
    ) -> Result<Option<Box<dyn Device>>, Box<dyn Device>> {
        self.bus.replace_device(unit, dev)
    }
}

impl Default for Machine {
    fn default() -> Self {
        Machine::new(None)
    }
}
