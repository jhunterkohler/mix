use std::borrow::Borrow;
use std::hash::Hash;
use std::{fmt, mem};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::asm::Program;
use crate::dev::DeviceUnit;
use crate::emu::Machine;
use crate::mem::MemoryAddress;
use crate::num::Short;

#[derive(Debug, Default)]
struct BreakpointIdFactory {
    next_id: u32,
}

impl BreakpointIdFactory {
    fn next(&mut self) -> BreakpointId {
        let inner = self.next_id;
        self.next_id.checked_add(1).unwrap();
        BreakpointId { inner }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BreakpointId {
    inner: u32,
}

impl BreakpointId {
    pub fn to_u32(self) -> u32 {
        self.inner
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BreakpointKind {
    // Breakpoints.
    MemoryLocation { location: Short },
    SourceLocation { line: usize },

    // Data breakpoints.
    MemLoad { address: MemoryAddress },
    MemStore { address: MemoryAddress },
    MemAccess { address: MemoryAddress },
    IoInput { unit: DeviceUnit },
    IoOutput { unit: DeviceUnit },
    IoControl { unit: DeviceUnit },
    IoAccess { unit: DeviceUnit },
}

pub trait BreakpointCondition {
    fn should_break(&self, state: &Machine) -> bool;
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct AlwaysBreak;

impl BreakpointCondition for AlwaysBreak {
    fn should_break(&self, _state: &Machine) -> bool {
        true
    }
}

struct BreakpointData {
    kind: BreakpointKind,
    condition: Box<dyn BreakpointCondition>,
    is_enabled: bool,
}

impl fmt::Debug for BreakpointData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BreakpointData")
            .field("kind", &self.kind)
            .field("condition", &"Box<dyn BreakpointCondition>")
            .field("is_enabled", &self.is_enabled)
            .finish()
    }
}

#[derive(Debug, Clone)]
pub struct BreakpointRef<'a> {
    id: BreakpointId,
    data: &'a BreakpointData,
}

impl BreakpointRef<'_> {
    pub fn id(&self) -> BreakpointId {
        self.id
    }

    pub fn kind(&self) -> &BreakpointKind {
        &self.data.kind
    }

    pub fn condition(&self) -> &dyn BreakpointCondition {
        self.data.condition.as_ref()
    }

    pub fn is_enabled(&self) -> bool {
        self.data.is_enabled
    }
}

#[derive(Debug, Default)]
struct BreakpointDataMap {
    inner: FxHashMap<BreakpointId, BreakpointData>,
}

impl BreakpointDataMap {
    fn add(
        &mut self,
        id: BreakpointId,
        kind: BreakpointKind,
        condition: Box<dyn BreakpointCondition>,
    ) {
        let data = BreakpointData {
            kind,
            condition: condition.into(),
            is_enabled: true,
        };

        self.inner.insert(id, data);
    }

    fn remove(&mut self, id: BreakpointId) -> bool {
        self.inner.remove(&id).is_some()
    }

    fn clear(&mut self) {
        self.inner.clear();
    }

    fn get(&self, id: BreakpointId) -> Option<BreakpointRef<'_>> {
        self.inner.get(&id).map(|data| BreakpointRef { id, data })
    }

    fn iter(&self) -> impl Iterator<Item = BreakpointRef<'_>> {
        self.inner.iter().map(|(&id, data)| BreakpointRef { id, data })
    }

    fn set_is_enabled(&mut self, id: BreakpointId, new_value: bool) {
        if let Some(data) = self.inner.get_mut(&id) {
            data.is_enabled = new_value
        }
    }

    fn can_activate(&mut self, id: BreakpointId, machine: &Machine) -> bool {
        self.inner.get(&id).is_some_and(|data| {
            data.is_enabled && data.condition.should_break(machine)
        })
    }
}

#[derive(Debug)]
struct BreakpointTrackingMap<K: Eq + Hash> {
    inner: FxHashMap<K, Vec<BreakpointId>>,
}

impl<K: Eq + Hash> BreakpointTrackingMap<K> {
    fn insert(&mut self, k: K, v: BreakpointId) {
        use std::collections::hash_map::Entry;

        match self.inner.entry(k) {
            Entry::Occupied(mut occupied) => {
                occupied.get_mut().push(v);
            }
            Entry::Vacant(vacant) => {
                vacant.insert(vec![v]);
            }
        }
    }

    fn get<Q: ?Sized>(&self, k: &Q) -> impl Iterator<Item = BreakpointId>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.inner.get(k).into_iter().flatten().copied()
    }

    fn clear(&mut self) {
        self.inner.clear()
    }
}

impl<K: Eq + Hash> Default for BreakpointTrackingMap<K> {
    fn default() -> Self {
        Self { inner: Default::default() }
    }
}

#[derive(Debug, Default)]
pub(super) struct BreakpointManager {
    id_factory: BreakpointIdFactory,
    // Zero indexed line numbers to memory addresses.
    source_map: FxHashMap<usize, MemoryAddress>,
    needs_tracking_update: bool,

    breakpoints: BreakpointDataMap,

    active_breakpoints: FxHashSet<BreakpointId>,
    prev_active_breakpoints: FxHashSet<BreakpointId>,

    location_tracking: BreakpointTrackingMap<Short>,
    mem_load_tracking: BreakpointTrackingMap<MemoryAddress>,
    mem_store_tracking: BreakpointTrackingMap<MemoryAddress>,
    io_input_tracking: BreakpointTrackingMap<DeviceUnit>,
    io_output_tracking: BreakpointTrackingMap<DeviceUnit>,
    io_control_tracking: BreakpointTrackingMap<DeviceUnit>,
}

impl BreakpointManager {
    pub fn load_program(&mut self, program: &Program) {
        self.source_map = program
            .debug_info()
            .source_map()
            .iter()
            .map(|entry| (entry.line_no(), entry.address()))
            .collect();

        self.needs_tracking_update = true;
    }

    pub fn add_breakpoint(
        &mut self,
        kind: BreakpointKind,
        condition: Box<dyn BreakpointCondition>,
    ) -> BreakpointId {
        let id = self.id_factory.next();
        self.breakpoints.add(id, kind, condition);
        self.needs_tracking_update = true;
        id
    }

    pub fn remove_breakpoint(&mut self, id: BreakpointId) {
        self.needs_tracking_update |= self.breakpoints.remove(id);
    }

    pub fn clear_breakpoints(&mut self) {
        self.breakpoints.clear();
        self.active_breakpoints.clear();
        self.prev_active_breakpoints.clear();
        self.location_tracking.clear();
        self.mem_load_tracking.clear();
        self.mem_store_tracking.clear();
        self.io_input_tracking.clear();
        self.io_output_tracking.clear();
        self.io_control_tracking.clear();
        self.needs_tracking_update = false;
    }

    pub fn get_breakpoint(
        &self,
        id: BreakpointId,
    ) -> Option<BreakpointRef<'_>> {
        self.breakpoints.get(id)
    }

    pub fn breakpoints(&self) -> impl Iterator<Item = BreakpointRef<'_>> {
        self.breakpoints.iter()
    }

    pub fn active_breakpoints(
        &self,
    ) -> impl Iterator<Item = BreakpointRef<'_>> {
        self.active_breakpoints
            .iter()
            .map(|id| self.get_breakpoint(*id).unwrap())
    }

    pub fn set_is_enabled(&mut self, id: BreakpointId, new_value: bool) {
        self.breakpoints.set_is_enabled(id, new_value);
    }

    pub fn bump_active_breakpoints(&mut self) {
        if !self.active_breakpoints.is_empty() {
            self.prev_active_breakpoints.clear();
            mem::swap(
                &mut self.active_breakpoints,
                &mut self.prev_active_breakpoints,
            );
        }
    }

    pub fn has_active(&self) -> bool {
        !self.active_breakpoints.is_empty()
    }

    pub fn needs_tracking_update(&self) -> bool {
        self.needs_tracking_update
    }

    pub fn update_tracking(&mut self) {
        debug_assert!(self.needs_tracking_update);

        for bp in self.breakpoints.iter() {
            match bp.kind() {
                BreakpointKind::MemoryLocation { location } => {
                    self.location_tracking.insert(*location, bp.id())
                }
                BreakpointKind::SourceLocation { line } => {
                    if let Some(&location) = self.source_map.get(line) {
                        self.location_tracking.insert(location.into(), bp.id())
                    }
                }
                BreakpointKind::MemLoad { address } => {
                    self.mem_load_tracking.insert(*address, bp.id())
                }
                BreakpointKind::MemStore { address } => {
                    self.mem_store_tracking.insert(*address, bp.id());
                }
                BreakpointKind::MemAccess { address } => {
                    self.mem_load_tracking.insert(*address, bp.id());
                    self.mem_store_tracking.insert(*address, bp.id());
                }
                BreakpointKind::IoInput { unit } => {
                    self.io_input_tracking.insert(*unit, bp.id());
                }
                BreakpointKind::IoOutput { unit } => {
                    self.io_output_tracking.insert(*unit, bp.id());
                }
                BreakpointKind::IoControl { unit } => {
                    self.io_control_tracking.insert(*unit, bp.id());
                }
                BreakpointKind::IoAccess { unit } => {
                    self.io_input_tracking.insert(*unit, bp.id());
                    self.io_output_tracking.insert(*unit, bp.id());
                    self.io_control_tracking.insert(*unit, bp.id());
                }
            }
        }
    }
}

macro_rules! define_track_fn {
    ($name:ident, $value_type:ty, $track_map:ident) => {
        pub fn $name(&mut self, machine: &Machine, value: $value_type) {
            debug_assert!(!self.needs_tracking_update);
            self.active_breakpoints.extend(
                self.$track_map
                    .get(&value)
                    .filter(|id| self.breakpoints.can_activate(*id, machine)),
            )
        }
    };
}

impl BreakpointManager {
    define_track_fn!(track_mem_load, MemoryAddress, mem_load_tracking);
    define_track_fn!(track_mem_store, MemoryAddress, mem_store_tracking);
    define_track_fn!(track_io_input, DeviceUnit, io_input_tracking);
    define_track_fn!(track_io_output, DeviceUnit, io_output_tracking);
    define_track_fn!(track_io_control, DeviceUnit, io_control_tracking);

    pub fn track_location(&mut self, machine: &Machine, value: Short) {
        self.active_breakpoints.extend(
            self.location_tracking.get(&value).filter(|id| {
                !self.prev_active_breakpoints.contains(id)
                    && self.breakpoints.can_activate(*id, machine)
            }),
        )
    }
}
