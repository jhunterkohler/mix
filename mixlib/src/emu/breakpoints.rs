use std::borrow::Borrow;
use std::hash::Hash;
use std::{fmt, mem};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::dev::DeviceUnit;
use crate::emu::Machine;
use crate::mem::MemoryAddress;
use crate::num::Short;

#[derive(Debug, Default)]
struct BreakpointIdFactory {
    next_id: u32,
}

impl BreakpointIdFactory {
    fn new() -> Self {
        Self { next_id: 0 }
    }

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
    SourceLocation { line: u64 },

    // Data breakpoints.
    MemRead { address: MemoryAddress },
    MemWrite { address: MemoryAddress },
    MemAccess { address: MemoryAddress },
    IoRead { unit: DeviceUnit },
    IoWrite { unit: DeviceUnit },
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
        struct Condition<'a>(&'a dyn BreakpointCondition);

        impl fmt::Debug for Condition<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_struct("dyn BreakpointCondition").finish()
            }
        }

        f.debug_struct("BreakpointData")
            .field("kind", &self.kind)
            .field("condition", &Condition(self.condition.as_ref()))
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
}

impl<K: Eq + Hash> Default for BreakpointTrackingMap<K> {
    fn default() -> Self {
        Self { inner: Default::default() }
    }
}

#[derive(Debug, Default)]
pub(super) struct BreakpointManager {
    id_factory: BreakpointIdFactory,
    source_map: FxHashMap<usize, MemoryAddress>,
    needs_tracking_update: bool,

    breakpoints: BreakpointDataMap,

    active_breakpoints: FxHashSet<BreakpointId>,
    prev_active_breakpoints: FxHashSet<BreakpointId>,

    location_tracking: BreakpointTrackingMap<Short>,
    mem_read_tracking: BreakpointTrackingMap<MemoryAddress>,
    mem_write_tracking: BreakpointTrackingMap<MemoryAddress>,
    io_read_tracking: BreakpointTrackingMap<DeviceUnit>,
    io_write_tracking: BreakpointTrackingMap<DeviceUnit>,
    io_control_tracking: BreakpointTrackingMap<DeviceUnit>,
}

impl BreakpointManager {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn set_source_map(&mut self, value: FxHashMap<usize, MemoryAddress>) {
        self.source_map = value;
        self.needs_tracking_update = true;
    }

    pub fn add_breakpoint(
        &mut self,
        kind: BreakpointKind,
        condition: Box<dyn BreakpointCondition>,
    ) -> BreakpointId {
        let id = self.id_factory.next();
        self.breakpoints.add(id, kind, condition);
        id
    }

    pub fn remove_breakpoint(&mut self, id: BreakpointId) {
        self.needs_tracking_update |= self.breakpoints.remove(id);
    }

    pub fn clear_breakpoints(&mut self) {
        todo!();
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

    pub fn is_active(&self, id: BreakpointId) -> bool {
        self.active_breakpoints.contains(&id)
    }

    pub fn needs_tracking_update(&self) -> bool {
        self.needs_tracking_update
    }

    pub fn update_tracking(&mut self) {
        debug_assert!(self.needs_tracking_update);
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
    define_track_fn!(track_mem_read, MemoryAddress, mem_read_tracking);
    define_track_fn!(track_mem_write, MemoryAddress, mem_write_tracking);
    define_track_fn!(track_io_read, DeviceUnit, io_read_tracking);
    define_track_fn!(track_io_write, DeviceUnit, io_write_tracking);
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
