//! CRUSH
use crate::host::HostId;
use crate::scheduling::placement::PlacementError;
use crate::scheduling::{Resource, placement::Placement};

impl Placement for mycrush::crush::Map {
    fn place<W: Resource>(&self, what: W) -> Result<Vec<HostId>, PlacementError> {
        // Not written yet. What it has to do: derive `x` from a stable encoding of
        // the resource's identity (never from a `TypeId`, which is not stable across
        // builds), choose a rule, take the device weights from the membership view,
        // run `do_rule`, and map the device ids it returns to hosts.
        let _ = what;
        todo!("CRUSH placement")
    }
}
