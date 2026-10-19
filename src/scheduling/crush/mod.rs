//! CRUSH
use std::any::TypeId;

use jetstream::prelude::*;
use jetstream_rpc::context::RemoteAddr;

use crate::scheduling::Placement;

impl Placement for mycrush::crush::Map {
    fn place<W: super::Resource>(
        &self,
        what: W,
    ) -> std::prelude::v1::Result<Vec<RemoteAddr>, super::PlacementError> {
        if what.type_id() == TypeId::of::<Data>() {
            todo!()
        } else {
            Err(super::PlacementError::NotFound)
        }
    }
}
