#![cfg(all(feature = "service", feature = "iroh"))]
// use crate::swim::service::{Membership, membership_protocol::MembershipService};
// use crate::{
//     actor::{
//         service::{Actor, Receipt, Record, Snapshot},
//         system::ActorSystem,
//     },
//     id::{Id, Lookup},
//     ownership::service::Offer,
// };
// use jetstream::prelude::*;

// pub(crate) struct IrohActorSystem {}

// #[async_trait]
// impl Lookup for IrohActorSystem {
//     type Item = jetstream::prelude::jetstream_rpc::context::RemoteAddr;

//     async fn lookup(&self, id: Id) -> Option<&Self::Item> {
//         todo!()
//     }
// }

// pub(crate) struct IrohActor {}

// impl Actor for IrohActor {
//     async fn poll(&self, ctx: Context) -> Result<Offer> {
//         todo!()
//     }

//     async fn acquire(&self, ctx: Context, epoch: u64) -> Result<()> {
//         todo!()
//     }

//     async fn begin_transfer(&self, ctx: Context, to: Id) -> Result<()> {
//         todo!()
//     }

//     async fn release(&self, ctx: Context, epoch: u64) -> Result<()> {
//         todo!()
//     }

//     async fn send(&self, ctx: Context, body: u64) -> Result<u64> {
//         todo!()
//     }

//     async fn accept(&self, ctx: Context, epoch: u64, sender: Id, seq: u64) -> Result<Receipt> {
//         todo!()
//     }

//     async fn state(&self, ctx: Context) -> Result<Snapshot> {
//         todo!()
//     }

//     async fn journal(&self, ctx: Context, from: u64, limit: u64) -> Result<Vec<Record>> {
//         todo!()
//     }
// }

// impl ActorSystem for IrohActorSystem {
//     type Actor = IrohActor;
// }
