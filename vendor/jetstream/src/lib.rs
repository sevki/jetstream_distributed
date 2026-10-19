#![doc(
    html_logo_url = "https://raw.githubusercontent.com/sevki/jetstream/main/logo/JetStream.png"
)]
#![doc(
    html_favicon_url = "https://raw.githubusercontent.com/sevki/jetstream/main/logo/JetStream.png"
)]
#![cfg_attr(docsrs, feature(doc_cfg))]
//! # JetStream
//! JetStream, is a collection of crates that provide a set of tools to build distributed systems.
//! It started it's life off in the CrosVM project, and has since been extracted into it's own project.
//! For more information please see the [JetStream Book](https://sevki.github.io/jetstream)
pub mod prelude {
    pub extern crate async_trait;
    pub extern crate futures;
    pub extern crate jetstream_error;
    pub extern crate jetstream_macros;
    pub extern crate jetstream_rpc;
    pub extern crate jetstream_wireformat;
    pub extern crate lazy_static;
    pub extern crate trait_variant;

    pub use async_trait::async_trait;
    pub use jetstream_error::*;
    pub use jetstream_macros::{service, JetStreamWireFormat};
    pub use jetstream_rpc::{
        client,
        client::ClientTransport,
        context::Context,
        server,
        server::Server,
        session::*,
        subscription,
        subscription::{Endpoint, Item, Subscription},
        Error, Frame, Framed, Framer, Message, Mux, Protocol, RpcCall,
        RpcStream, Rversion, TagPool, Tversion, Version, RJETSTREAMERROR,
        RVERSION, TVERSION,
    };
    pub use jetstream_wireformat::{Data, WireFormat};
    pub use lazy_static::*;
    pub use trait_variant::make;

    #[cfg(feature = "tracing")]
    pub extern crate tracing;
    #[cfg(feature = "tracing")]
    pub use tracing::*;
    #[cfg(feature = "tracing")]
    pub extern crate tracing_subscriber;
}

#[cfg(feature = "9p")]
pub mod p9 {
    extern crate jetstream_9p;
    pub use jetstream_9p::*;
}

// Native-only, matching where Cargo.toml declares these dependencies: QUIC
// needs UDP sockets, which wasm32 has none of. The feature can be on in a
// build that also targets wasm32; the crate just isn't there to re-export.
#[cfg(all(feature = "quic", not(target_arch = "wasm32")))]
pub mod quic {
    extern crate jetstream_quic;
    pub use jetstream_quic::*;
}

#[cfg(all(feature = "http", not(target_arch = "wasm32")))]
pub mod http {
    extern crate jetstream_http;
    pub use jetstream_http::*;
}

#[cfg(all(target_arch = "wasm32", feature = "wasm"))]
pub mod wasm {
    extern crate jetstream_wasm;
    pub use jetstream_wasm::*;
}

#[cfg(feature = "iroh")]
pub mod iroh {
    extern crate jetstream_iroh;
    pub use jetstream_iroh::*;
}

pub mod macros;
