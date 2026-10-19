//! The wire format of a [`Context`](super::Context): see its docs for what the
//! encoding promises.

use std::io;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

use jetstream_wireformat::WireFormat;
use jetstream_wireformat::wire_format_extensions::ConvertWireFormat;

use super::{Context, NodeId, Peer, RemoteAddr, Unix, WebCredentials};

fn decode(bytes: &[u8]) -> io::Result<Context> {
    Context::from_bytes(&bytes::Bytes::copy_from_slice(bytes))
}

fn round_trip(context: Context) {
    let bytes = context.as_bytes();
    assert_eq!(bytes.len() as u32, context.byte_size(), "{context:?}");
    let back = decode(&bytes).expect("decodes");
    assert_eq!(back, context);
}

#[test]
fn nothing_known_round_trips() {
    round_trip(Context::default());
}

#[test]
fn every_remote_address_round_trips() {
    for remote in [
        RemoteAddr::IpAddr(IpAddr::V4(Ipv4Addr::new(10, 0, 0, 7))),
        RemoteAddr::IpAddr(IpAddr::V6(Ipv6Addr::LOCALHOST)),
        RemoteAddr::UnixAddr("/run/plateau/node.sock".into()),
    ] {
        round_trip(Context::new(Some(remote), None));
    }
}

#[test]
fn every_peer_round_trips() {
    for peer in [
        Peer::NodeId(NodeId("node-a".to_string())),
        Peer::WebCredentials(WebCredentials(http::HeaderValue::from_static(
            "Bearer t",
        ))),
        Peer::Unix(Unix::new(Some(4242), 1000, 100)),
        Peer::Unix(Unix::new(None, 0, 0)),
    ] {
        round_trip(Context::new(None, Some(peer)));
    }
}

#[test]
fn a_remote_and_a_peer_travel_together() {
    round_trip(Context::new(
        Some(RemoteAddr::IpAddr(IpAddr::V4(Ipv4Addr::LOCALHOST))),
        Some(Peer::Unix(Unix::new(Some(1), 2, 3))),
    ));
}

/// The numbers are a promise to builds with different features, so they are
/// written down here: changing one is changing the format.
#[test]
fn the_tags_are_pinned() {
    let tag_of_remote = |remote| {
        let bytes = Context::new(Some(remote), None).as_bytes();
        // `Option` writes its own present/absent byte first.
        bytes[1]
    };
    assert_eq!(
        tag_of_remote(RemoteAddr::IpAddr(IpAddr::V4(Ipv4Addr::LOCALHOST))),
        0
    );
    assert_eq!(tag_of_remote(RemoteAddr::UnixAddr("/s".into())), 1);

    let tag_of_peer = |peer| {
        let bytes = Context::new(None, Some(peer)).as_bytes();
        // Absent remote (one byte), then the peer's present byte.
        bytes[2]
    };
    assert_eq!(tag_of_peer(Peer::NodeId(NodeId("n".to_string()))), 0);
    assert_eq!(tag_of_peer(Peer::Unix(Unix::new(None, 0, 0))), 1);
    assert_eq!(
        tag_of_peer(Peer::WebCredentials(WebCredentials(
            http::HeaderValue::from_static("x")
        ))),
        2
    );
    assert_eq!(tag_of_peer(Peer::Actor("Notebook:ab".to_string())), 3);
}

#[test]
fn an_unknown_kind_is_refused_not_ignored() {
    // Remote present, kind 99.
    let mut bytes = Context::new(
        Some(RemoteAddr::IpAddr(IpAddr::V4(Ipv4Addr::LOCALHOST))),
        None,
    )
    .as_bytes();
    bytes[1] = 99;
    assert!(decode(&bytes).is_err());

    // Peer present, kind 99.
    let mut bytes =
        Context::new(None, Some(Peer::Unix(Unix::new(None, 0, 0)))).as_bytes();
    bytes[2] = 99;
    assert!(decode(&bytes).is_err());
}

/// The kind a gated variant would have, in a build that doesn't have it, is
/// an error and not another variant.
#[cfg(not(feature = "x509"))]
#[test]
fn a_tls_peer_is_refused_where_it_cannot_be_represented() {
    // No remote, a peer, kind 4: where `Tls` is numbered, after `Actor`.
    assert!(decode(&[0, 1, 4]).is_err());
}

/// The gated variant is last, so the ungated ones keep their numbers in a
/// build that has it.
#[cfg(feature = "x509")]
#[test]
fn a_tls_peer_round_trips_and_is_numbered_last() {
    use super::{TlsCert, TlsPeer};

    let peer = Peer::Tls(TlsPeer {
        chain: vec![TlsCert {
            fingerprint: "ab12".to_string(),
            common_name: Some("node-a".to_string()),
            dns_names: vec!["a.example".to_string()],
            ip_addresses: vec![IpAddr::V4(Ipv4Addr::LOCALHOST)],
            emails: vec![],
            uris: vec![],
        }],
    });
    round_trip(Context::new(None, Some(peer.clone())));
    assert_eq!(Context::new(None, Some(peer)).as_bytes()[2], 4);
}

#[cfg(unix)]
#[test]
fn a_path_that_is_not_utf8_cannot_be_carried() {
    use std::os::unix::ffi::OsStrExt;
    let path = std::path::PathBuf::from(std::ffi::OsStr::from_bytes(&[
        b'/', 0xff, 0xfe,
    ]));
    let context = Context::new(Some(RemoteAddr::UnixAddr(path)), None);
    let mut sink = Vec::new();
    let error = context.encode(&mut sink).unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
}

#[test]
fn a_truncated_context_is_an_error() {
    let bytes = Context::new(None, Some(Peer::Unix(Unix::new(Some(1), 2, 3))))
        .as_bytes();
    assert!(decode(&bytes[..bytes.len() - 2]).is_err());
}
