#[cfg(feature = "iroh")]
use std::collections::BTreeSet;
#[cfg(feature = "iroh")]
use std::net::SocketAddr;
use std::path::PathBuf;
use std::{fmt::Display, net::IpAddr};

use jetstream_wireformat::{JetStreamWireFormat, WireFormat};
#[cfg(tokio_unix)]
use tokio::net::{UnixStream, unix::UCred};
#[cfg(any(feature = "turmoil", tokio_unix, native))]
use tokio_util::codec::Framed;
#[cfg(any(feature = "iroh", feature = "x509"))]
use url::Url;

#[cfg(test)]
mod tests;

/// Who is calling: what a node authenticated about a connection.
///
/// It has a wire format so a host can hand it to code running on the same
/// node, such as a wasm guest. **Beside the frame, never inside it:** a frame
/// is whatever the peer sent, so an identity in one is the caller's claim about
/// itself, while a `Context` is what the node established. The encoding only
/// moves it from the node to code running on that node.
///
/// * **The numbers don't depend on cargo features.** [`RemoteAddr`] and
///   [`Peer`] number their variants by position, so those with a `cfg` come
///   last (see their docs). A variant this build lacks is an error to decode,
///   not an identity dropped: a guest built without `x509` that is handed a
///   TLS peer must refuse the call, not treat the caller as anonymous.
/// * **A Unix socket path that is not UTF-8 cannot be carried** and refuses to
///   encode.
///
/// What it does not promise is that a decoded identity is *true*. [`Unix`]
/// credentials and a [`RemoteAddr::UnixAddr`] are encodable, but mean something
/// only on the node that observed them. Producing one from a socket you
/// accepted is sound; accepting one from the network is not, and nothing here
/// stops a caller from doing it.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, JetStreamWireFormat)]
pub struct Context {
    remote: Option<RemoteAddr>,
    peer: Option<Peer>,
}

impl Display for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.peer {
            Some(Peer::NodeId(id)) => write!(f, "{}", id.0),
            #[cfg(tokio_unix)]
            Some(Peer::Unix(cred)) => write!(
                f,
                "{}",
                cred.process_path()
                    .expect("Failed to get process path")
                    .to_string_lossy()
            ),
            // Without a process table to look the pid up in (a wasm guest),
            // the numbers are all there is.
            #[cfg(not(tokio_unix))]
            Some(Peer::Unix(cred)) => {
                write!(f, "unix:{}:{}", cred.uid(), cred.gid())
            }
            #[cfg(feature = "x509")]
            Some(Peer::Tls(tls_peer)) => {
                if let Some(leaf) = tls_peer.leaf() {
                    if let Some(cn) = &leaf.common_name {
                        write!(f, "{}", cn)
                    } else {
                        write!(f, "{}", leaf.fingerprint)
                    }
                } else {
                    write!(f, "TLS(empty chain)")
                }
            }
            Some(Peer::WebCredentials(creds)) => {
                write!(
                    f,
                    "WebCredentials({})",
                    creds.0.to_str().unwrap_or("<invalid>")
                )
            }
            None => write!(f, "None"),
        }
    }
}

impl From<NodeId> for Context {
    fn from(value: NodeId) -> Self {
        Context {
            remote: None,
            peer: Some(Peer::NodeId(value)),
        }
    }
}

/// Where a connection came from.
///
/// **The order of the variants is the wire format.** The derive numbers them
/// by position, so a variant is only ever appended, and one behind a `cfg`
/// goes after every one that isn't: the ungated variants then have the same
/// number in every build, and a gated one has its number only where it
/// exists. A host and a wasm guest are built with different features; decoding
/// a variant the other end has and this one lacks fails ("invalid variant
/// index") rather than becoming some other variant. `context::wire::tests`
/// pins the numbers.
#[derive(Debug, Clone, PartialEq, Eq, Hash, JetStreamWireFormat)]
pub enum RemoteAddr {
    IpAddr(IpAddr),
    /// A path on the machine that accepted the connection: it names nothing on
    /// any other.
    UnixAddr(PathBuf),
    #[cfg(feature = "iroh")]
    NodeAddr(NodeAddr),
}

/// Who a connection was authenticated as. Ordered as [`RemoteAddr`] is, and
/// for the same reason: the order is the wire format.
#[derive(Debug, Clone, PartialEq, Eq, Hash, JetStreamWireFormat)]
pub enum Peer {
    NodeId(NodeId),
    /// Who the kernel said was on the other end of a Unix socket, to the node
    /// that accepted it. Meaningful on that node only; see [`Unix`].
    Unix(Unix),
    WebCredentials(WebCredentials),

    #[cfg(feature = "x509")]
    Tls(TlsPeer),
}

/// Parsed TLS certificate with extracted identity information
#[cfg(feature = "x509")]
#[derive(Debug, Clone, PartialEq, Eq, Hash, JetStreamWireFormat)]
pub struct TlsCert {
    /// SHA-256 fingerprint of the certificate (hex encoded)
    pub fingerprint: String,
    /// Common Name from the certificate subject (if present)
    pub common_name: Option<String>,
    /// DNS names from SAN (e.g., "example.com")
    pub dns_names: Vec<String>,
    /// IP addresses from SAN (for P2P certs)
    pub ip_addresses: Vec<IpAddr>,
    /// Email addresses from SAN (RFC 822 names)
    pub emails: Vec<String>,
    /// URIs from SAN (e.g., "spiffe://cluster.local/ns/default/sa/myapp")
    pub uris: Vec<Url>,
}

#[cfg(feature = "x509")]
impl TlsCert {
    /// Parse a TLS certificate from DER-encoded bytes
    pub fn from_der(
        der: &[u8],
    ) -> Result<Self, x509_certificate::X509CertificateError> {
        use x509_certificate::X509Certificate;

        let cert = X509Certificate::from_der(der)?;

        let fingerprint = cert
            .sha256_fingerprint()
            .map(|d| hex::encode(d.as_ref()))
            .unwrap_or_default();

        let common_name = cert.subject_common_name();

        let mut dns_names = Vec::new();
        let mut ip_addresses = Vec::new();
        let mut emails = Vec::new();
        let mut uris = Vec::new();

        // OID for Subject Alternative Name: 2.5.29.17
        let oid_san = bcder::Oid(bytes::Bytes::from_static(&[85, 29, 17]));

        for ext in cert.iter_extensions() {
            if ext.id == oid_san {
                // Parse SANs manually since x509-certificate expects constructed
                // tags but RFC 5280 uses IMPLICIT (primitive) tags for most types
                let value_bytes = ext.value.clone().into_bytes();
                parse_subject_alt_names(
                    &value_bytes,
                    &mut dns_names,
                    &mut ip_addresses,
                    &mut emails,
                    &mut uris,
                );
            }
        }

        Ok(TlsCert {
            fingerprint,
            common_name,
            dns_names,
            ip_addresses,
            emails,
            uris,
        })
    }
}

/// Parse Subject Alternative Names from DER-encoded extension value.
/// RFC 5280 uses IMPLICIT tagging for GeneralName, so we parse manually.
#[cfg(feature = "x509")]
fn parse_subject_alt_names(
    data: &[u8],
    dns_names: &mut Vec<String>,
    ip_addresses: &mut Vec<IpAddr>,
    emails: &mut Vec<String>,
    uris: &mut Vec<Url>,
) {
    // SAN extension value is a SEQUENCE of GeneralName
    // Skip the outer SEQUENCE tag (0x30) and length
    if data.len() < 2 || data[0] != 0x30 {
        return;
    }

    let (seq_len, offset) = parse_der_length(&data[1..]);
    if offset == 0 {
        return;
    }
    let mut i = 1 + offset;
    let end = std::cmp::min(i + seq_len, data.len());

    // GeneralName IMPLICIT tags (context-specific, primitive):
    // [1] rfc822Name       - 0x81
    // [2] dNSName          - 0x82
    // [6] uniformResourceIdentifier - 0x86
    // [7] iPAddress        - 0x87
    while i + 2 <= end {
        let tag = data[i];
        let (content_len, len_offset) = parse_der_length(&data[i + 1..]);
        if len_offset == 0 {
            break;
        }
        let content_start = i + 1 + len_offset;
        let content_end = content_start + content_len;
        if content_end > end {
            break;
        }
        let content = &data[content_start..content_end];

        match tag {
            0x81 => {
                // rfc822Name (email)
                if let Ok(email) = std::str::from_utf8(content) {
                    emails.push(email.to_string());
                }
            }
            0x82 => {
                // dNSName
                if let Ok(dns) = std::str::from_utf8(content) {
                    dns_names.push(dns.to_string());
                }
            }
            0x86 => {
                // uniformResourceIdentifier
                if let Ok(uri_str) = std::str::from_utf8(content) {
                    if let Ok(url) = Url::parse(uri_str) {
                        uris.push(url);
                    }
                }
            }
            0x87 => {
                // iPAddress
                match content.len() {
                    4 => {
                        if let Ok(arr) = <[u8; 4]>::try_from(content) {
                            ip_addresses.push(IpAddr::V4(arr.into()));
                        }
                    }
                    16 => {
                        if let Ok(arr) = <[u8; 16]>::try_from(content) {
                            ip_addresses.push(IpAddr::V6(arr.into()));
                        }
                    }
                    _ => {}
                }
            }
            _ => {
                // Skip other GeneralName types (otherName, x400Address, etc.)
            }
        }

        i = content_end;
    }
}

/// Parse DER length encoding. Returns (length, bytes_consumed).
#[cfg(feature = "x509")]
fn parse_der_length(data: &[u8]) -> (usize, usize) {
    if data.is_empty() {
        return (0, 0);
    }
    let first = data[0];
    if first < 0x80 {
        // Short form: length is the byte itself
        (first as usize, 1)
    } else if first == 0x80 {
        // Indefinite length - not valid in DER
        (0, 0)
    } else {
        // Long form: first byte indicates number of length bytes
        let num_bytes = (first & 0x7f) as usize;
        if num_bytes > data.len() - 1 || num_bytes > 4 {
            return (0, 0);
        }
        let mut len = 0usize;
        for &b in &data[1..1 + num_bytes] {
            len = (len << 8) | (b as usize);
        }
        (len, 1 + num_bytes)
    }
}

/// TLS peer identity containing the certificate chain
#[cfg(feature = "x509")]
#[derive(Debug, Clone, PartialEq, Eq, Hash, JetStreamWireFormat)]
pub struct TlsPeer {
    /// Certificate chain (leaf cert first, then intermediates)
    pub chain: Vec<TlsCert>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WebCredentials(pub http::HeaderValue);

impl WireFormat for WebCredentials {
    fn byte_size(&self) -> u32 {
        2 + self.0.as_bytes().len() as u32
    }

    fn encode<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()>
    where
        Self: Sized,
    {
        let bytes = self.0.as_bytes();
        // Little-endian, like every other integer on this wire, and like
        // `decode` below reads it. It was big-endian here, so a value only
        // decoded to itself when its length was a palindrome of bytes.
        let len = u16::try_from(bytes.len()).map_err(|_| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "credentials are too long",
            )
        })?;
        len.encode(writer)?;
        writer.write_all(bytes)
    }

    fn decode<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self>
    where
        Self: Sized,
    {
        let len = u16::decode(reader)?;
        let mut buf = vec![0u8; len as usize];
        reader.read_exact(&mut buf)?;
        let header_value =
            http::HeaderValue::from_bytes(&buf).map_err(|_| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    "Invalid header value",
                )
            })?;
        Ok(WebCredentials(header_value))
    }
}

#[cfg(feature = "x509")]
impl TlsPeer {
    /// Parse a certificate chain from DER-encoded bytes
    pub fn from_der_chain<T: AsRef<[u8]>>(
        certs: &[T],
    ) -> Result<Self, x509_certificate::X509CertificateError> {
        let chain = certs
            .iter()
            .map(|c| TlsCert::from_der(c.as_ref()))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(TlsPeer { chain })
    }

    /// Get the leaf certificate (first in chain)
    pub fn leaf(&self) -> Option<&TlsCert> {
        self.chain.first()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, JetStreamWireFormat)]
pub struct NodeId(String);

#[cfg(feature = "iroh")]
#[derive(Debug, Clone, PartialEq, Eq, Hash, JetStreamWireFormat)]
pub struct NodeAddr {
    id: NodeId,
    addrs: BTreeSet<TransportAddr>,
}

#[cfg(feature = "iroh")]
/// Available address types.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum TransportAddr {
    /// Relays
    Relay(iroh::RelayUrl),
    /// IP based addresses
    Ip(SocketAddr),
}

#[cfg(feature = "iroh")]
impl From<iroh::TransportAddr> for TransportAddr {
    fn from(addr: iroh::TransportAddr) -> Self {
        match addr {
            iroh::TransportAddr::Relay(url) => TransportAddr::Relay(url),
            iroh::TransportAddr::Ip(addr) => TransportAddr::Ip(addr),
            _ => unreachable!(),
        }
    }
}

#[cfg(feature = "iroh")]
impl From<&TransportAddr> for iroh::TransportAddr {
    fn from(addr: &TransportAddr) -> Self {
        match addr {
            TransportAddr::Relay(url) => {
                iroh::TransportAddr::Relay(url.clone())
            }
            TransportAddr::Ip(addr) => iroh::TransportAddr::Ip(*addr),
        }
    }
}

#[cfg(feature = "iroh")]
impl WireFormat for TransportAddr {
    fn byte_size(&self) -> u32 {
        1 + match self {
            TransportAddr::Relay(url) => url.byte_size(),
            TransportAddr::Ip(addr) => addr.byte_size(),
        }
    }

    fn encode<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()>
    where
        Self: Sized,
    {
        match self {
            TransportAddr::Relay(url) => {
                0_u8.encode(writer)?;
                url.encode(writer)
            }
            TransportAddr::Ip(addr) => {
                1_u8.encode(writer)?;
                addr.encode(writer)
            }
        }
    }

    fn decode<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self>
    where
        Self: Sized,
    {
        match u8::decode(reader)? {
            0 => Ok(TransportAddr::Relay(iroh::RelayUrl::from(Url::decode(
                reader,
            )?))),
            1 => Ok(TransportAddr::Ip(SocketAddr::decode(reader)?)),
            _ => Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Invalid transport address type",
            )),
        }
    }
}

#[cfg(feature = "iroh")]
impl From<iroh::PublicKey> for NodeId {
    fn from(value: iroh::PublicKey) -> Self {
        NodeId(value.to_string())
    }
}

#[cfg(feature = "iroh")]
impl From<NodeAddr> for iroh::EndpointAddr {
    fn from(value: NodeAddr) -> Self {
        use std::str::FromStr;

        use iroh::PublicKey;

        iroh::EndpointAddr {
            id: PublicKey::from_str(&value.id.0)
                .expect("Failed to convert NodeId to iroh::NodeId"),
            addrs: value.addrs.iter().map(|addr| addr.into()).collect(),
        }
    }
}

#[cfg(feature = "iroh")]
impl From<iroh::EndpointAddr> for NodeAddr {
    fn from(value: iroh::EndpointAddr) -> Self {
        NodeAddr {
            id: NodeId(value.id.to_string()),
            addrs: value.addrs.into_iter().map(|addr| addr.into()).collect(),
        }
    }
}

/// A Unix-socket peer's credentials: what the kernel reported about the process
/// on the other end, to the node that accepted the connection.
///
/// Plain numbers, so it can be carried (see the `WireFormat` impl for
/// [`Context`]) -- but they mean something **only on the node that observed
/// them**. A uid is a user on that machine, a pid is a process in that pid
/// namespace for as long as it lives, and [`Unix::process_path`] reads that
/// machine's `/proc`. A node must produce one from a socket it accepted itself
/// and never trust one that arrived over the network; when it forwards a call
/// to another node, it speaks as itself.
///
/// It used to wrap tokio's `UCred`, which has no public constructor, so a
/// value could be encoded but never decoded. It is built from one with
/// `Unix::from`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, JetStreamWireFormat)]
pub struct Unix {
    pid: Option<i32>,
    uid: u32,
    gid: u32,
}

impl Unix {
    pub fn new(pid: Option<i32>, uid: u32, gid: u32) -> Self {
        Unix { pid, uid, gid }
    }

    /// The process, if the platform said which.
    pub fn pid(&self) -> Option<i32> {
        self.pid
    }

    pub fn uid(&self) -> u32 {
        self.uid
    }

    pub fn gid(&self) -> u32 {
        self.gid
    }
}

#[cfg(tokio_unix)]
impl From<UCred> for Unix {
    fn from(cred: UCred) -> Self {
        Unix {
            pid: cred.pid(),
            uid: cred.uid(),
            gid: cred.gid(),
        }
    }
}

#[cfg(tokio_unix)]
impl Unix {
    /// returns the process' path
    pub fn process_path(&self) -> Result<PathBuf, std::io::Error> {
        use std::fs::read_link;
        if let Some(pid) = self.pid() {
            read_link(format!("/proc/{}/exe", pid))
        } else {
            Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "PID not found",
            ))
        }
    }
}

pub trait Contextual {
    fn context(&self) -> Context;
}

#[cfg(tokio_unix)]
impl<U> Contextual for Framed<UnixStream, U> {
    fn context(&self) -> Context {
        let remote = if let Ok(addr) = self.get_ref().peer_addr() {
            addr.as_pathname()
                .map(|addr| RemoteAddr::UnixAddr(addr.to_path_buf()))
        } else {
            None
        };
        let peer = if let Ok(ucred) = self.get_ref().peer_cred() {
            Some(Peer::Unix(Unix::from(ucred)))
        } else {
            None
        };
        Context { remote, peer }
    }
}

// r[impl jetstream.session.identity]
// A plain TCP stream authenticates nothing, so the peer is `None` and
// only the remote address is reported.
//
// Gated on having a network stack rather than on unix sockets: tokio's
// TCP is cross-platform, and gating it with the `UnixStream` impls would
// leave `SingleLaneSession::service_io` unusable with TCP on Windows.
#[cfg(native)]
impl<U> Contextual for Framed<tokio::net::TcpStream, U> {
    fn context(&self) -> Context {
        let remote = self
            .get_ref()
            .peer_addr()
            .ok()
            .map(|addr| RemoteAddr::IpAddr(addr.ip()));
        Context { remote, peer: None }
    }
}

#[cfg(feature = "turmoil")]
impl<U> Contextual for Framed<turmoil::net::TcpStream, U> {
    fn context(&self) -> Context {
        let addr = self.get_ref().peer_addr().unwrap();
        Context {
            remote: Some(RemoteAddr::IpAddr(addr.ip())),
            peer: None,
        }
    }
}

#[cfg(cloudflare)]
impl Contextual for worker::Request {
    fn context(&self) -> Context {
        Context {
            remote: None,
            peer: None,
        }
    }
}

impl Context {
    pub fn new(remote: Option<RemoteAddr>, peer: Option<Peer>) -> Self {
        Context { remote, peer }
    }

    /// Get the remote address
    pub fn remote(&self) -> Option<&RemoteAddr> {
        self.remote.as_ref()
    }

    /// Get the peer identity
    pub fn peer(&self) -> Option<&Peer> {
        self.peer.as_ref()
    }
}
