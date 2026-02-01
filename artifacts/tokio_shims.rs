//! tokio "shims" for features that aren't available for Wasm targets.

use crate::net::{TcpListener, ToSocketAddrs};
use std::io;

impl TcpListener {
    pub async fn bind<A: ToSocketAddrs>(addr: A) -> io::Result<TcpListener> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "operation not supported on this platform",
        ))
    }
}
