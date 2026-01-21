use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

pub struct TcpListener;

impl TcpListener {
    pub async fn bind<A: ToSocketAddrs>(addr: A) {
        addr.to_socket_addrs().await;
    }
}

pub struct MaybeReady;
impl Future for MaybeReady {
    type Output = ();

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Ready(())
    }
}

pub trait ToSocketAddrs {
    type Fut: Future;

    fn to_socket_addrs(&self) -> Self::Fut;
}

impl ToSocketAddrs for &str {
    type Fut = MaybeReady;

    fn to_socket_addrs(&self) -> Self::Fut {
        MaybeReady
    }
}

pub async fn main() {
    TcpListener::bind("127.0.0.1:6142").await
}
