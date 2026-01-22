// For crucible-mir's benefit, we always use unsupported::Parker, which
// implements all thread-parking functions as no-ops. This is arguably too
// simplistic, as this skips calling operations that could trigger a context
// switch in concurrent programs. Although crux-mir does have some support for
// modeling this sort of concurrency, it has since bitrotted. (See #238.) If
// this concurrency support is revived, then we will need to revisit the
// approach here.

mod unsupported;
pub use unsupported::Parker;
