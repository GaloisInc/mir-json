// cfg_if::cfg_if! {
//     if #[cfg(any(
//         all(target_os = "windows", not(target_vendor = "win7")),
//         target_os = "linux",
//         target_os = "android",
//         target_os = "freebsd",
//         target_os = "openbsd",
//         target_os = "dragonfly",
//         all(target_family = "wasm", target_feature = "atomics"),
//         target_os = "hermit",
//     ))] {
//         mod futex;
//         pub use futex::Mutex;
//     } else if #[cfg(target_os = "fuchsia")] {
//         mod fuchsia;
//         pub use fuchsia::Mutex;
//     } else if #[cfg(any(
//         target_family = "unix",
//         target_os = "teeos",
//     ))] {
//         mod pthread;
//         pub use pthread::Mutex;
//     } else if #[cfg(all(target_os = "windows", target_vendor = "win7"))] {
//         mod windows7;
//         pub use windows7::{Mutex, raw};
//     } else if #[cfg(all(target_vendor = "fortanix", target_env = "sgx"))] {
//         mod sgx;
//         pub use sgx::Mutex;
//     } else if #[cfg(target_os = "solid_asp3")] {
//         mod itron;
//         pub use itron::Mutex;
//     } else if #[cfg(target_os = "xous")] {
//         mod xous;
//         pub use xous::Mutex;
//     } else {
        mod no_threads;
        pub use no_threads::Mutex;
//     }
// }
