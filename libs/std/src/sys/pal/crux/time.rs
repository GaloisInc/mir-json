use crate::sys::{self, FromInner, IntoInner};
use crate::time::Duration;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Instant(Duration);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct SystemTime(Duration);

pub const UNIX_EPOCH: SystemTime = SystemTime(Duration::ZERO);

impl Instant {
    pub fn now() -> Instant {
        Instant(Duration::ZERO)
    }

    pub fn checked_sub_instant(&self, other: &Instant) -> Option<Duration> {
        self.0.checked_sub(other.0)
    }

    pub fn checked_add_duration(&self, other: &Duration) -> Option<Instant> {
        Some(Instant(self.0.checked_add(*other)?))
    }

    pub fn checked_sub_duration(&self, other: &Duration) -> Option<Instant> {
        Some(Instant(self.0.checked_sub(*other)?))
    }
}

impl SystemTime {
    pub const MAX: SystemTime = SystemTime(Duration::MAX);

    pub const MIN: SystemTime = SystemTime(Duration::ZERO);

    pub fn now() -> SystemTime {
        UNIX_EPOCH
    }

    pub fn sub_time(&self, other: &SystemTime) -> Result<Duration, Duration> {
        match self.0.checked_sub(other.0) {
            Some(duration) => Ok(duration),
            None => Err(other.0 - self.0),
        }
    }

    pub fn checked_add_duration(&self, other: &Duration) -> Option<SystemTime> {
        Some(SystemTime(self.0.checked_add(*other)?))
    }

    pub fn checked_sub_duration(&self, other: &Duration) -> Option<SystemTime> {
        Some(SystemTime(self.0.checked_sub(*other)?))
    }
}

impl FromInner<sys::time::SystemTime> for SystemTime {
    fn from_inner(time: sys::time::SystemTime) -> SystemTime {
        match time.sub_time(&sys::time::UNIX_EPOCH) {
            Ok(pos) => UNIX_EPOCH.checked_add_duration(&pos).unwrap(),
            Err(neg) => UNIX_EPOCH.checked_sub_duration(&neg).unwrap(),
        }
    }
}

impl IntoInner<sys::time::SystemTime> for SystemTime {
    fn into_inner(self) -> sys::time::SystemTime {
        // NB: A bit skeevy, but much easier than actually converting to a
        // sys::time::SystemTime
        sys::time::UNIX_EPOCH
    }
}
