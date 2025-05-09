use crate::cell::Cell;
use core::crucible::concurrency;

pub struct Mutex {
    // This platform has no threads, so we can use a Cell here.
    locked: Cell<bool>,
}

unsafe impl Send for Mutex {}
unsafe impl Sync for Mutex {} // no threads on this platform

impl Mutex {
    #[inline]
    pub const fn new() -> Mutex {
        Mutex { locked: Cell::new(false) }
    }

    #[inline]
    pub fn lock(&self) {
        concurrency::mutex_lock(self);
        assert_eq!(self.locked.replace(true), false, "cannot recursively acquire mutex");
    }

    #[inline]
    pub unsafe fn unlock(&self) {
        concurrency::mutex_unlock(self);
        self.locked.set(false);
    }

    #[inline]
    pub fn try_lock(&self) -> bool {
        self.locked.replace(true) == false
    }
}
