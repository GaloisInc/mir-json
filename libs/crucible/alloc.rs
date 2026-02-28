use core::alloc::{self, Layout, AllocError};
use core::marker::PhantomData;
use core::mem;
use core::ptr::NonNull;

/// Allocate an array of `len` elements of type `T`.  The array begins uninitialized.
pub fn allocate<T>(len: usize) -> *mut T {
    core::crucible::alloc::allocate(len)
}

/// Allocate an array of `len` elements of type `T`.  The array initially contains all zeros.  This
/// fails if `crux-mir` doesn't know how to zero-initialize `T`.
pub fn allocate_zeroed<T>(len: usize) -> *mut T {
    core::crucible::alloc::allocate_zeroed(len)
}

/// Reallocate the array at `*ptr` to contain `new_len` elements.  This reallocation always happens
/// in-place and never fails, so there is no need to return a new pointer.
pub fn reallocate<T>(ptr: *mut T, new_len: usize) {
    core::crucible::alloc::reallocate(ptr, new_len)
}

pub struct TypedAllocator<T>(pub PhantomData<T>);

impl<T> TypedAllocator<T> {
    pub const fn new() -> TypedAllocator<T> {
        TypedAllocator(PhantomData)
    }
}

impl<T> Default for TypedAllocator<T> {
    fn default() -> TypedAllocator<T> {
        TypedAllocator::new()
    }
}

fn size_to_len<T>(size: usize) -> usize {
    if mem::size_of::<T>() == 0 {
        0
    } else {
        size / Layout::new::<T>().size()
    }
}

unsafe impl<T> alloc::Allocator for TypedAllocator<T> {
    // Required methods
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        unsafe {
            let len = size_to_len::<T>(layout.size());
            let ptr = NonNull::new_unchecked(allocate::<T>(len));
            Ok(NonNull::slice_from_raw_parts(
                core::mem::transmute::<NonNull<T>, NonNull<u8>>(ptr),
                len,
            ))
        }
    }
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        // No-op.  crucible-mir currently doesn't track deallocation.
    }

    // Provided methods
    fn allocate_zeroed(
        &self,
        layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        unsafe {
            let len = size_to_len::<T>(layout.size());
            let ptr = NonNull::new_unchecked(allocate_zeroed::<T>(len));
            Ok(NonNull::slice_from_raw_parts(
                core::mem::transmute::<NonNull<T>, NonNull<u8>>(ptr),
                len,
            ))
        }
    }
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        let old_len = size_to_len::<T>(old_layout.size());
        let new_len = size_to_len::<T>(new_layout.size());
        reallocate(ptr.as_ptr().cast::<T>(), new_len);
        // `reallocate` always reallocates in place, so we can just return the old pointer.
        Ok(NonNull::slice_from_raw_parts(ptr.cast::<u8>(), new_len))
    }
    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        panic!("crucible does not yet support Allocator::grow_zeroed")
    }
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        let old_len = size_to_len::<T>(old_layout.size());
        let new_len = size_to_len::<T>(new_layout.size());
        reallocate(ptr.as_ptr().cast::<T>(), new_len);
        Ok(NonNull::slice_from_raw_parts(ptr.cast::<u8>(), new_len))
    }
}
