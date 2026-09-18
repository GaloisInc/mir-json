use core::alloc::{self, AllocError, Layout};
use core::intrinsics::const_eval_select;
use core::marker::PhantomData;
use core::mem;
use core::ptr::NonNull;
use crate::alloc::Global;

/// Allocate an array of `len` elements of type `T`.  The array begins uninitialized.
pub fn allocate<T>(_len: usize) -> *mut T {
    unimplemented!("allocate")
}

/// Allocate an array of `len` elements of type `T`.  The array initially contains all zeros.  This
/// fails if `crux-mir` doesn't know how to zero-initialize `T`.
pub fn allocate_zeroed<T>(_len: usize) -> *mut T {
    unimplemented!("allocate_zeroed")
}

/// Reallocate the array at `*ptr` to contain `new_len` elements. Accessing this
/// array via the `ptr` parameter, rather than the newly-returned pointer, is
/// unspecified behavior.
pub fn reallocate<T>(_ptr: *mut T, _new_len: usize) -> *mut T {
    unimplemented!("reallocate")
}

pub struct TypedAllocator<T>(pub PhantomData<T>);

impl<T> TypedAllocator<T> {
    /// Workaround for const-stability issues when using `fn new` from `RawVec` const methods.
    pub const NEW: Self = Self(PhantomData);

    pub const fn new() -> TypedAllocator<T> {
        TypedAllocator(PhantomData)
    }
}

impl<T> Default for TypedAllocator<T> {
    fn default() -> TypedAllocator<T> {
        TypedAllocator::new()
    }
}

const fn size_to_len<T>(size: usize) -> usize {
    if mem::size_of::<T>() == 0 {
        0
    } else {
        size / Layout::new::<T>().size()
    }
}

#[unstable(feature = "crucible_intrinsics", issue = "none")]
#[rustc_const_unstable(feature = "crucible_intrinsics", issue = "none")]
const unsafe impl<T> alloc::Allocator for TypedAllocator<T> {
    // Required methods

    #[rustc_allow_const_fn_unstable(const_eval_select)]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        #[rustc_allow_const_fn_unstable(const_heap)]
        #[rustc_allow_const_fn_unstable(const_trait_impl)]
        const fn go_const(layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            Global.allocate(layout)
        }
        fn go_runtime<T>(layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            unsafe {
                let len = size_to_len::<T>(layout.size());
                let ptr = NonNull::new_unchecked(allocate::<T>(len));
                Ok(NonNull::slice_from_raw_parts(ptr.cast::<u8>(), len))
            }
        }
        const_eval_select((layout,), go_const, go_runtime::<T>)
    }

    #[rustc_allow_const_fn_unstable(const_eval_select)]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        #[rustc_allow_const_fn_unstable(const_heap)]
        #[rustc_allow_const_fn_unstable(const_trait_impl)]
        const fn go_const(ptr: NonNull<u8>, layout: Layout) {
            unsafe {
                Global.deallocate(ptr, layout)
            }
        }
        fn go_runtime<T>(ptr: NonNull<u8>, layout: Layout) {
            // No-op.  crucible-mir currently doesn't track deallocation.
        }
        const_eval_select((ptr, layout), go_const, go_runtime::<T>)
    }

    // Provided methods

    #[rustc_allow_const_fn_unstable(const_eval_select)]
    fn allocate_zeroed(
        &self,
        layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        #[rustc_allow_const_fn_unstable(const_heap)]
        #[rustc_allow_const_fn_unstable(const_trait_impl)]
        const fn go_const(layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            Global.allocate(layout)
        }
        fn go_runtime<T>(layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            unsafe {
                let len = size_to_len::<T>(layout.size());
                let ptr = NonNull::new_unchecked(allocate_zeroed::<T>(len));
                Ok(NonNull::slice_from_raw_parts(ptr.cast::<u8>(), len))
            }
        }
        const_eval_select((layout,), go_const, go_runtime::<T>)
    }

    #[rustc_allow_const_fn_unstable(const_eval_select)]
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        #[rustc_allow_const_fn_unstable(const_heap)]
        #[rustc_allow_const_fn_unstable(const_trait_impl)]
        const fn go_const(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocError> {
            unsafe {
                Global.grow(ptr, old_layout, new_layout)
            }
        }
        fn go_runtime<T>(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocError> {
            unsafe {
                let _old_len = size_to_len::<T>(old_layout.size());
                let new_len = size_to_len::<T>(new_layout.size());
                let new_ptr: *mut T = reallocate(ptr.as_ptr().cast::<T>(), new_len);
                let new_nonnull: NonNull<u8> = unsafe { NonNull::new_unchecked(new_ptr.cast::<u8>()) };
                Ok(NonNull::slice_from_raw_parts(new_nonnull, new_len))
            }
        }
        const_eval_select((ptr, old_layout, new_layout), go_const, go_runtime::<T>)
    }

    #[rustc_allow_const_fn_unstable(const_eval_select)]
    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        #[rustc_allow_const_fn_unstable(const_heap)]
        #[rustc_allow_const_fn_unstable(const_trait_impl)]
        const fn go_const(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocError> {
            unsafe {
                Global.grow_zeroed(ptr, old_layout, new_layout)
            }
        }
        fn go_runtime<T>(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocError> {
            unsafe {
                panic!("crucible does not yet support Allocator::grow_zeroed")
            }
        }
        const_eval_select((ptr, old_layout, new_layout), go_const, go_runtime::<T>)
    }

    #[rustc_allow_const_fn_unstable(const_eval_select)]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        #[rustc_allow_const_fn_unstable(const_heap)]
        #[rustc_allow_const_fn_unstable(const_trait_impl)]
        const fn go_const(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocError> {
            unsafe {
                Global.shrink(ptr, old_layout, new_layout)
            }
        }
        fn go_runtime<T>(
            ptr: NonNull<u8>,
            old_layout: Layout,
            new_layout: Layout,
        ) -> Result<NonNull<[u8]>, AllocError> {
            unsafe {
                let _old_len = size_to_len::<T>(old_layout.size());
                let new_len = size_to_len::<T>(new_layout.size());
                let new_ptr: *mut T = reallocate(ptr.as_ptr().cast::<T>(), new_len);
                let new_nonnull: NonNull<u8> = unsafe { NonNull::new_unchecked(new_ptr.cast::<u8>()) };
                Ok(NonNull::slice_from_raw_parts(new_nonnull, new_len))
            }
        }
        const_eval_select((ptr, old_layout, new_layout), go_const, go_runtime::<T>)
    }
}
