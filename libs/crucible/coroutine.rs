pub fn coroutine_field<T, U, const I: usize>(coroutine: *const T) -> *const U {
    unimplemented!("coroutine_field requires crux-mir override")
}

pub fn coroutine_field_ref<T, U, const I: usize>(coroutine: &T) -> &U {
    unsafe { &*coroutine_field::<T, U, I>(coroutine) }
}

pub fn coroutine_field_mut<T, U, const I: usize>(coroutine: &mut T) -> &mut U {
    unsafe { &mut *coroutine_field::<T, U, I>(coroutine).cast_mut() }
}
