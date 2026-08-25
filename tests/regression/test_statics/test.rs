#![feature(thread_local)]

// Ordinary immutable static.
pub static ORDINARY: u32 = 42;

// Mutable static.
pub static mut MUT_STATIC: u32 = 7;

// Static referencing a string literal (creates an anonymous {{alloc}}).
pub static STR_REF: &str = "hi";

// Nested static: rustc invents an anonymous nested static for the inner
// `&LEAF` reference because the outer initializer takes a `&` to a
// `const` that itself contains a `&`. See `Note [Nested statics]` in
// analyz/mod.rs for the mechanism.
pub const LEAF: &[u64] = &[42];
pub static NESTED_OUTER: &[&[u64]] = &[&LEAF];

// Thread-local static (with an initializer).
#[thread_local]
pub static TLS_COUNTER: u32 = 3;

// Thread-local static whose initializer is a reference to a promoted
// literal. The `&0` is const-promoted (not lifted to a nested static)
// so `TLS_REF` ends up holding a pointer into an anonymous
// `GlobalAlloc::Memory` allocation.
#[thread_local]
pub static TLS_REF: &u32 = &0;

// Slice literals are like STR_REF in that it points into an anonymous
// allocation, but the renderer treats slices structurally (rendering
// each element via `try_render_opty`) rather than as an opaque byte
// buffer, so this exercises a separate arm from the string case.
pub static ARR_REF: &[u8] = &[1, 2, 3];

// `static mut` with a compound value. Exercises `make_allocation_body`
// with `is_mut = true`, distinct from `MUT_STATIC` (primitive) above.
pub static mut MUT_ARR: [u32; 3] = [1, 2, 3];

// Function-pointer static. Exercises the `FnPtr` arm of
// `try_render_opty`, and confirms that `mir.used.instances` gets
// populated for functions reached only via constant statics.
fn fn_ptr_target() -> u32 { 100 }
pub static FN_PTR: fn() -> u32 = fn_ptr_target;

pub union Mix {
  f1: (bool, u8),
  f2: (u8, bool),
}

// Z0 has a value which is half from one of the union and half from the other
pub static Z0: Mix = {
    let mut u = Mix { f1: (true, 99) };
    u.f2.0 = 99; // overwrite through *the other* union, but only half the value
    u
};

// Some function, so we can initialize function pointers.
fn f(arg: i32) -> i32 { arg }

// `Z1` points to `f`
pub static Z1: fn(i32) -> i32 = f;

pub struct T(*const());
unsafe impl Sync for T {}

// `Z2` is a *const() pointer that points to a function
pub static Z2: T = {
   let f1 = f as fn(i32) -> i32;
   T(unsafe { core::mem::transmute(f1) })
};


pub union U { cast: fn(u32) -> u32 }

// We can use a union to circumvent value expectations:
// here's how we can make a function pointer, which has the value 8.
// Without the union `rustc` reports "undefined behavior".
pub static Z3: U = {
    U { cast: unsafe { core::mem::transmute((&8u8) as *const u8) } }
};

// Force each static to be used so it appears in mono items.
pub fn touch_all() -> u32 {
    let _a       = &Z0;
    let _a       = &Z1;
    let T(_a)    = Z2;
    let _a       = unsafe { Z3.cast };

    let mut_val = unsafe { MUT_STATIC };
    let mut_arr_val = unsafe { MUT_ARR[0] };
    ORDINARY
        .wrapping_add(mut_val)
        .wrapping_add(STR_REF.len() as u32)
        .wrapping_add(NESTED_OUTER.len() as u32)
        .wrapping_add(TLS_COUNTER)
        .wrapping_add(*TLS_REF)
        .wrapping_add(ARR_REF[0] as u32)
        .wrapping_add(mut_arr_val)
        .wrapping_add(FN_PTR())
}
