use crucible_proc_macros::crux_spec_for;

fn f(x: u8) -> u8 {
    x + 1
}

#[crux_spec_for(crate::f)]
fn f_test() {
    let x = crate::f(0);
}
