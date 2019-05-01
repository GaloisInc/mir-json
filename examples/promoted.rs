const C: usize = 1;
static S: &usize = &C;
const C2: &usize = &C;

fn f() {
    let x = &C;
    let y = &S;
    let z = &C2;
}
