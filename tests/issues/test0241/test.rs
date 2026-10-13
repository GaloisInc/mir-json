static S1: &[u8] = &[1, 2, 3, 4];
static S2: &u8 = S1.split_last().unwrap().0;

pub fn f() -> &'static u8 {
    S2
}

static X: &u8 = &(1_i32, 2_u8).1;

pub fn g() -> &'static u8 {
    X
}

static Y: (&u8, &u8) = {
    let r = &(1_i32, 2_u8, 3_u8);
    (&r.1, &r.2)
};
static Y0: &u8 = Y.0;
static Y1: &u8 = Y.1;

pub fn h0() -> &'static u8 {
    Y0
}

pub fn h1() -> &'static u8 {
    Y1
}
