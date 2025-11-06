struct S<const N: usize>;

const C: usize = 123;

const fn k() -> usize { 5 }

fn f<const N: usize>(_: S<N>) {}

pub fn g() {
    f::<C>(S);
    f::<{1 + 1}>(S);
    f::<{k()}>(S);
}
