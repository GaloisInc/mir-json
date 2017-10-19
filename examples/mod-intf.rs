trait Blah {
    fn snrzz(x: usize) -> usize;
}

mod foo {
    struct This;

    impl super::Blah for This {
        fn snrzz(x: usize) -> usize { x + 1 }
    }
}

mod bar {
    struct That;

    impl super::Blah for That {
        fn snrzz(x: usize) -> usize { x - 1 }
    }
}

fn dkalf(x: usize) -> usize {
    x
}

fn main () { }
