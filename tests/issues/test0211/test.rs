trait Supertrait1 {
    type AssocItem1;
    fn f1(&self) -> Self::AssocItem1;
}

trait Subtrait1<T>: Supertrait1<AssocItem1 = T> {}

impl Supertrait1 for u8 {
    type AssocItem1 = u8;
    fn f1(&self) -> Self::AssocItem1 {
        *self
    }
}

impl Subtrait1<u8> for u8 {}

pub fn g1() -> u8 {
    let b: Box<dyn Subtrait1<u8>> = Box::new(42u8);
    b.f1()
}

/////

trait Supertrait2 {
    type AssocItem2;
    fn f2(&self) -> Self::AssocItem2;
}

trait Subtrait2<T>: Supertrait2<AssocItem2 = T> {}

impl Supertrait2 for u8 {
    type AssocItem2 = (u8, u8);
    fn f2(&self) -> Self::AssocItem2 {
        (*self, *self)
    }
}

impl Subtrait2<(u8, u8)> for u8 {}

pub fn g2() -> (u8, u8) {
    let b: Box<dyn Subtrait2<(u8, u8)>> = Box::new(42u8);
    b.f2()
}

/////

trait Supertrait3<S> {
    type AssocItem3;
    fn f3(&self, z: S) -> Self::AssocItem3;
}

trait Subtrait3<T>: Supertrait3<u32, AssocItem3 = T> {}

impl Supertrait3<u32> for u8 {
    type AssocItem3 = (u8, u16, u32);
    fn f3(&self, z: u32) -> Self::AssocItem3 {
        (*self, *self as u16, z as u32)
    }
}

impl Subtrait3<(u8, u16, u32)> for u8 {}

pub fn g3() -> (u8, u16, u32) {
    let b: Box<dyn Subtrait3<(u8, u16, u32)>> = Box::new(42u8);
    b.f3(27u32)
}

/////

trait Supertrait4<S> {
    type AssocItem4;
    fn f4(&self, z: S) -> Self::AssocItem4;
}

trait Subtrait4: Supertrait4<u32, AssocItem4 = (u8, u16, u32)> {}

impl Supertrait4<u32> for u8 {
    type AssocItem4 = (u8, u16, u32);
    fn f4(&self, z: u32) -> Self::AssocItem4 {
        (*self, *self as u16, z as u32)
    }
}

impl Subtrait4 for u8 {}

pub fn g4() -> (u8, u16, u32) {
    let b: Box<dyn Subtrait4> = Box::new(42u8);
    b.f4(27u32)
}

/////

trait Supertrait5<S> {
    type AssocItem5;
    fn f5(&self, z: S) -> Self::AssocItem5;
}

trait Subtrait5<T1, T2>: Supertrait5<T2, AssocItem5 = T1> {}

impl Supertrait5<u32> for u8 {
    type AssocItem5 = (u8, u16, u32);
    fn f5(&self, z: u32) -> Self::AssocItem5 {
        (*self, *self as u16, z as u32)
    }
}

impl Subtrait5<(u8, u16, u32), u32> for u8 {}

pub fn g5() -> (u8, u16, u32) {
    let b: Box<dyn Subtrait5<(u8, u16, u32), u32>> = Box::new(42u8);
    b.f5(27u32)
}

/////

use std::ops::Deref;

trait Supertrait6<T> {
    type AssocItem6;
    fn f6(&self) -> Self::AssocItem6;
}

impl Supertrait6<u8> for bool {
    type AssocItem6 = u8;
    fn f6(&self) -> Self::AssocItem6 {
        2
    }
}

impl Supertrait6<u16> for bool {
    type AssocItem6 = u16;
    fn f6(&self) -> Self::AssocItem6 {
        3
    }
}

trait Subtrait6: Supertrait6<u8, AssocItem6 = u8> + Supertrait6<u16, AssocItem6 = u16> {}

impl Subtrait6 for bool {}

pub fn g6() -> u16 {
    let b: Box<dyn Subtrait6> = Box::new(true);
    let br: &dyn Subtrait6 = b.deref();
    let a: u8 = <dyn Subtrait6 as Supertrait6<u8>>::f6(br);
    let b: u16 = <dyn Subtrait6 as Supertrait6<u16>>::f6(br);
    (a as u16) + b
}
