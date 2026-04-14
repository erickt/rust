//@ compile-flags: -Zexperimental-relative-rust-abi-vtables=y

#![crate_type = "lib"]

pub trait Base {
    fn base(&self);
}

pub trait Left: Base {
    fn left(&self);
}

pub trait Right: Base {
    fn right(&self);
}

pub trait Diamond: Left + Right {
    fn diamond(&self);
}

pub struct MyStruct;

impl Base for MyStruct {
    fn base(&self) {}
}

impl Left for MyStruct {
    fn left(&self) {}
}

impl Right for MyStruct {
    fn right(&self) {}
}

impl Diamond for MyStruct {
    fn diamond(&self) {}
}

// CHECK: @vtable.0 = private {{.*}}constant [8 x i32] [i32 0, i32 0, i32 1, i32 trunc {{.*}}, i32 trunc {{.*}}, i32 trunc {{.*}}, i32 trunc {{.*}}@vtable.1{{.*}}, i32 trunc {{.*}}], align 4

// CHECK: @vtable.1 = private {{.*}}constant [5 x i32] [i32 0, i32 0, i32 1, i32 trunc {{.*}}, i32 trunc {{.*}}], align 4

pub fn create_diamond() -> Box<dyn Diamond> {
    Box::new(MyStruct)
}
