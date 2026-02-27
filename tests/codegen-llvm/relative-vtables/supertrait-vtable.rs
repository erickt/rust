//@ compile-flags: -Zexperimental-relative-rust-abi-vtables=y -C no-prepopulate-passes -Copt-level=0

#![crate_type = "lib"]

pub trait Base {
    fn base(&self);
}

pub trait A: Base {
    fn a(&self);
}

pub trait B: Base {
    fn b(&self);
}

pub trait Diamond: A + B {
    fn diamond(&self);
}

// CHECK: @vtable.0 = private unnamed_addr constant [8 x i32] [
// CHECK-SAME: i32 0, i32 0, i32 1,
// CHECK-SAME: i32 trunc (i64 sub (i64 ptrtoint (ptr dso_local_equivalent [[BASE_BASE:@[^ ]+Base4base[^ ]*]] to i64), i64 ptrtoint (ptr @vtable.0 to i64)) to i32),
// CHECK-SAME: i32 trunc (i64 sub (i64 ptrtoint (ptr dso_local_equivalent [[A_A:@[^ ]+1A1a[^ ]*]] to i64), i64 ptrtoint (ptr @vtable.0 to i64)) to i32),
// CHECK-SAME: i32 trunc (i64 sub (i64 ptrtoint (ptr dso_local_equivalent [[B_B:@[^ ]+1B1b[^ ]*]] to i64), i64 ptrtoint (ptr @vtable.0 to i64)) to i32),
// CHECK-SAME: i32 trunc (i64 sub (i64 ptrtoint (ptr @vtable.1 to i64), i64 ptrtoint (ptr @vtable.0 to i64)) to i32),
// CHECK-SAME: i32 trunc (i64 sub (i64 ptrtoint (ptr dso_local_equivalent [[DIAMOND_DIAMOND:@[^ ]+Diamond7diamond[^ ]*]] to i64), i64 ptrtoint (ptr @vtable.0 to i64)) to i32)], align 4

#[no_mangle]
pub fn upcast_diamond_to_b(x: Box<dyn Diamond>) -> Box<dyn B> {
    // CHECK-LABEL: define { ptr, ptr } @upcast_diamond_to_b(ptr align 1 %x.0, ptr align 8 %x.1)
    // CHECK: [[UPCAST_SLOT_PRT:%.+]] = {{.*}}call ptr @llvm.load.relative.i32(ptr %x.1, i32 24)
    // CHECK: [[RES0:%.+]] = insertvalue { ptr, ptr } poison, ptr %x.0, 0
    // CHECK: [[RES1:%.+]] = insertvalue { ptr, ptr } [[RES0]], ptr [[UPCAST_SLOT_PRT]], 1
    // CHECK: ret { ptr, ptr } [[RES1]]
    x as Box<dyn B>
}

struct S;
impl Base for S {
    fn base(&self) {}
}
impl A for S {
    fn a(&self) {}
}
impl B for S {
    fn b(&self) {}
}
impl Diamond for S {
    fn diamond(&self) {}
}

pub fn create_diamond() -> Box<dyn Diamond> {
    Box::new(S)
}
