//@ compile-flags: -Zexperimental-relative-rust-abi-vtables=y
//@ aux-build: cross-crate-vtable-aux.rs

#![crate_type = "lib"]

extern crate cross_crate_vtable_aux;

use cross_crate_vtable_aux::{CrossCrateStruct, CrossCrateTrait};

// CHECK: @vtable.{{.*}} = private {{.*}}constant [4 x i32] [
// CHECK-SAME:   i32 0,
// CHECK-SAME:   i32 0,
// CHECK-SAME:   i32 1,
// CHECK-SAME:   i32 trunc (i64 sub (i64 sub (i64 ptrtoint (ptr dso_local_equivalent {{.*}}cross_crate_method{{.*}} to i64), i64 ptrtoint (ptr @vtable.{{.*}} to i64)), i64 12) to i32)
// CHECK-SAME: ], align 4

pub fn create_cross_crate() -> Box<dyn CrossCrateTrait> {
    Box::new(CrossCrateStruct)
}
