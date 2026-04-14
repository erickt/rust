//@ compile-flags: -Zexperimental-relative-rust-abi-vtables=y

#![crate_type = "lib"]

pub trait CrossCrateTrait {
    fn cross_crate_method(&self);
}

pub struct CrossCrateStruct;

impl CrossCrateTrait for CrossCrateStruct {
    fn cross_crate_method(&self) {}
}
