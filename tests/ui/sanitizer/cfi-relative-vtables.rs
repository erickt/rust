//@ run-pass
//@ needs-sanitizer-cfi
//@ compile-flags: -Zsanitizer=cfi -Clto -Ccodegen-units=1 -Copt-level=3 -Cunsafe-allow-abi-mismatch=sanitizer -Cprefer-dynamic=no

trait Trait {
    fn foo(&self) -> i32;
}
struct Struct;
impl Trait for Struct {
    fn foo(&self) -> i32 { 42 }
}
fn main() {
    let s = Struct;
    let t: &dyn Trait = &s;
    assert_eq!(t.foo(), 42);
}
