// run-pass
// needs-sanitizer-cfi
// compile-flags: -Zsanitizer=cfi -Clto -Ccodegen-units=1 -Copt-level=3 -Zexperimental-relative-rust-abi-vtables=y

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
