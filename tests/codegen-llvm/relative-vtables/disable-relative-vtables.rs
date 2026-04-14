//@ compile-flags: -Zexperimental-relative-rust-abi-vtables=n

#![crate_type = "lib"]

// CHECK:      @vtable.0 = private {{.*}}constant <{ [24 x i8], ptr, ptr }> <{ [24 x i8] {{.*}}, ptr @{{.*}}foo{{.*}}, ptr @{{.*}}bar{{.*}} }>

trait MyTrait {
    fn foo(&self);
    fn bar(&self) -> u32;
}

struct Struct {
    u: u32,
}

impl MyTrait for Struct {
    fn foo(&self) {}
    fn bar(&self) -> u32 {
        self.u
    }
}

pub fn create_struct() -> Box<dyn MyTrait> {
    Box::new(Struct { u: 1 })
}

// CHECK-LABEL: define void @{{.*}}invoke_foo{{.*}}
// CHECK:         [[GEP:%.*]] = getelementptr inbounds {{.*}}i8, ptr [[VTABLE:%.*]], i64 24
// CHECK:         [[FUNC:%.*]] = load ptr, ptr [[GEP]]
// CHECK-NOT:     @llvm.load.relative
// CHECK:         tail call void [[FUNC]]
pub fn invoke_foo(x: &dyn MyTrait) {
    x.foo();
}
