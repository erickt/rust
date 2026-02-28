pub trait Foo { fn bar(&self); } impl Foo for () { fn bar(&self) {} } pub fn use_foo(x: &dyn Foo) { x.bar(); }
