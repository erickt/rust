# Task 4: Trait Upcasting & Complex VTable Layouts

## Objective
Ensure that relative vtables work correctly for complex inheritance hierarchies, including trait upcasting and supertraits.

## Requirements
- Support trait upcasting for complex hierarchies (supertraits).
- **New**: Implement "VTable Group Splitting" – emitting separate globals for each vtable in a group to support dead virtual function stripping.
- Fix regressions in `supertrait-vtable.rs` and related tests.
- Resolve regressions in trait upcasting by ensuring offsets are correctly calculated in a relative layout.
- Update `compiler/rustc_codegen_llvm` to handle `TraitVPtr` during vtable construction for upcasting.
- Verify correctness for diamond inheritance and multiple supertraits.

## Reference
- Commit `d3518bc29f3d04a697643fbf74caee33f8f03f8c`: Fixes for `supertrait-vtable.rs` and upcasting regressions.
