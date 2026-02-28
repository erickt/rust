# Task 3: LLVM Codegen Implementation

## Objective
Implement the backend support in `rustc_codegen_llvm` to emit relative vtables and perform lookups using relative offsets.

## Requirements
- Emit relative offsets using `trunc (sub ...)` relative to the vtable address point.
- Use `llvm.dso_local_equivalent` for function pointers in vtables to support PIC.
- Implement vtable lookups using the `llvm.load.relative` intrinsic.
- **New**: Use `llvm.vtable.slot.offset` for calculating slot offsets to enable better LLVM optimizations (LTO/WPD).
- Ensure proper alignment and section placement for relative vtables.
- Store temporary LLVM IR, assembly, and experimental artifacts in `relative-vtables-project/experiments/`.
- (Optional) Implement RTTI proxies if required for compatibility, similar to Clang's `.rtti_proxy`.

## Reference
- Clang implementation in `clang/lib/CodeGen/CGVTables.cpp`.
- Commit `da587faa812aaf03df6d5319783be1a754cbd9f5`: Initial codegen support.
- Commit `d3518bc29f3d04a697643fbf74caee33f8f03f8c`: Backend consistency fixes.

## Verification
- [ ] Run `./x.py check --stage 1 --quiet`
- [ ] Run `./x.py test --stage 1 --skip tests/debuginfo --skip tests/rustdoc-ui`
- [ ] **CRITICAL**: Confirm all tests pass (excluding known pre-existing failures).
