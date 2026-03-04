# Task 8: CFI and kCFI Support

## Objective
Implement Control Flow Integrity (CFI) and kernel Control Flow Integrity (kCFI) metadata and checks for relative vtables to prevent control-flow hijacking attacks.

## Requirements
1.  **Metadata Generation**: Ensure `rustc_codegen_llvm` attaches the necessary `type` metadata to relative vtable definitions so LLVM can use them for indirect call checking.
2.  **Call Site Lowering**: Update `load_vtable` and the dynamic dispatch generation in `meth.rs` to emit `@llvm.type.test` or direct kCFI checks during method invocation when relative vtables are enabled.
3.  **Cross-Crate CFI**: Ensure the CFI hashes correctly identify identically typed traits across crate boundaries (even when vtables are deduplicated by ICF or exist in separate translation units).
4.  **Graceful Degradation/Incompatibility Detection**: If full CFI/kCFI isn't technically possible yet with LLVM's relative vtable intrinsic implementation, identify the gaps and emit warnings/errors when both `-Zexperimental-relative-rust-abi-vtables` and `-Zsanitizer=cfi/kcfi` are provided.

## Reference
- LLVM RFC on Virtual Call ABI
- Clang implementation of CFI with Relative VTables. `clang/lib/CodeGen/CGVTables.cpp` and `clang/test/CodeGenCXX/cfi-relative-vtables.cpp`.
- Rust issue #[rust-lang/rust/issues/89653] regarding CFI implementation.

## Verification
- [ ] Add `tests/ui/sanitizer/cfi-relative-vtables.rs` to verify dynamic calls trap on invalid types.
- [ ] Ensure `x.py test --stage 1 tests/ui/sanitizer/` passes with relative vtables on.
- [ ] Confirm `ui` Tests pass without regressions.
