# Task 1: Core Compiler & Session Options

## Objective
Implement or restore the unstable compiler flag `-Zexperimental-relative-rust-abi-vtables` and set up the basic session configuration.

## Requirements
- Add `experimental_relative_rust_abi_vtables` to `compiler/rustc_session/src/options.rs`.
- Implement target-specific defaults in `compiler/rustc_session/src/config.rs` (e.g., enabling by default for Fuchsia).
- Add safety guards to disable relative vtables when incompatible features like CFI, KCFI, or Virtual Function Elimination (VFE) are enabled.
- Update `src/doc/rustc/src/codegen-options/index.md` to document the new flag.

## Reference
- Commit `da587faa812aaf03df6d5319783be1a754cbd9f5`: Initial flag implementation.
- Commit `d3518bc29f3d04a697643fbf74caee33f8f03f8c`: Safety guards for CFI/VFE.
