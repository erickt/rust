# Task 6: External Crate Verification

## Objective
Verify that the relative vtables implementation is robust enough to compile and run complex external crates.

## Requirements
1.  **Baseline Verification**: Ensure the stage1 compiler can compile `reqwest` without the feature enabled:
    - `rustup run stage1 cargo build --example simple`
2.  **Feature Verification**: Ensure the stage1 compiler can compile `reqwest` with relative vtables enabled:
    - `RUSTFLAGS="-Zexperimental-relative-rust-abi-vtables=y" rustup run stage1 cargo build --example simple`
3.  **Correctness**: Run the `reqwest` examples and ensure they execute without segmentation faults or ABI-related errors.
4.  **Compatibility**: Verify other complex crates (e.g., `serde`, `tokio`) if time permits to ensure broad ABI compatibility.

## Reference
- RFC #903: Mentions the importance of PIC-friendliness for broad library support.

## Verification
- [ ] Run `./x.py check --stage 1 --quiet`
- [ ] Run `./x.py test --stage 1 --skip tests/debuginfo --skip tests/rustdoc-ui`
- [ ] **CRITICAL**: Confirm all tests pass (excluding known pre-existing failures).
