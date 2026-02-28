# Task 5: Verification & Testing

## Objective
Verify the implementation through comprehensive testing and ensure no regressions in existing features.

## Requirements
- Port and adapt existing tests from `da587faa812aaf03df6d5319783be1a754cbd9f5` and `d3518bc29f3d04a697643fbf74caee33f8f03f8c`:
    - `tests/codegen-llvm/relative-vtables/simple-vtable.rs`
    - `tests/codegen-llvm/relative-vtables/supertrait-vtable.rs`
- Add new UI tests to verify runtime correctness of trait object method calls and upcasting.
- Verify compatibility with LTO and basic CFI (if possible) or ensure it is correctly disabled.
- Benchmark binary size and performance (optional but recommended).
- **Note**: Run tests with `--skip tests/debuginfo --skip tests/rustdoc-ui` to skip pre-existing failures.

## Reference
- Commit `d3518bc29f3d04a697643fbf74caee33f8f03f8c`: Improved test robustness and regex matching.
