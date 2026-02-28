# Task 2: Middle-end & ABI Adjustments

## Objective
Update the compiler middle-end to account for the new relative vtable layout in ABI calculations.

## Requirements
- Modify `compiler/rustc_ty_utils/src/abi.rs` to adjust `pointee_align` and `pointee_size` for vtable pointers when relative vtables are enabled.
- Ensure that vtable pointers are treated as pointing to `i32` offsets rather than absolute function pointers.
- Verify that `rustc_middle::ty::vtable` correctly represents the components of a relative vtable.

## Reference
- Commit `da587faa812aaf03df6d5319783be1a754cbd9f5`: Initial ABI adjustments in `abi.rs`.

## Verification
- [ ] Run `./x.py check --stage 1 --quiet`
- [ ] Run `./x.py test --stage 1 --skip tests/debuginfo --skip tests/rustdoc-ui`
- [ ] **CRITICAL**: Confirm all tests pass (excluding known pre-existing failures).
