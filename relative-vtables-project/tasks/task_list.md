# Task List: Relative VTable Support

## Research & Design
- [x] Research Clang/LLVM implementation of relative vtables
    - [x] Search `src/llvm-project` for relative vtable implementation
    - [x] Review slide deck on C++ relative vtables
- [x] Analyze existing Rust prototype (commit `da587faa812aaf03df6d5319783be1a754cbd9f5`)
- [x] Analyze prior session progress (commit `d3518bc29f3d04a697643fbf74caee33f8f03f8c`)
- [x] Design the task breakdown for multiple agents
- [x] Create task markdown files
- [x] Research LLVM/Clang test coverage for relative vtables
- [x] Draft Detailed Design Document
    - [x] Explain mechanism (dso_local_equivalent, load.relative)
    - [x] Document CFI/LTO interactions
    - [x] Define testing strategy and edge cases
- [x] Update agent prompt with onboarding and testing workflow

## Implementation
- [x] 01_compiler_flags_and_session_options.md
- [x] 02_middle_end_and_abi_adjustments.md
- [x] 03_llvm_codegen_implementation.md
- [/] 04_trait_upcasting_and_complex_layouts.md
- [ ] 05_verification_and_testing.md
- [ ] 06_external_crate_verification.md
