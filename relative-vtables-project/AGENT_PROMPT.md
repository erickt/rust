# Agent Guidance: Implementing Relative VTables in Rust

This document serves as a high-level guide for agents working on the implementation of PIC-friendly relative vtables for Rust.

## Onboarding
Before starting any work, the agent MUST:
1.  Read Rust's `README.md` to understand the project structure and build system.
2.  Read the `relative-vtables-project/design_doc.md` to understand the technical approach.
3.  Read through all open tasks in `relative-vtables-project/tasks/`, explore previous work in `relative-vtables-project/ideas/`, and check the latest progress in `relative-vtables-project/status`.
4.  Run `./x.py build --quiet` to ensure the current state of the codebase is not broken.

## Project Structure
- `relative-vtables-project/tasks/`: Contains granular, descriptively named task files (e.g., `01_compiler_flags_and_session_options.md`).
- `relative-vtables-project/completed-tasks/`: Move finished task files here.
- `relative-vtables-project/experiments/`: Directory for storing temporary build artifacts, LLVM IR (`.ll`, `.bc`), and other experimental data.
- `relative-vtables-project/ideas/`: Store new issues, improvements, or future work items here.
- `relative-vtables-project/status`: Append periodic updates about current activities and trial results.
- `compiler/rustc_codegen_llvm/src/consts.rs`: Primary location for vtable codegen adjustments.
- `compiler/rustc_ty_utils/src/abi.rs`: ABI layout adjustments.

## Workflow Instructions
1.  **Sequential Execution**: Tasks should be worked on in numerical order. Each task depends on the success and implementation of the previous one.
2.  **Descriptive Task Naming**: When creating new tasks, use a descriptive name that clearly states the task's objective (e.g., `XX_feature_name.md`).
3.  **Experimentation**: When testing or verifying a change, save all generated LLVM IR, assembly, or binary snippets in `relative-vtables-project/experiments/` to preserve context for the next agent.
4.  **LSP Priority**: Prioritize using the `lsp` skill to search code (`view_file_outline`, `view_code_item`) and observe problems before shelling out to expensive build commands. Iterate on fixing LSP-reported diagnostics after editing code.
5.  **Check-in Often**: Frequent commits are required to maintain context. Follow this commit message format:
    ```
    <concise description>

    <detailed description>
    <results>
    ```
5.  **Stop on Authentication**: If you are prompted for `gcert` or any other interactive authentication, STOP and notify the user.
6.  **Reference Implementation**: Refer to Clang's implementation in `src/llvm-project/clang/lib/CodeGen/CGVTables.cpp` for how LLVM's `dso_local_equivalent` and `load.relative` are used.
7.  **Status Reporting**: Maintain a log in `relative-vtables-project/status`. Periodically append info about what you are currently doing and what you have tried that worked or did not work.

## Toolchain Usage
If you want to run the compiler you just built with `cargo`, use the following commands:
- **Stage 1**: `rustup run stage1 cargo ...`
- **Stage 2**: `rustup run stage2 cargo ...`

## Testing Procedure
Follow these steps in order to verify changes:
1.  `./x.py check --quiet`
2.  `./x.py build --quiet`
3.  `./x.py test --skip tests/debuginfo --skip tests/rustdoc-ui` (skipping known failing tests).
4.  (Once tests pass) Verify with external crates (e.g., `reqwest`):
    - Without feature: `rustup run stage1 cargo build --example simple`
    - With feature: `RUSTFLAGS="-Zexperimental-relative-rust-abi-vtables=y" rustup run stage1 cargo build --example simple`

## Documentation
Always update `relative-vtables-project/design_doc.md` if the implementation approach changes significantly. Ensure the document remains the source of truth for the design.

## Idea Tracking
If you discover a new issue, improvement, or future work item, add a new file to `relative-vtables-project/ideas/` with the following format:
```
<title>
---
priority: high / low

<description>
<root cause if known>
<suggested approach>
<key files involved>
```

Refer to the individual, descriptively named task files in `relative-vtables-project/tasks/` for detailed requirements. Move them to `completed-tasks/` once finished.
