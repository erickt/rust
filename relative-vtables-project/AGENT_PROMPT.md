# Agent Guidance: Implementing Relative VTables in Rust

This document serves as a high-level guide for agents working on the implementation of PIC-friendly relative vtables for Rust.

## Onboarding
Before starting any work, the agent MUST:
1.  Read Rust's `README.md` to understand the project structure and build system.
2.  Read the `relative-vtables-project/design_doc.md` to understand the technical approach.
3.  Run `./x.py build --quiet` to ensure the current state of the codebase is not broken.
4.  Read through all tasks in `relative-vtables-project/tasks/relative-vtables/` to understand the upcoming work.

## Project Structure
- `relative-vtables-project/tasks`: Contains granular task files (1-5) and an `overview.md`.
- `relative-vtables-project/completed-tasks/`: Move finished task files here.
- `relative-vtables-project/experiments/`: Directory for storing temporary build artifacts, LLVM IR (`.ll`, `.bc`), and other experimental data.
- `relative-vtables-project/ideas/`: Store new issues, improvements, or future work items here.
- `relative-vtables-project/status`: Append periodic updates about current activities and trial results.
- `compiler/rustc_codegen_llvm/src/consts.rs`: Primary location for vtable codegen adjustments.
- `compiler/rustc_ty_utils/src/abi.rs`: ABI layout adjustments.

## Workflow Instructions
1.  **Sequential Execution**: Tasks should be worked on in numerical order (Task 1 through Task 5). Each task depends on the success and implementation of the previous one.
2.  **Experimentation**: When testing or verifying a change, save all generated LLVM IR, assembly, or binary snippets in `relative-vtables-project/experiments/` to preserve context for the next agent.
3.  **Check-in Often**: Frequent commits are required to maintain context. Follow this commit message format:
    ```
    <concise description>

    <detailed description>
    <results>
    ```
4.  **Reference Implementation**: Refer to Clang's implementation in `src/llvm-project/clang/lib/CodeGen/CGVTables.cpp` for how LLVM's `dso_local_equivalent` and `load.relative` are used.
5.  **Status Reporting**: Maintain a log in `relative-vtables-project/status`. Periodically append info about what you are currently doing and what you have tried that worked or did not work.

## Testing Procedure
Follow these steps in order to verify changes:
1.  `./x.py check --quiet`
2.  `./x.py build --quiet`
3.  `./x.py test --skip tests/debuginfo --skip tests/rustdoc-ui` (skipping known failing tests).

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

## Task Overview
1.  **Task 1**: Flags & Configuration (Restore `-Zexperimental-relative-rust-abi-vtables`).
2.  **Task 2**: ABI Layout (Adjust alignment and size for relative pointers).
3.  **Task 3**: Core Codegen (Emit relative offsets using LLVM intrinsics).
4.  **Task 4**: Upcasting (Fix complex layout and supertrait issues).
5.  **Task 5**: Full Verification (End-to-end testing and performance/size checks).

Refer to the individual task files for detailed requirements and move them to `completed-tasks/` once finished.
