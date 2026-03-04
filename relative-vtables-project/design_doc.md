# Design Document: Relative VTables for Rust

## Motivation
Standard vtables in Rust (and C++) consist of absolute pointers to functions and RTTI. This requires a dynamic relocation for every vtable entry in Position-Independent Code (PIC), which increases binary size and startup time. Relative vtables replace these absolute pointers with 32-bit relative offsets, significantly reducing the number of relocations and allowing for better code sharing.

## Mechanism

### VTable Layout
A relative vtable is an array of `i32` offsets. Each offset is calculated relative to the "address point" of the vtable.

- **Non-relative**: `[ptr null, ptr RTTI, ptr fun1, ptr fun2, ...]`
- **Non-relative**: `[ptr null, ptr RTTI, ptr fun1, ptr fun2, ...]`
- **Relative**: `[i32 offset_to_RTTI, i32 offset_to_fun1, i32 offset_to_fun2, ...]`

### VTable Group Splitting
To simplify Dead Virtual Function Stripping and improve CFI efficiency, the relative ABI splits vtable groups (for classes with multiple bases) into separate globals instead of one large contiguous global. Each vtable global should be named appropriately (e.g., `@A_vtable`).

### LLVM Backend Support
The implementation relies on two key LLVM features:

1.  **`dso_local_equivalent`**: Used to represent a function pointer in a way that LLVM can reliably calculate a relative offset to it, even if the function might be overridden or located in a different translation unit in some configurations. It ensures the symbol is effectively local for the purpose of offset calculation.
2.  **`llvm.load.relative`**: An intrinsic designed to load a value from a relative offset. It takes a base pointer and an `i32` offset.
    - IR: `%ptr = call ptr @llvm.load.relative.i32(ptr %vtable, i32 %offset)`
3.  **`llvm.vtable.slot.offset`**: (Important for LTO/WPD) This intrinsic returns the byte offset of a specific virtual function slot within a vtable. Using this instead of hardcoded constants allows LLVM to reshape or reorder vtables during optimization.
    - IR: `%offset = call i32 @llvm.vtable.slot.offset(metadata !"TraitName", i32 0)`

### RTTI Proxies
The RTTI component might be located in a different linkage unit than the vtable. To handle this, a "proxy" variable is created with internal or `linkonce_odr` linkage that points to the actual RTTI. The vtable then stores a relative offset to this proxy.

## Interactions with Advanced Features

### Control Flow Integrity (CFI)
CFI relies on type metadata annotated on vtables. When relative vtables are enabled:
1.  **Load Intrinsic**: Instead of `llvm.type.checked.load`, the compiler must use `llvm.type.checked.load.relative`.
2.  **Metadata Offsets**: The byte offsets in `!type` metadata must be adjusted because the vtable components are now 4-byte `i32`s instead of 8-byte pointers (on 64-bit systems).
3.  **GlobalDCE**: Global Dead Code Elimination for virtual functions must be aware of the relative layout and `dso_local_equivalent` to correctly identify used functions.

### Link-Time Optimization (LTO)
LTO and Whole-Program VTable (WPD) optimizations (like devirtualization) must be compatible with the relative layout. LLVM already supports this via the relative versions of the type-checked load intrinsics.

## Testing Strategy

### LLVM/Clang Parity
We should mirror the coverage found in LLVM's `type-metadata.cpp` and `RelativeVTablesABI/` tests:
1.  **Layout Verification**: Ensure the generated IR uses `i32` and correct `trunc (sub ...)` expressions.
2.  **Lookup Verification**: Ensure `llvm.load.relative` is used for method calls.
3.  **Upcasting**: Test complex hierarchies (supertrait upcasting) to ensure offsets are correctly handled when moving between vtables.
4.  **Negative Guards**: Verify that relative vtables are correctly disabled when incompatible flags (like CFI on certain platforms) are used.

### Rust-Specific Tests
1.  **Trait Objects**: All trait object operations (method call, `drop_in_place`).
2.  **Supertraits**: Upcasting from child trait objects to parent trait objects.
5.  **CFI Integration**: Explicitly test that `rustc` with CFI + relative vtables generates the correct `llvm.type.checked.load.relative` calls.
    
## Implementation Details and Rationale

The final implementation in the Rust compiler differs slightly from the initial theoretical LLVM design in order to accommodate Rust-specific ABI requirements and edge cases.

### 1. 4-Byte Metadata Extraction vs 8-Byte Absolute Metadata
When extracting the `size` and `align` components from a `dyn Trait` object, absolute vtables simply offset into an array of 8-byte pointers (`*mut u8` and `usize`). Relative vtables pack all elements sequentially as 4-byte `i32` relative offsets. 
- **Rationale**: Rust's `load_vtable` function in the LLVM backend (`rustc_codegen_llvm/src/builder.rs`) was adjusted to properly extract a sequential 4-byte element and zero-extend it (`zext`) to machine-word size (e.g. `i64`). If we used 8-byte loads against a packed `i32` sequence, we would read two offset values simultaneously, destroying the program integrity.

### 2. Upcasting and NULL Pointer Displacement
Rust frequently relies on the capacity to represent optionally present virtual method slots and trait super-hierarchies, where unused upcasting slots might be initialized as `ptr null`.
- **Rationale**: A relative `null` is fundamentally meaningless in algebraic offset logic. We chose to structurally emit `i32 0` directly for any function pointer slot that evaluates to `null` provenance. This guarantees the offset calculation safely skips zeroed memory slots, avoiding LLVM's integer arithmetic panicking on scalar variables lacking alloc provenance.

### 3. CFI jump tables and `offset` algebra
A critical divergence from naive `Target - Base` geometric distance calculations occurred when we enabled `-Zsanitizer=cfi`. 
- **Rationale**: The core C++ Relative ABI relies on `llvm.load.relative.i32(ptr %vtable, i32 %offset)`, which *algebraically adds* `%offset` to the memory address loaded from `%vtable`. 
- During `LowerTypeTests` LTO passes for CFI, LLVM explicitly substitutes relative indices. Because the intrinsic intrinsically adds the slot index internally, the constant stored in the global `.rodata` segment MUST offset this arithmetic by subtracting the target's explicit structural offset.
- Our final layout formula is `Target - VTable_Base - Slot_Offset`. This completely eliminates jump-table tracking errors caused by LTO offset rewriting without requiring complex `libLTO` manual modifications.
- **CRITICAL**: The `Slot_Offset` must be the geometric offset within the *relative* layout, not the absolute layout. Rust's internal `Size` algorithms yield the byte offset corresponding to 8-byte vtable slots (e.g., slot 3 = 24 bytes). Since relative vtables pack as `i32` elements, the formula must explicitly scaled to `(absolute_offset_bytes / 8) * 4`.

### 4. Cross-Platform Compatibility Support
Rather than permanently modifying every backend configuration simultaneously, the feature is tightly gated under `-Zexperimental-relative-rust-abi-vtables` and the `-Cunsafe-allow-abi-mismatch=sanitizer` pipeline.
- **Rationale**: Different architectures have wildly distinct jump architectures (e.g. AArch64 relative adrp instructions). By bounding the new ABI to experimental flag inclusion, we can rigorously deploy the C++ conformity logic over x86_64 and progressively stabilize the LTO handling on secondary platforms over subsequent compiler release cycles.
