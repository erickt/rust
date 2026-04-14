; ModuleID = 'simple_vtable.eca59c2d9e176ad3-cgu.0'
source_filename = "simple_vtable.eca59c2d9e176ad3-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%"core::fmt::rt::Argument<'_>" = type { %"core::fmt::rt::ArgumentType<'_>" }
%"core::fmt::rt::ArgumentType<'_>" = type { ptr, [1 x i64] }

@alloc_94b9d93a972c9ddf5a033fb4b08ba432 = private unnamed_addr constant [28 x i8] c"library/core/src/ptr/mod.rs\00", align 1
@alloc_5f470752059900a83e2ef10e24113e49 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_94b9d93a972c9ddf5a033fb4b08ba432, [16 x i8] c"\1B\00\00\00\00\00\00\00\0F\02\00\00\05\00\00\00" }>, align 8
@alloc_4e0b9646061945c00d0edbf1d69fff6a = private unnamed_addr constant [29 x i8] c"library/alloc/src/vec/mod.rs\00", align 1
@alloc_98e4901a4d77aa9832f944d6010d68f1 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_4e0b9646061945c00d0edbf1d69fff6a, [16 x i8] c"\1C\00\00\00\00\00\00\00r\08\00\00\09\00\00\00" }>, align 8
@vtable.0 = private unnamed_addr constant [5 x i32] [i32 0, i32 4, i32 4, i32 trunc (i64 sub (i64 sub (i64 ptrtoint (ptr dso_local_equivalent @_RNvXs_CskjFhZNFXKrT_13simple_vtableNtB4_7Struct2NtB4_7MyTrait3foo to i64), i64 ptrtoint (ptr @vtable.0 to i64)), i64 24) to i32), i32 trunc (i64 sub (i64 sub (i64 ptrtoint (ptr dso_local_equivalent @_RNvXs_CskjFhZNFXKrT_13simple_vtableNtB4_7Struct2NtB4_7MyTrait3bar to i64), i64 ptrtoint (ptr @vtable.0 to i64)), i64 32) to i32)], align 4
@alloc_13af184f83ea529683dab3456027e412 = private unnamed_addr constant [3 x i8] c"abc", align 1
@vtable.1 = private unnamed_addr constant [5 x i32] [i32 trunc (i64 sub (i64 ptrtoint (ptr dso_local_equivalent @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeNtCskjFhZNFXKrT_13simple_vtable6StructEBI_ to i64), i64 ptrtoint (ptr @vtable.1 to i64)) to i32), i32 24, i32 8, i32 trunc (i64 sub (i64 sub (i64 ptrtoint (ptr dso_local_equivalent @_RNvXCskjFhZNFXKrT_13simple_vtableNtB2_6StructNtB2_7MyTrait3foo to i64), i64 ptrtoint (ptr @vtable.1 to i64)), i64 24) to i32), i32 trunc (i64 sub (i64 sub (i64 ptrtoint (ptr dso_local_equivalent @_RNvXCskjFhZNFXKrT_13simple_vtableNtB2_6StructNtB2_7MyTrait3bar to i64), i64 ptrtoint (ptr @vtable.1 to i64)), i64 32) to i32)], align 4
@alloc_d9b93e2770fc27f14fdfffcf6febca6d = private unnamed_addr constant [33 x i8] c"library/core/src/ptr/non_null.rs\00", align 1
@alloc_4693b25d3eabde0252d3a3cfc0a04ff1 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_d9b93e2770fc27f14fdfffcf6febca6d, [16 x i8] c" \00\00\00\00\00\00\00\AA\05\00\00\12\00\00\00" }>, align 8
@anon.42aad29631b5bed5b04828ecca743db5.0 = private unnamed_addr constant <{ [8 x i8], [8 x i8] }> <{ [8 x i8] zeroinitializer, [8 x i8] undef }>, align 8
@alloc_5ba1495433bc7bd4d57e2fc7e46f3ce7 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_d9b93e2770fc27f14fdfffcf6febca6d, [16 x i8] c" \00\00\00\00\00\00\00\10\01\00\00\1B\00\00\00" }>, align 8
@alloc_462d48c71ecbcc11b125140bcb84ed12 = private unnamed_addr constant [34 x i8] c"library/core/src/ptr/const_ptr.rs\00", align 1
@alloc_97ea21a74f677b9ef8611233fc5bfdff = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_462d48c71ecbcc11b125140bcb84ed12, [16 x i8] c"!\00\00\00\00\00\00\00a\05\00\00\17\00\00\00" }>, align 8
@alloc_fad0cd83b7d1858a846a172eb260e593 = private unnamed_addr constant [42 x i8] c"is_aligned_to: align is not a power-of-two", align 1
@alloc_fc9ab3224673f8be7b78582aac5df6a6 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_462d48c71ecbcc11b125140bcb84ed12, [16 x i8] c"!\00\00\00\00\00\00\00^\05\00\00\0D\00\00\00" }>, align 8
@alloc_0a6a989224bce28eb2f5fb5f80443071 = private unnamed_addr constant [33 x i8] c"library/alloc/src/raw_vec/mod.rs\00", align 1
@alloc_ce9f95331637087388e965745b6757b6 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_0a6a989224bce28eb2f5fb5f80443071, [16 x i8] c" \00\00\00\00\00\00\00\B5\01\00\00\15\00\00\00" }>, align 8
@alloc_0625062a5eee489a7813ee965a38d15a = private unnamed_addr constant [198 x i8] c"unsafe precondition(s) violated: Alignment::new_unchecked requires a power of two\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@alloc_8cf3531fd3c828ab298b686071a40c17 = private unnamed_addr constant [259 x i8] c"unsafe precondition(s) violated: Layout::from_size_alignment_unchecked requires that the rounded-up allocation size does not exceed isize::MAX\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@alloc_560a59ed819b9d9a5841f6e731c4c8e5 = private unnamed_addr constant [210 x i8] c"unsafe precondition(s) violated: NonNull::new_unchecked requires that the pointer is non-null\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@alloc_57d70e9d94c65ecfc15225d29a5ed72b = private unnamed_addr constant [198 x i8] c"unsafe precondition(s) violated: Vec::set_len requires that new_len <= capacity()\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@alloc_bd3468a7b96187f70c1ce98a3e7a63bf = private unnamed_addr constant [283 x i8] c"unsafe precondition(s) violated: ptr::copy_nonoverlapping requires that both pointer arguments are aligned and non-null and the specified memory ranges do not overlap\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@alloc_64e308ef4babfeb8b6220184de794a17 = private unnamed_addr constant [221 x i8] c"unsafe precondition(s) violated: hint::assert_unchecked must never be called when the condition is false\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1
@alloc_dce51cf9e5104603cc1941c9c61f00a7 = private unnamed_addr constant [28 x i8] c"library/core/src/num/mod.rs\00", align 1
@alloc_86b951561bf1022fc084636771000468 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_dce51cf9e5104603cc1941c9c61f00a7, [16 x i8] c"\1B\00\00\00\00\00\00\00x\05\00\00\05\00\00\00" }>, align 8
@alloc_763310d78c99c2c1ad3f8a9821e942f3 = private unnamed_addr constant [61 x i8] c"is_nonoverlapping: `size_of::<T>() * count` overflows a usize", align 1
@alloc_724bfa08d8112cb0bda01416cbde3db0 = private unnamed_addr constant [16 x i8] c"\0BStruct foo \C0\01\0A\00", align 1
@alloc_15e44448982b88d2e5ac1289a6e5f540 = private unnamed_addr constant [34 x i8] c"library/core/src/ptr/alignment.rs\00", align 1
@alloc_1dd1f17b7d26b1300b870840ad476677 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_15e44448982b88d2e5ac1289a6e5f540, [16 x i8] c"!\00\00\00\00\00\00\00\7F\00\00\00\12\00\00\00" }>, align 8
@alloc_478cc3c807941c07ea2a306b26093e01 = private unnamed_addr constant [33 x i8] c"library/core/src/alloc/layout.rs\00", align 1
@alloc_500d4670593dfc9f2e6da26af3f15b8b = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_478cc3c807941c07ea2a306b26093e01, [16 x i8] c" \00\00\00\00\00\00\00\01\01\00\00\12\00\00\00" }>, align 8
@alloc_d23184c8762add5bca60e3eefedad428 = private unnamed_addr constant [17 x i8] c"\0CStruct2 foo \C0\01\0A\00", align 1

; <core::fmt::rt::Argument>::new_display::<alloc::string::String>
; Function Attrs: inlinehint nonlazybind uwtable
define void @_RINvMNtNtCsl1Y3iNB2xjl_4core3fmt2rtNtB3_8Argument11new_displayNtNtCsdHhxNI3WGqv_5alloc6string6StringECskjFhZNFXKrT_13simple_vtable(ptr sret([16 x i8]) align 8 %_0, ptr align 8 %x) unnamed_addr #0 {
start:
  %_2 = alloca [16 x i8], align 8
  store ptr %x, ptr %_2, align 8
  %0 = getelementptr inbounds i8, ptr %_2, i64 8
  store ptr @_RNvXsq_NtCsdHhxNI3WGqv_5alloc6stringNtB5_6StringNtNtCsl1Y3iNB2xjl_4core3fmt7Display3fmtCskjFhZNFXKrT_13simple_vtable, ptr %0, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_2, i64 16, i1 false)
  ret void
}

; <core::fmt::rt::Argument>::new_display::<u32>
; Function Attrs: inlinehint nonlazybind uwtable
define void @_RINvMNtNtCsl1Y3iNB2xjl_4core3fmt2rtNtB3_8Argument11new_displaymECskjFhZNFXKrT_13simple_vtable(ptr sret([16 x i8]) align 8 %_0, ptr align 4 %x) unnamed_addr #0 {
start:
  %_2 = alloca [16 x i8], align 8
  store ptr %x, ptr %_2, align 8
  %0 = getelementptr inbounds i8, ptr %_2, i64 8
  store ptr @_RNvXs8_NtNtNtCsl1Y3iNB2xjl_4core3fmt3num3impmNtB9_7Display3fmt, ptr %0, align 8
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %_2, i64 16, i1 false)
  ret void
}

; <core::fmt::Arguments>::new::<16, 1>
; Function Attrs: inlinehint nonlazybind uwtable
define { ptr, ptr } @_RINvMs2_NtCsl1Y3iNB2xjl_4core3fmtNtB6_9Arguments3newKj10_Kj1_ECskjFhZNFXKrT_13simple_vtable(ptr align 1 %template, ptr align 8 %args) unnamed_addr #0 {
start:
  %0 = insertvalue { ptr, ptr } poison, ptr %template, 0
  %1 = insertvalue { ptr, ptr } %0, ptr %args, 1
  ret { ptr, ptr } %1
}

; <core::fmt::Arguments>::new::<17, 1>
; Function Attrs: inlinehint nonlazybind uwtable
define { ptr, ptr } @_RINvMs2_NtCsl1Y3iNB2xjl_4core3fmtNtB6_9Arguments3newKj11_Kj1_ECskjFhZNFXKrT_13simple_vtable(ptr align 1 %template, ptr align 8 %args) unnamed_addr #0 {
start:
  %0 = insertvalue { ptr, ptr } poison, ptr %template, 0
  %1 = insertvalue { ptr, ptr } %0, ptr %args, 1
  ret { ptr, ptr } %1
}

; core::ptr::drop_in_place::<dyn simple_vtable::MyTrait>
; Function Attrs: nonlazybind uwtable
define void @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeDNtCskjFhZNFXKrT_13simple_vtable7MyTraitEL_EBJ_(ptr align 1 %_1.0, ptr align 4 %_1.1) unnamed_addr #1 {
start:
  %0 = call ptr @llvm.load.relative.i32(ptr %_1.1, i32 0), !invariant.load !3
  %1 = icmp ne ptr %0, %_1.1
  br i1 %1, label %is_not_null, label %bb1

is_not_null:                                      ; preds = %start
  call void %0(ptr %_1.0) #15
  br label %bb1

bb1:                                              ; preds = %is_not_null, %start
  ret void
}

; core::ptr::drop_in_place::<alloc::vec::Vec<u8>>
; Function Attrs: nonlazybind uwtable
define void @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeINtNtCsdHhxNI3WGqv_5alloc3vec3VechEECskjFhZNFXKrT_13simple_vtable(ptr align 8 %_1) unnamed_addr #1 personality ptr @rust_eh_personality {
start:
  %0 = alloca [16 x i8], align 8
; invoke <alloc::vec::Vec<u8> as core::ops::drop::Drop>::drop
  invoke void @_RNvXso_NtCsdHhxNI3WGqv_5alloc3vecINtB5_3VechENtNtNtCsl1Y3iNB2xjl_4core3ops4drop4Drop4dropCs7XHCnmxDBD7_5gimli(ptr align 8 %_1)
          to label %bb4 unwind label %cleanup

bb3:                                              ; preds = %cleanup
; invoke core::ptr::drop_in_place::<alloc::raw_vec::RawVec<u8>>
  invoke void @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeINtNtCsdHhxNI3WGqv_5alloc7raw_vec6RawVechEECskjFhZNFXKrT_13simple_vtable(ptr align 8 %_1) #16
          to label %bb1 unwind label %terminate

cleanup:                                          ; preds = %start
  %1 = landingpad { ptr, i32 }
          cleanup
  %2 = extractvalue { ptr, i32 } %1, 0
  %3 = extractvalue { ptr, i32 } %1, 1
  store ptr %2, ptr %0, align 8
  %4 = getelementptr inbounds i8, ptr %0, i64 8
  store i32 %3, ptr %4, align 8
  br label %bb3

bb4:                                              ; preds = %start
; call core::ptr::drop_in_place::<alloc::raw_vec::RawVec<u8>>
  call void @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeINtNtCsdHhxNI3WGqv_5alloc7raw_vec6RawVechEECskjFhZNFXKrT_13simple_vtable(ptr align 8 %_1)
  ret void

terminate:                                        ; preds = %bb3
  %5 = landingpad { ptr, i32 }
          filter [0 x ptr] zeroinitializer
; call core::panicking::panic_in_cleanup
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking16panic_in_cleanup() #17
  unreachable

bb1:                                              ; preds = %bb3
  %6 = load ptr, ptr %0, align 8
  %7 = getelementptr inbounds i8, ptr %0, i64 8
  %8 = load i32, ptr %7, align 8
  %9 = insertvalue { ptr, i32 } poison, ptr %6, 0
  %10 = insertvalue { ptr, i32 } %9, i32 %8, 1
  resume { ptr, i32 } %10
}

; core::ptr::drop_in_place::<alloc::boxed::Box<dyn simple_vtable::MyTrait>>
; Function Attrs: nonlazybind uwtable
define void @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeINtNtCsdHhxNI3WGqv_5alloc5boxed3BoxDNtCskjFhZNFXKrT_13simple_vtable7MyTraitEL_EEB1i_(ptr align 8 %_1) unnamed_addr #1 personality ptr @rust_eh_personality {
start:
  %0 = alloca [16 x i8], align 8
  %_6.0 = load ptr, ptr %_1, align 8
  %1 = getelementptr inbounds i8, ptr %_1, i64 8
  %_6.1 = load ptr, ptr %1, align 8
  %2 = call ptr @llvm.load.relative.i32(ptr %_6.1, i32 0), !invariant.load !3
  %3 = icmp ne ptr %2, %_6.1
  br i1 %3, label %is_not_null, label %bb3

is_not_null:                                      ; preds = %start
  invoke void %2(ptr %_6.0)
          to label %bb3 unwind label %cleanup

bb3:                                              ; preds = %is_not_null, %start
; call <alloc::boxed::Box<dyn simple_vtable::MyTrait> as core::ops::drop::Drop>::drop
  call void @_RNvXs8_NtCsdHhxNI3WGqv_5alloc5boxedINtB5_3BoxDNtCskjFhZNFXKrT_13simple_vtable7MyTraitEL_ENtNtNtCsl1Y3iNB2xjl_4core3ops4drop4Drop4dropBK_(ptr align 8 %_1) #15
  ret void

bb4:                                              ; preds = %cleanup
; invoke <alloc::boxed::Box<dyn simple_vtable::MyTrait> as core::ops::drop::Drop>::drop
  invoke void @_RNvXs8_NtCsdHhxNI3WGqv_5alloc5boxedINtB5_3BoxDNtCskjFhZNFXKrT_13simple_vtable7MyTraitEL_ENtNtNtCsl1Y3iNB2xjl_4core3ops4drop4Drop4dropBK_(ptr align 8 %_1) #16
          to label %bb1 unwind label %terminate

cleanup:                                          ; preds = %is_not_null
  %4 = landingpad { ptr, i32 }
          cleanup
  %5 = extractvalue { ptr, i32 } %4, 0
  %6 = extractvalue { ptr, i32 } %4, 1
  store ptr %5, ptr %0, align 8
  %7 = getelementptr inbounds i8, ptr %0, i64 8
  store i32 %6, ptr %7, align 8
  br label %bb4

terminate:                                        ; preds = %bb4
  %8 = landingpad { ptr, i32 }
          filter [0 x ptr] zeroinitializer
; call core::panicking::panic_in_cleanup
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking16panic_in_cleanup() #17
  unreachable

bb1:                                              ; preds = %bb4
  %9 = load ptr, ptr %0, align 8
  %10 = getelementptr inbounds i8, ptr %0, i64 8
  %11 = load i32, ptr %10, align 8
  %12 = insertvalue { ptr, i32 } poison, ptr %9, 0
  %13 = insertvalue { ptr, i32 } %12, i32 %11, 1
  resume { ptr, i32 } %13
}

; core::ptr::drop_in_place::<alloc::raw_vec::RawVec<u8>>
; Function Attrs: nonlazybind uwtable
define void @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeINtNtCsdHhxNI3WGqv_5alloc7raw_vec6RawVechEECskjFhZNFXKrT_13simple_vtable(ptr align 8 %_1) unnamed_addr #1 {
start:
; call <alloc::raw_vec::RawVec<u8> as core::ops::drop::Drop>::drop
  call void @_RNvXs1_NtCsdHhxNI3WGqv_5alloc7raw_vecINtB5_6RawVechENtNtNtCsl1Y3iNB2xjl_4core3ops4drop4Drop4dropCs7XHCnmxDBD7_5gimli(ptr align 8 %_1)
  ret void
}

; core::ptr::drop_in_place::<simple_vtable::Struct>
; Function Attrs: nonlazybind uwtable
define void @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeNtCskjFhZNFXKrT_13simple_vtable6StructEBI_(ptr align 8 %_1) unnamed_addr #1 {
start:
; call core::ptr::drop_in_place::<alloc::string::String>
  call void @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeNtNtCsdHhxNI3WGqv_5alloc6string6StringECskjFhZNFXKrT_13simple_vtable(ptr align 8 %_1)
  ret void
}

; core::ptr::drop_in_place::<alloc::string::String>
; Function Attrs: nonlazybind uwtable
define void @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeNtNtCsdHhxNI3WGqv_5alloc6string6StringECskjFhZNFXKrT_13simple_vtable(ptr align 8 %_1) unnamed_addr #1 {
start:
; call core::ptr::drop_in_place::<alloc::vec::Vec<u8>>
  call void @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeINtNtCsdHhxNI3WGqv_5alloc3vec3VechEECskjFhZNFXKrT_13simple_vtable(ptr align 8 %_1)
  ret void
}

; <u8 as <[_]>::to_vec_in::ConvertVec>::to_vec::<alloc::alloc::Global>
; Function Attrs: inlinehint nonlazybind uwtable
define void @_RINvXs_NvMNtCsdHhxNI3WGqv_5alloc5sliceSp9to_vec_inhNtB5_10ConvertVec6to_vecNtNtBa_5alloc6GlobalECskjFhZNFXKrT_13simple_vtable(ptr sret([24 x i8]) align 8 %v, ptr align 1 %s.0, i64 %s.1) unnamed_addr #0 {
start:
  %_17 = alloca [8 x i8], align 8
; call <alloc::raw_vec::RawVecInner>::with_capacity_in
  %0 = call { i64, ptr } @_RNvMs4_NtCsdHhxNI3WGqv_5alloc7raw_vecNtB5_11RawVecInner16with_capacity_inCskjFhZNFXKrT_13simple_vtable(i64 %s.1, i64 1, i64 1) #15
  %_10.0 = extractvalue { i64, ptr } %0, 0
  %_10.1 = extractvalue { i64, ptr } %0, 1
  store i64 %_10.0, ptr %v, align 8
  %1 = getelementptr inbounds i8, ptr %v, i64 8
  store ptr %_10.1, ptr %1, align 8
  %2 = getelementptr inbounds i8, ptr %v, i64 16
  store i64 0, ptr %2, align 8
  %_4 = icmp ugt i64 %s.1, 0
  br i1 %_4, label %bb1, label %bb2

bb2:                                              ; preds = %bb9, %start
  ret void

bb1:                                              ; preds = %start
  %3 = getelementptr inbounds i8, ptr %v, i64 8
  %_12 = load ptr, ptr %3, align 8
  br label %bb4

bb4:                                              ; preds = %bb1
; call core::ptr::copy_nonoverlapping::precondition_check
  call void @_RNvNvNtCsl1Y3iNB2xjl_4core3ptr19copy_nonoverlapping18precondition_checkCskjFhZNFXKrT_13simple_vtable(ptr %s.0, ptr %_12, i64 1, i64 1, i64 %s.1, ptr align 8 @alloc_5f470752059900a83e2ef10e24113e49) #18
  br label %bb6

bb6:                                              ; preds = %bb4
  %4 = mul i64 %s.1, 1
  call void @llvm.memcpy.p0.p0.i64(ptr align 1 %_12, ptr align 1 %s.0, i64 %4, i1 false)
  br label %bb7

bb7:                                              ; preds = %bb6
  br label %bb12

bb12:                                             ; preds = %bb7
  %self = load i64, ptr %v, align 8
  store i64 %self, ptr %_17, align 8
  br label %bb10

bb10:                                             ; preds = %bb12
  %5 = load i64, ptr %_17, align 8
; call <alloc::vec::Vec<_, _>>::set_len::precondition_check
  call void @_RNvNvMs_NtCsdHhxNI3WGqv_5alloc3vecINtB6_3VecppE7set_len18precondition_checkCskjFhZNFXKrT_13simple_vtable(i64 %s.1, i64 %5, ptr align 8 @alloc_98e4901a4d77aa9832f944d6010d68f1) #18
  br label %bb9

bb9:                                              ; preds = %bb10
  %6 = getelementptr inbounds i8, ptr %v, i64 16
  store i64 %s.1, ptr %6, align 8
  br label %bb2

bb11:                                             ; No predecessors!
  unreachable
}

; simple_vtable::invoke_foo
; Function Attrs: nonlazybind uwtable
define void @_RNvCskjFhZNFXKrT_13simple_vtable10invoke_foo(ptr align 1 %x.0, ptr align 4 %x.1) unnamed_addr #1 {
start:
  %0 = call ptr @llvm.load.relative.i32(ptr %x.1, i32 12), !invariant.load !3
  call void %0(ptr align 1 %x.0) #15
  ret void
}

; simple_vtable::invoke_drop
; Function Attrs: nonlazybind uwtable
define void @_RNvCskjFhZNFXKrT_13simple_vtable11invoke_drop(i1 zeroext %b) unnamed_addr #1 personality ptr @rust_eh_personality {
start:
  %0 = alloca [16 x i8], align 8
  %bx = alloca [16 x i8], align 8
; call simple_vtable::create_struct
  %1 = call { ptr, ptr } @_RNvCskjFhZNFXKrT_13simple_vtable13create_struct(i1 zeroext %b)
  %2 = extractvalue { ptr, ptr } %1, 0
  %3 = extractvalue { ptr, ptr } %1, 1
  store ptr %2, ptr %bx, align 8
  %4 = getelementptr inbounds i8, ptr %bx, i64 8
  store ptr %3, ptr %4, align 8
  %_5.0 = load ptr, ptr %bx, align 8
  %5 = getelementptr inbounds i8, ptr %bx, i64 8
  %_5.1 = load ptr, ptr %5, align 8
; invoke simple_vtable::invoke_foo
  invoke void @_RNvCskjFhZNFXKrT_13simple_vtable10invoke_foo(ptr align 1 %_5.0, ptr align 4 %_5.1)
          to label %bb2 unwind label %cleanup

bb4:                                              ; preds = %cleanup
; invoke core::ptr::drop_in_place::<alloc::boxed::Box<dyn simple_vtable::MyTrait>>
  invoke void @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeINtNtCsdHhxNI3WGqv_5alloc5boxed3BoxDNtCskjFhZNFXKrT_13simple_vtable7MyTraitEL_EEB1i_(ptr align 8 %bx) #16
          to label %bb5 unwind label %terminate

cleanup:                                          ; preds = %start
  %6 = landingpad { ptr, i32 }
          cleanup
  %7 = extractvalue { ptr, i32 } %6, 0
  %8 = extractvalue { ptr, i32 } %6, 1
  store ptr %7, ptr %0, align 8
  %9 = getelementptr inbounds i8, ptr %0, i64 8
  store i32 %8, ptr %9, align 8
  br label %bb4

bb2:                                              ; preds = %start
; call core::ptr::drop_in_place::<alloc::boxed::Box<dyn simple_vtable::MyTrait>>
  call void @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeINtNtCsdHhxNI3WGqv_5alloc5boxed3BoxDNtCskjFhZNFXKrT_13simple_vtable7MyTraitEL_EEB1i_(ptr align 8 %bx)
  ret void

terminate:                                        ; preds = %bb4
  %10 = landingpad { ptr, i32 }
          filter [0 x ptr] zeroinitializer
; call core::panicking::panic_in_cleanup
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking16panic_in_cleanup() #17
  unreachable

bb5:                                              ; preds = %bb4
  %11 = load ptr, ptr %0, align 8
  %12 = getelementptr inbounds i8, ptr %0, i64 8
  %13 = load i32, ptr %12, align 8
  %14 = insertvalue { ptr, i32 } poison, ptr %11, 0
  %15 = insertvalue { ptr, i32 } %14, i32 %13, 1
  resume { ptr, i32 } %15
}

; simple_vtable::create_struct
; Function Attrs: nonlazybind uwtable
define { ptr, ptr } @_RNvCskjFhZNFXKrT_13simple_vtable13create_struct(i1 zeroext %b) unnamed_addr #1 personality ptr @rust_eh_personality {
start:
  %0 = alloca [16 x i8], align 8
  %1 = alloca [16 x i8], align 8
  %_6 = alloca [24 x i8], align 8
  %_5 = alloca [24 x i8], align 8
  %_2 = alloca [16 x i8], align 8
  br i1 %b, label %bb1, label %bb4

bb4:                                              ; preds = %start
; invoke alloc::boxed::box_new_uninit
  %_3.i1 = invoke ptr @_RNvNtCsdHhxNI3WGqv_5alloc5boxed14box_new_uninitCskjFhZNFXKrT_13simple_vtable(i64 4, i64 4)
          to label %_RNvMNtCsdHhxNI3WGqv_5alloc5boxedINtB2_3BoxNtCskjFhZNFXKrT_13simple_vtable7Struct2E3newBG_.exit unwind label %cleanup.i2

cleanup.i2:                                       ; preds = %bb4
  %2 = landingpad { ptr, i32 }
          cleanup
  %3 = extractvalue { ptr, i32 } %2, 0
  %4 = extractvalue { ptr, i32 } %2, 1
  store ptr %3, ptr %0, align 8
  %5 = getelementptr inbounds i8, ptr %0, i64 8
  store i32 %4, ptr %5, align 8
  %6 = load ptr, ptr %0, align 8
  %7 = getelementptr inbounds i8, ptr %0, i64 8
  %8 = load i32, ptr %7, align 8
  %9 = insertvalue { ptr, i32 } poison, ptr %6, 0
  %10 = insertvalue { ptr, i32 } %9, i32 %8, 1
  resume { ptr, i32 } %10

_RNvMNtCsdHhxNI3WGqv_5alloc5boxedINtB2_3BoxNtCskjFhZNFXKrT_13simple_vtable7Struct2E3newBG_.exit: ; preds = %bb4
  store i32 1, ptr %_3.i1, align 4
  store ptr %_3.i1, ptr %_2, align 8
  %11 = getelementptr inbounds i8, ptr %_2, i64 8
  store ptr @vtable.0, ptr %11, align 8
  br label %bb6

bb1:                                              ; preds = %start
; call <str as alloc::string::ToString>::to_string
  call void @_RNvXsB_NtCsdHhxNI3WGqv_5alloc6stringeNtB5_8ToString9to_stringCskjFhZNFXKrT_13simple_vtable(ptr sret([24 x i8]) align 8 %_6, ptr align 1 @alloc_13af184f83ea529683dab3456027e412, i64 3) #15
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_5, ptr align 8 %_6, i64 24, i1 false)
; invoke alloc::boxed::box_new_uninit
  %_3.i = invoke ptr @_RNvNtCsdHhxNI3WGqv_5alloc5boxed14box_new_uninitCskjFhZNFXKrT_13simple_vtable(i64 8, i64 24)
          to label %_RNvMNtCsdHhxNI3WGqv_5alloc5boxedINtB2_3BoxNtCskjFhZNFXKrT_13simple_vtable6StructE3newBG_.exit unwind label %cleanup.i

cleanup.i:                                        ; preds = %bb1
  %12 = landingpad { ptr, i32 }
          cleanup
  %13 = extractvalue { ptr, i32 } %12, 0
  %14 = extractvalue { ptr, i32 } %12, 1
  store ptr %13, ptr %1, align 8
  %15 = getelementptr inbounds i8, ptr %1, i64 8
  store i32 %14, ptr %15, align 8
; invoke core::ptr::drop_in_place::<simple_vtable::Struct>
  invoke void @_RINvNtCsl1Y3iNB2xjl_4core3ptr13drop_in_placeNtCskjFhZNFXKrT_13simple_vtable6StructEBI_(ptr align 8 %_5) #16
          to label %bb2.i unwind label %terminate.i

terminate.i:                                      ; preds = %cleanup.i
  %16 = landingpad { ptr, i32 }
          filter [0 x ptr] zeroinitializer
; call core::panicking::panic_in_cleanup
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking16panic_in_cleanup() #17
  unreachable

bb2.i:                                            ; preds = %cleanup.i
  %17 = load ptr, ptr %1, align 8
  %18 = getelementptr inbounds i8, ptr %1, i64 8
  %19 = load i32, ptr %18, align 8
  %20 = insertvalue { ptr, i32 } poison, ptr %17, 0
  %21 = insertvalue { ptr, i32 } %20, i32 %19, 1
  resume { ptr, i32 } %21

_RNvMNtCsdHhxNI3WGqv_5alloc5boxedINtB2_3BoxNtCskjFhZNFXKrT_13simple_vtable6StructE3newBG_.exit: ; preds = %bb1
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_3.i, ptr align 8 %_5, i64 24, i1 false)
  store ptr %_3.i, ptr %_2, align 8
  %22 = getelementptr inbounds i8, ptr %_2, i64 8
  store ptr @vtable.1, ptr %22, align 8
  br label %bb6

bb6:                                              ; preds = %_RNvMNtCsdHhxNI3WGqv_5alloc5boxedINtB2_3BoxNtCskjFhZNFXKrT_13simple_vtable6StructE3newBG_.exit, %_RNvMNtCsdHhxNI3WGqv_5alloc5boxedINtB2_3BoxNtCskjFhZNFXKrT_13simple_vtable7Struct2E3newBG_.exit
  %_0.0 = load ptr, ptr %_2, align 8
  %23 = getelementptr inbounds i8, ptr %_2, i64 8
  %_0.1 = load ptr, ptr %23, align 8
  %24 = insertvalue { ptr, ptr } poison, ptr %_0.0, 0
  %25 = insertvalue { ptr, ptr } %24, ptr %_0.1, 1
  ret { ptr, ptr } %25
}

; <alloc::alloc::Global>::alloc_impl_runtime
; Function Attrs: inlinehint nonlazybind uwtable
define internal { ptr, i64 } @_RNvMNtCsdHhxNI3WGqv_5alloc5allocNtB2_6Global18alloc_impl_runtimeCskjFhZNFXKrT_13simple_vtable(i64 %layout.0, i64 %layout.1, i1 zeroext %zeroed) unnamed_addr #0 {
start:
  %self1 = alloca [8 x i8], align 8
  %self = alloca [8 x i8], align 8
  %_9 = alloca [8 x i8], align 8
  %raw_ptr = alloca [8 x i8], align 8
  %_0 = alloca [16 x i8], align 8
  %0 = icmp eq i64 %layout.1, 0
  br i1 %0, label %bb2, label %bb1

bb2:                                              ; preds = %start
  %data = inttoptr i64 %layout.0 to ptr
  %data2 = inttoptr i64 %layout.0 to ptr
  br label %bb7

bb1:                                              ; preds = %start
  br i1 %zeroed, label %bb3, label %bb4

bb7:                                              ; preds = %bb2
  %_19 = inttoptr i64 %layout.0 to ptr
; call <core::ptr::non_null::NonNull<_>>::new_unchecked::precondition_check
  call void @_RNvNvMs1_NtNtCsl1Y3iNB2xjl_4core3ptr8non_nullINtB7_7NonNullpE13new_unchecked18precondition_checkCskjFhZNFXKrT_13simple_vtable(ptr %_19, ptr align 8 @alloc_4693b25d3eabde0252d3a3cfc0a04ff1) #18
  br label %bb9

bb9:                                              ; preds = %bb7
  store ptr %data2, ptr %_0, align 8
  %1 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 0, ptr %1, align 8
  br label %bb6

bb6:                                              ; preds = %bb21, %bb14, %bb9
  %2 = load ptr, ptr %_0, align 8
  %3 = getelementptr inbounds i8, ptr %_0, i64 8
  %4 = load i64, ptr %3, align 8
  %5 = insertvalue { ptr, i64 } poison, ptr %2, 0
  %6 = insertvalue { ptr, i64 } %5, i64 %4, 1
  ret { ptr, i64 } %6

bb4:                                              ; preds = %bb1
; call __rustc::__rust_no_alloc_shim_is_unstable_v2
  call void @_RNvCs2fcwfXhWpkc_7___rustc35___rust_no_alloc_shim_is_unstable_v2() #19
; call __rustc::__rust_alloc
  %7 = call ptr @_RNvCs2fcwfXhWpkc_7___rustc12___rust_alloc(i64 %layout.1, i64 %layout.0) #19
  store ptr %7, ptr %raw_ptr, align 8
  br label %bb5

bb3:                                              ; preds = %bb1
; call __rustc::__rust_no_alloc_shim_is_unstable_v2
  call void @_RNvCs2fcwfXhWpkc_7___rustc35___rust_no_alloc_shim_is_unstable_v2() #19
; call __rustc::__rust_alloc_zeroed
  %8 = call ptr @_RNvCs2fcwfXhWpkc_7___rustc19___rust_alloc_zeroed(i64 %layout.1, i64 %layout.0) #19
  store ptr %8, ptr %raw_ptr, align 8
  br label %bb5

bb5:                                              ; preds = %bb3, %bb4
  %9 = load ptr, ptr %raw_ptr, align 8
  %_29 = ptrtoint ptr %9 to i64
  %10 = icmp eq i64 %_29, 0
  br i1 %10, label %bb14, label %bb15

bb14:                                             ; preds = %bb5
  store ptr null, ptr %self1, align 8
  store ptr null, ptr %self, align 8
  %11 = load ptr, ptr @anon.42aad29631b5bed5b04828ecca743db5.0, align 8
  %12 = load i64, ptr getelementptr inbounds (i8, ptr @anon.42aad29631b5bed5b04828ecca743db5.0, i64 8), align 8
  store ptr %11, ptr %_0, align 8
  %13 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %12, ptr %13, align 8
  br label %bb6

bb15:                                             ; preds = %bb5
  br label %bb16

bb16:                                             ; preds = %bb15
  %_31 = load ptr, ptr %raw_ptr, align 8
; call <core::ptr::non_null::NonNull<_>>::new_unchecked::precondition_check
  call void @_RNvNvMs1_NtNtCsl1Y3iNB2xjl_4core3ptr8non_nullINtB7_7NonNullpE13new_unchecked18precondition_checkCskjFhZNFXKrT_13simple_vtable(ptr %_31, ptr align 8 @alloc_5ba1495433bc7bd4d57e2fc7e46f3ce7) #18
  br label %bb18

bb18:                                             ; preds = %bb16
  %_28 = load ptr, ptr %raw_ptr, align 8
  store ptr %_28, ptr %self1, align 8
  %v = load ptr, ptr %self1, align 8
  store ptr %v, ptr %self, align 8
  %v3 = load ptr, ptr %self, align 8
  store ptr %v3, ptr %_9, align 8
  %ptr = load ptr, ptr %_9, align 8
  br label %bb19

bb19:                                             ; preds = %bb18
; call <core::ptr::non_null::NonNull<_>>::new_unchecked::precondition_check
  call void @_RNvNvMs1_NtNtCsl1Y3iNB2xjl_4core3ptr8non_nullINtB7_7NonNullpE13new_unchecked18precondition_checkCskjFhZNFXKrT_13simple_vtable(ptr %ptr, ptr align 8 @alloc_4693b25d3eabde0252d3a3cfc0a04ff1) #18
  br label %bb21

bb21:                                             ; preds = %bb19
  store ptr %ptr, ptr %_0, align 8
  %14 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %layout.1, ptr %14, align 8
  br label %bb6
}

; <*const ()>::is_aligned_to
; Function Attrs: inlinehint nonlazybind uwtable
define zeroext i1 @_RNvMNtNtCsl1Y3iNB2xjl_4core3ptr9const_ptrPu13is_aligned_toCskjFhZNFXKrT_13simple_vtable(ptr %self, i64 %align) unnamed_addr #0 {
start:
  %0 = alloca [4 x i8], align 4
  %1 = call i64 @llvm.ctpop.i64(i64 %align)
  %2 = trunc i64 %1 to i32
  store i32 %2, ptr %0, align 4
  %_9 = load i32, ptr %0, align 4
  %3 = icmp eq i32 %_9, 1
  br i1 %3, label %bb1, label %bb2

bb1:                                              ; preds = %start
  %_6 = ptrtoint ptr %self to i64
  %_8.0 = sub i64 %align, 1
  %_8.1 = icmp ult i64 %align, 1
  br i1 %_8.1, label %panic, label %bb3

bb2:                                              ; preds = %start
; call core::panicking::panic_fmt
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking9panic_fmt(ptr @alloc_fad0cd83b7d1858a846a172eb260e593, ptr inttoptr (i64 85 to ptr), ptr align 8 @alloc_fc9ab3224673f8be7b78582aac5df6a6) #20
  unreachable

bb3:                                              ; preds = %bb1
  %_5 = and i64 %_6, %_8.0
  %_0 = icmp eq i64 %_5, 0
  ret i1 %_0

panic:                                            ; preds = %bb1
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_RNvNtNtCsl1Y3iNB2xjl_4core9panicking11panic_const24panic_const_sub_overflow(ptr align 8 @alloc_97ea21a74f677b9ef8611233fc5bfdff) #20
  unreachable
}

; <alloc::raw_vec::RawVecInner>::with_capacity_in
; Function Attrs: inlinehint nonlazybind uwtable
define { i64, ptr } @_RNvMs4_NtCsdHhxNI3WGqv_5alloc7raw_vecNtB5_11RawVecInner16with_capacity_inCskjFhZNFXKrT_13simple_vtable(i64 %capacity, i64 %elem_layout.0, i64 %elem_layout.1) unnamed_addr #0 {
start:
  %self = alloca [8 x i8], align 8
  %_4 = alloca [24 x i8], align 8
; call <alloc::raw_vec::RawVecInner>::try_allocate_in
  call void @_RNvMs4_NtCsdHhxNI3WGqv_5alloc7raw_vecNtB5_11RawVecInner15try_allocate_inCs7XHCnmxDBD7_5gimli(ptr sret([24 x i8]) align 8 %_4, i64 %capacity, i1 zeroext false, i64 %elem_layout.0, i64 %elem_layout.1)
  %_5 = load i64, ptr %_4, align 8
  %0 = trunc nuw i64 %_5 to i1
  br i1 %0, label %bb3, label %bb4

bb3:                                              ; preds = %start
  %1 = getelementptr inbounds i8, ptr %_4, i64 8
  %err.0 = load i64, ptr %1, align 8
  %2 = getelementptr inbounds i8, ptr %1, i64 8
  %err.1 = load i64, ptr %2, align 8
; call alloc::raw_vec::handle_error
  call void @_RNvNtCsdHhxNI3WGqv_5alloc7raw_vec12handle_error(i64 %err.0, i64 %err.1) #21
  unreachable

bb4:                                              ; preds = %start
  %3 = getelementptr inbounds i8, ptr %_4, i64 8
  %this.0 = load i64, ptr %3, align 8
  %4 = getelementptr inbounds i8, ptr %3, i64 8
  %this.1 = load ptr, ptr %4, align 8
  %5 = icmp eq i64 %elem_layout.1, 0
  br i1 %5, label %bb6, label %bb7

bb6:                                              ; preds = %bb4
  store i64 -1, ptr %self, align 8
  br label %bb5

bb7:                                              ; preds = %bb4
  store i64 %this.0, ptr %self, align 8
  br label %bb5

bb5:                                              ; preds = %bb7, %bb6
  %6 = load i64, ptr %self, align 8
  %_11 = sub i64 %6, 0
  %_7 = icmp ugt i64 %capacity, %_11
  %cond = xor i1 %_7, true
  br label %bb8

bb8:                                              ; preds = %bb5
; call core::hint::assert_unchecked::precondition_check
  call void @_RNvNvNtCsl1Y3iNB2xjl_4core4hint16assert_unchecked18precondition_checkCskjFhZNFXKrT_13simple_vtable(i1 zeroext %cond, ptr align 8 @alloc_ce9f95331637087388e965745b6757b6) #18
  br label %bb9

bb9:                                              ; preds = %bb8
  %7 = insertvalue { i64, ptr } poison, i64 %this.0, 0
  %8 = insertvalue { i64, ptr } %7, ptr %this.1, 1
  ret { i64, ptr } %8

bb2:                                              ; No predecessors!
  unreachable
}

; alloc::boxed::box_new_uninit
; Function Attrs: inlinehint nonlazybind uwtable
define internal ptr @_RNvNtCsdHhxNI3WGqv_5alloc5boxed14box_new_uninitCskjFhZNFXKrT_13simple_vtable(i64 %layout.0, i64 %layout.1) unnamed_addr #0 {
start:
  %_2 = alloca [16 x i8], align 8
; call <alloc::alloc::Global>::alloc_impl_runtime
  %0 = call { ptr, i64 } @_RNvMNtCsdHhxNI3WGqv_5alloc5allocNtB2_6Global18alloc_impl_runtimeCskjFhZNFXKrT_13simple_vtable(i64 %layout.0, i64 %layout.1, i1 zeroext false) #15
  %1 = extractvalue { ptr, i64 } %0, 0
  %2 = extractvalue { ptr, i64 } %0, 1
  store ptr %1, ptr %_2, align 8
  %3 = getelementptr inbounds i8, ptr %_2, i64 8
  store i64 %2, ptr %3, align 8
  %4 = load ptr, ptr %_2, align 8
  %5 = getelementptr inbounds i8, ptr %_2, i64 8
  %6 = load i64, ptr %5, align 8
  %7 = ptrtoint ptr %4 to i64
  %8 = icmp eq i64 %7, 0
  %_3 = select i1 %8, i64 1, i64 0
  %9 = trunc nuw i64 %_3 to i1
  br i1 %9, label %bb2, label %bb3

bb2:                                              ; preds = %start
; call alloc::alloc::handle_alloc_error
  call void @_RNvNtCsdHhxNI3WGqv_5alloc5alloc18handle_alloc_error(i64 %layout.0, i64 %layout.1) #21
  unreachable

bb3:                                              ; preds = %start
  %ptr.0 = load ptr, ptr %_2, align 8
  %10 = getelementptr inbounds i8, ptr %_2, i64 8
  %ptr.1 = load i64, ptr %10, align 8
  ret ptr %ptr.0

bb1:                                              ; No predecessors!
  unreachable
}

; core::intrinsics::cold_path
; Function Attrs: cold nounwind nonlazybind uwtable
define internal void @_RNvNtCsl1Y3iNB2xjl_4core10intrinsics9cold_pathCskjFhZNFXKrT_13simple_vtable() unnamed_addr #2 {
start:
  ret void
}

; <core::ptr::alignment::Alignment>::new_unchecked::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind uwtable
define internal void @_RNvNvMNtNtCsl1Y3iNB2xjl_4core3ptr9alignmentNtB4_9Alignment13new_unchecked18precondition_checkCskjFhZNFXKrT_13simple_vtable(i64 %align, ptr align 8 %0) unnamed_addr #3 {
start:
  %1 = alloca [4 x i8], align 4
  %2 = call i64 @llvm.ctpop.i64(i64 %align)
  %3 = trunc i64 %2 to i32
  store i32 %3, ptr %1, align 4
  %_5 = load i32, ptr %1, align 4
  %4 = icmp eq i32 %_5, 1
  br i1 %4, label %bb1, label %bb2

bb1:                                              ; preds = %start
  ret void

bb2:                                              ; preds = %start
; call core::panicking::panic_nounwind_fmt
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking18panic_nounwind_fmt(ptr @alloc_0625062a5eee489a7813ee965a38d15a, ptr inttoptr (i64 397 to ptr), i1 zeroext false, ptr align 8 %0) #22
  unreachable
}

; <core::alloc::layout::Layout>::from_size_alignment_unchecked::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind uwtable
define internal void @_RNvNvMNtNtCsl1Y3iNB2xjl_4core5alloc6layoutNtB4_6Layout29from_size_alignment_unchecked18precondition_checkCskjFhZNFXKrT_13simple_vtable(i64 %size, i64 %alignment, ptr align 8 %0) unnamed_addr #3 {
start:
  %_7 = sub nuw i64 -9223372036854775808, %alignment
  %_3 = icmp ule i64 %size, %_7
  br i1 %_3, label %bb1, label %bb2

bb2:                                              ; preds = %start
; call core::panicking::panic_nounwind_fmt
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking18panic_nounwind_fmt(ptr @alloc_8cf3531fd3c828ab298b686071a40c17, ptr inttoptr (i64 519 to ptr), i1 zeroext false, ptr align 8 %0) #22
  unreachable

bb1:                                              ; preds = %start
  ret void
}

; <core::ptr::non_null::NonNull<_>>::new_unchecked::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind uwtable
define internal void @_RNvNvMs1_NtNtCsl1Y3iNB2xjl_4core3ptr8non_nullINtB7_7NonNullpE13new_unchecked18precondition_checkCskjFhZNFXKrT_13simple_vtable(ptr %ptr, ptr align 8 %0) unnamed_addr #3 {
start:
  %_5 = ptrtoint ptr %ptr to i64
  %1 = icmp eq i64 %_5, 0
  br i1 %1, label %bb1, label %bb2

bb1:                                              ; preds = %start
; call core::panicking::panic_nounwind_fmt
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking18panic_nounwind_fmt(ptr @alloc_560a59ed819b9d9a5841f6e731c4c8e5, ptr inttoptr (i64 421 to ptr), i1 zeroext false, ptr align 8 %0) #22
  unreachable

bb2:                                              ; preds = %start
  ret void
}

; <alloc::vec::Vec<_, _>>::set_len::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind uwtable
define internal void @_RNvNvMs_NtCsdHhxNI3WGqv_5alloc3vecINtB6_3VecppE7set_len18precondition_checkCskjFhZNFXKrT_13simple_vtable(i64 %new_len, i64 %capacity, ptr align 8 %0) unnamed_addr #3 {
start:
  %_3 = icmp ule i64 %new_len, %capacity
  br i1 %_3, label %bb1, label %bb2

bb2:                                              ; preds = %start
; call core::panicking::panic_nounwind_fmt
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking18panic_nounwind_fmt(ptr @alloc_57d70e9d94c65ecfc15225d29a5ed72b, ptr inttoptr (i64 397 to ptr), i1 zeroext false, ptr align 8 %0) #22
  unreachable

bb1:                                              ; preds = %start
  ret void
}

; core::ptr::copy_nonoverlapping::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind uwtable
define internal void @_RNvNvNtCsl1Y3iNB2xjl_4core3ptr19copy_nonoverlapping18precondition_checkCskjFhZNFXKrT_13simple_vtable(ptr %src, ptr %dst, i64 %size, i64 %align, i64 %count, ptr align 8 %0) unnamed_addr #3 personality ptr @rust_eh_personality {
start:
  %zero_size = alloca [1 x i8], align 1
  %1 = icmp eq i64 %count, 0
  br i1 %1, label %bb1, label %bb2

bb1:                                              ; preds = %start
  store i8 1, ptr %zero_size, align 1
  br label %bb3

bb2:                                              ; preds = %start
  %2 = icmp eq i64 %size, 0
  %3 = zext i1 %2 to i8
  store i8 %3, ptr %zero_size, align 1
  br label %bb3

bb3:                                              ; preds = %bb2, %bb1
  %4 = load i8, ptr %zero_size, align 1
  %is_zst = trunc nuw i8 %4 to i1
; invoke <*const ()>::is_aligned_to
  %_15 = invoke zeroext i1 @_RNvMNtNtCsl1Y3iNB2xjl_4core3ptr9const_ptrPu13is_aligned_toCskjFhZNFXKrT_13simple_vtable(ptr %src, i64 %align)
          to label %bb15 unwind label %terminate

terminate:                                        ; preds = %bb5, %bb4, %bb3
  %5 = landingpad { ptr, i32 }
          filter [0 x ptr] zeroinitializer
; call core::panicking::panic_cannot_unwind
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking19panic_cannot_unwind() #17
  unreachable

bb15:                                             ; preds = %bb3
  br i1 %_15, label %bb11, label %bb12

bb12:                                             ; preds = %bb15
  br label %bb7

bb11:                                             ; preds = %bb15
  br i1 %is_zst, label %bb13, label %bb14

bb7:                                              ; preds = %bb14, %bb12
  br label %bb8

bb14:                                             ; preds = %bb11
  %_17 = ptrtoint ptr %src to i64
  %_16 = icmp eq i64 %_17, 0
  %_8 = xor i1 %_16, true
  br i1 %_8, label %bb4, label %bb7

bb13:                                             ; preds = %bb11
  br label %bb4

bb4:                                              ; preds = %bb13, %bb14
; invoke <*const ()>::is_aligned_to
  %_18 = invoke zeroext i1 @_RNvMNtNtCsl1Y3iNB2xjl_4core3ptr9const_ptrPu13is_aligned_toCskjFhZNFXKrT_13simple_vtable(ptr %dst, i64 %align)
          to label %bb20 unwind label %terminate

bb8:                                              ; preds = %bb6, %bb7
  br label %bb9

bb20:                                             ; preds = %bb4
  br i1 %_18, label %bb16, label %bb17

bb17:                                             ; preds = %bb20
  br label %bb6

bb16:                                             ; preds = %bb20
  %6 = load i8, ptr %zero_size, align 1
  %7 = trunc nuw i8 %6 to i1
  br i1 %7, label %bb18, label %bb19

bb6:                                              ; preds = %bb19, %bb17
  br label %bb8

bb19:                                             ; preds = %bb16
  %_20 = ptrtoint ptr %dst to i64
  %_19 = icmp eq i64 %_20, 0
  %_10 = xor i1 %_19, true
  br i1 %_10, label %bb5, label %bb6

bb18:                                             ; preds = %bb16
  br label %bb5

bb5:                                              ; preds = %bb18, %bb19
; invoke core::ub_checks::maybe_is_nonoverlapping::runtime
  %_6 = invoke zeroext i1 @_RNvNvNtCsl1Y3iNB2xjl_4core9ub_checks23maybe_is_nonoverlapping7runtimeCskjFhZNFXKrT_13simple_vtable(ptr %src, ptr %dst, i64 %size, i64 %count)
          to label %bb21 unwind label %terminate

bb9:                                              ; preds = %bb21, %bb8
; call core::panicking::panic_nounwind_fmt
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking18panic_nounwind_fmt(ptr @alloc_bd3468a7b96187f70c1ce98a3e7a63bf, ptr inttoptr (i64 567 to ptr), i1 zeroext false, ptr align 8 %0) #22
  unreachable

bb21:                                             ; preds = %bb5
  br i1 %_6, label %bb10, label %bb9

bb10:                                             ; preds = %bb21
  ret void
}

; core::hint::assert_unchecked::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind uwtable
define internal void @_RNvNvNtCsl1Y3iNB2xjl_4core4hint16assert_unchecked18precondition_checkCskjFhZNFXKrT_13simple_vtable(i1 zeroext %cond, ptr align 8 %0) unnamed_addr #3 {
start:
  br i1 %cond, label %bb2, label %bb1

bb1:                                              ; preds = %start
; call core::panicking::panic_nounwind_fmt
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking18panic_nounwind_fmt(ptr @alloc_64e308ef4babfeb8b6220184de794a17, ptr inttoptr (i64 443 to ptr), i1 zeroext false, ptr align 8 %0) #22
  unreachable

bb2:                                              ; preds = %start
  ret void
}

; core::ub_checks::maybe_is_nonoverlapping::runtime
; Function Attrs: inlinehint nonlazybind uwtable
define internal zeroext i1 @_RNvNvNtCsl1Y3iNB2xjl_4core9ub_checks23maybe_is_nonoverlapping7runtimeCskjFhZNFXKrT_13simple_vtable(ptr %src, ptr %dst, i64 %size, i64 %count) unnamed_addr #0 {
start:
  %diff = alloca [8 x i8], align 8
  %_9 = alloca [16 x i8], align 8
  %src_usize = ptrtoint ptr %src to i64
  %dst_usize = ptrtoint ptr %dst to i64
  %0 = call { i64, i1 } @llvm.umul.with.overflow.i64(i64 %size, i64 %count)
  %_13.0 = extractvalue { i64, i1 } %0, 0
  %_13.1 = extractvalue { i64, i1 } %0, 1
  br i1 %_13.1, label %bb1, label %bb3

bb3:                                              ; preds = %start
  %1 = getelementptr inbounds i8, ptr %_9, i64 8
  store i64 %_13.0, ptr %1, align 8
  store i64 1, ptr %_9, align 8
  %2 = getelementptr inbounds i8, ptr %_9, i64 8
  %size1 = load i64, ptr %2, align 8
  %_21 = icmp ult i64 %src_usize, %dst_usize
  br i1 %_21, label %bb4, label %bb6

bb1:                                              ; preds = %start
; call core::panicking::panic_nounwind
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking14panic_nounwind(ptr align 1 @alloc_763310d78c99c2c1ad3f8a9821e942f3, i64 61) #22
  unreachable

bb6:                                              ; preds = %bb3
  %_23.0 = sub i64 %src_usize, %dst_usize
  %_23.1 = icmp ult i64 %src_usize, %dst_usize
  br i1 %_23.1, label %panic, label %bb7

bb4:                                              ; preds = %bb3
  %_22.0 = sub i64 %dst_usize, %src_usize
  %_22.1 = icmp ult i64 %dst_usize, %src_usize
  br i1 %_22.1, label %panic2, label %bb5

bb7:                                              ; preds = %bb6
  store i64 %_23.0, ptr %diff, align 8
  br label %bb8

panic:                                            ; preds = %bb6
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_RNvNtNtCsl1Y3iNB2xjl_4core9panicking11panic_const24panic_const_sub_overflow(ptr align 8 @alloc_86b951561bf1022fc084636771000468) #20
  unreachable

bb8:                                              ; preds = %bb5, %bb7
  %3 = load i64, ptr %diff, align 8
  %_0 = icmp uge i64 %3, %size1
  ret i1 %_0

bb5:                                              ; preds = %bb4
  store i64 %_22.0, ptr %diff, align 8
  br label %bb8

panic2:                                           ; preds = %bb4
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_RNvNtNtCsl1Y3iNB2xjl_4core9panicking11panic_const24panic_const_sub_overflow(ptr align 8 @alloc_86b951561bf1022fc084636771000468) #20
  unreachable
}

; <simple_vtable::Struct as simple_vtable::MyTrait>::bar
; Function Attrs: nonlazybind uwtable
define i32 @_RNvXCskjFhZNFXKrT_13simple_vtableNtB2_6StructNtB2_7MyTrait3bar(ptr align 8 %self) unnamed_addr #1 {
start:
  ret i32 42
}

; <simple_vtable::Struct as simple_vtable::MyTrait>::foo
; Function Attrs: nonlazybind uwtable
define void @_RNvXCskjFhZNFXKrT_13simple_vtableNtB2_6StructNtB2_7MyTrait3foo(ptr align 8 %self) unnamed_addr #1 {
start:
  %_7 = alloca [16 x i8], align 8
  %args = alloca [16 x i8], align 8
; call <core::fmt::rt::Argument>::new_display::<alloc::string::String>
  call void @_RINvMNtNtCsl1Y3iNB2xjl_4core3fmt2rtNtB3_8Argument11new_displayNtNtCsdHhxNI3WGqv_5alloc6string6StringECskjFhZNFXKrT_13simple_vtable(ptr sret([16 x i8]) align 8 %_7, ptr align 8 %self) #15
  %0 = getelementptr inbounds nuw %"core::fmt::rt::Argument<'_>", ptr %args, i64 0
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %0, ptr align 8 %_7, i64 16, i1 false)
; call <core::fmt::Arguments>::new::<16, 1>
  %1 = call { ptr, ptr } @_RINvMs2_NtCsl1Y3iNB2xjl_4core3fmtNtB6_9Arguments3newKj10_Kj1_ECskjFhZNFXKrT_13simple_vtable(ptr align 1 @alloc_724bfa08d8112cb0bda01416cbde3db0, ptr align 8 %args) #15
  %_3.0 = extractvalue { ptr, ptr } %1, 0
  %_3.1 = extractvalue { ptr, ptr } %1, 1
; call std::io::stdio::_print
  call void @_RNvNtNtCscuvkGynyuSZ_3std2io5stdio6__print(ptr %_3.0, ptr %_3.1)
  ret void
}

; <str as alloc::string::SpecToString>::spec_to_string
; Function Attrs: inlinehint nonlazybind uwtable
define internal void @_RNvXs21_NtCsdHhxNI3WGqv_5alloc6stringeNtB6_12SpecToString14spec_to_stringCskjFhZNFXKrT_13simple_vtable(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %self.0, i64 %self.1) unnamed_addr #0 {
start:
  %bytes = alloca [24 x i8], align 8
; call <u8 as <[_]>::to_vec_in::ConvertVec>::to_vec::<alloc::alloc::Global>
  call void @_RINvXs_NvMNtCsdHhxNI3WGqv_5alloc5sliceSp9to_vec_inhNtB5_10ConvertVec6to_vecNtNtBa_5alloc6GlobalECskjFhZNFXKrT_13simple_vtable(ptr sret([24 x i8]) align 8 %bytes, ptr align 1 %self.0, i64 %self.1) #15
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %bytes, i64 24, i1 false)
  ret void
}

; <alloc::boxed::Box<dyn simple_vtable::MyTrait> as core::ops::drop::Drop>::drop
; Function Attrs: inlinehint nonlazybind uwtable
define void @_RNvXs8_NtCsdHhxNI3WGqv_5alloc5boxedINtB5_3BoxDNtCskjFhZNFXKrT_13simple_vtable7MyTraitEL_ENtNtNtCsl1Y3iNB2xjl_4core3ops4drop4Drop4dropBK_(ptr align 8 %self) unnamed_addr #0 {
start:
  %0 = alloca [8 x i8], align 8
  %1 = alloca [8 x i8], align 8
  %ptr.0 = load ptr, ptr %self, align 8
  %2 = getelementptr inbounds i8, ptr %self, i64 8
  %ptr.1 = load ptr, ptr %2, align 8
  %3 = getelementptr inbounds i8, ptr %ptr.1, i64 4
  %4 = load i32, ptr %3, align 4, !invariant.load !3
  %5 = zext i32 %4 to i64
  %6 = getelementptr inbounds i8, ptr %ptr.1, i64 8
  %7 = load i32, ptr %6, align 4, !invariant.load !3
  %8 = zext i32 %7 to i64
  store i64 %5, ptr %1, align 8
  %size = load i64, ptr %1, align 8
  %9 = getelementptr inbounds i8, ptr %ptr.1, i64 4
  %10 = load i32, ptr %9, align 4, !invariant.load !3
  %11 = zext i32 %10 to i64
  %12 = getelementptr inbounds i8, ptr %ptr.1, i64 8
  %13 = load i32, ptr %12, align 4, !invariant.load !3
  %14 = zext i32 %13 to i64
  store i64 %14, ptr %0, align 8
  %align = load i64, ptr %0, align 8
  br label %bb6

bb6:                                              ; preds = %start
; call <core::ptr::alignment::Alignment>::new_unchecked::precondition_check
  call void @_RNvNvMNtNtCsl1Y3iNB2xjl_4core3ptr9alignmentNtB4_9Alignment13new_unchecked18precondition_checkCskjFhZNFXKrT_13simple_vtable(i64 %align, ptr align 8 @alloc_1dd1f17b7d26b1300b870840ad476677) #18
  br label %bb7

bb7:                                              ; preds = %bb6
  br label %bb8

bb8:                                              ; preds = %bb7
; call <core::alloc::layout::Layout>::from_size_alignment_unchecked::precondition_check
  call void @_RNvNvMNtNtCsl1Y3iNB2xjl_4core5alloc6layoutNtB4_6Layout29from_size_alignment_unchecked18precondition_checkCskjFhZNFXKrT_13simple_vtable(i64 %size, i64 %align, ptr align 8 @alloc_500d4670593dfc9f2e6da26af3f15b8b) #18
  br label %bb9

bb9:                                              ; preds = %bb8
  %15 = icmp eq i64 %size, 0
  br i1 %15, label %bb3, label %bb1

bb3:                                              ; preds = %bb1, %bb9
  ret void

bb1:                                              ; preds = %bb9
  %_7 = getelementptr inbounds i8, ptr %self, i64 16
; call <alloc::alloc::Global as core::alloc::Allocator>::deallocate
  call void @_RNvXs_NtCsdHhxNI3WGqv_5alloc5allocNtB4_6GlobalNtNtCsl1Y3iNB2xjl_4core5alloc9Allocator10deallocateCskjFhZNFXKrT_13simple_vtable(ptr align 1 %_7, ptr %ptr.0, i64 %align, i64 %size) #15
  br label %bb3
}

; <str as alloc::string::ToString>::to_string
; Function Attrs: inlinehint nonlazybind uwtable
define void @_RNvXsB_NtCsdHhxNI3WGqv_5alloc6stringeNtB5_8ToString9to_stringCskjFhZNFXKrT_13simple_vtable(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %self.0, i64 %self.1) unnamed_addr #0 {
start:
; call <str as alloc::string::SpecToString>::spec_to_string
  call void @_RNvXs21_NtCsdHhxNI3WGqv_5alloc6stringeNtB6_12SpecToString14spec_to_stringCskjFhZNFXKrT_13simple_vtable(ptr sret([24 x i8]) align 8 %_0, ptr align 1 %self.0, i64 %self.1) #15
  ret void
}

; <simple_vtable::Struct2 as simple_vtable::MyTrait>::bar
; Function Attrs: nonlazybind uwtable
define i32 @_RNvXs_CskjFhZNFXKrT_13simple_vtableNtB4_7Struct2NtB4_7MyTrait3bar(ptr align 4 %self) unnamed_addr #1 {
start:
  %_0 = load i32, ptr %self, align 4
  ret i32 %_0
}

; <simple_vtable::Struct2 as simple_vtable::MyTrait>::foo
; Function Attrs: nonlazybind uwtable
define void @_RNvXs_CskjFhZNFXKrT_13simple_vtableNtB4_7Struct2NtB4_7MyTrait3foo(ptr align 4 %self) unnamed_addr #1 {
start:
  %_8 = alloca [16 x i8], align 8
  %args = alloca [16 x i8], align 8
  %_6 = alloca [4 x i8], align 4
; call <simple_vtable::Struct2 as simple_vtable::MyTrait>::bar
  %0 = call i32 @_RNvXs_CskjFhZNFXKrT_13simple_vtableNtB4_7Struct2NtB4_7MyTrait3bar(ptr align 4 %self)
  store i32 %0, ptr %_6, align 4
; call <core::fmt::rt::Argument>::new_display::<u32>
  call void @_RINvMNtNtCsl1Y3iNB2xjl_4core3fmt2rtNtB3_8Argument11new_displaymECskjFhZNFXKrT_13simple_vtable(ptr sret([16 x i8]) align 8 %_8, ptr align 4 %_6) #15
  %1 = getelementptr inbounds nuw %"core::fmt::rt::Argument<'_>", ptr %args, i64 0
  call void @llvm.memcpy.p0.p0.i64(ptr align 8 %1, ptr align 8 %_8, i64 16, i1 false)
; call <core::fmt::Arguments>::new::<17, 1>
  %2 = call { ptr, ptr } @_RINvMs2_NtCsl1Y3iNB2xjl_4core3fmtNtB6_9Arguments3newKj11_Kj1_ECskjFhZNFXKrT_13simple_vtable(ptr align 1 @alloc_d23184c8762add5bca60e3eefedad428, ptr align 8 %args) #15
  %_3.0 = extractvalue { ptr, ptr } %2, 0
  %_3.1 = extractvalue { ptr, ptr } %2, 1
; call std::io::stdio::_print
  call void @_RNvNtNtCscuvkGynyuSZ_3std2io5stdio6__print(ptr %_3.0, ptr %_3.1)
  ret void
}

; <alloc::alloc::Global as core::alloc::Allocator>::deallocate
; Function Attrs: inlinehint nonlazybind uwtable
define internal void @_RNvXs_NtCsdHhxNI3WGqv_5alloc5allocNtB4_6GlobalNtNtCsl1Y3iNB2xjl_4core5alloc9Allocator10deallocateCskjFhZNFXKrT_13simple_vtable(ptr align 1 %self, ptr %ptr, i64 %layout.0, i64 %layout.1) unnamed_addr #0 {
start:
  %0 = icmp eq i64 %layout.1, 0
  br i1 %0, label %bb2, label %bb1

bb2:                                              ; preds = %bb1, %start
  ret void

bb1:                                              ; preds = %start
; call __rustc::__rust_dealloc
  call void @_RNvCs2fcwfXhWpkc_7___rustc14___rust_dealloc(ptr %ptr, i64 %layout.1, i64 %layout.0) #19
  br label %bb2
}

; <alloc::string::String as core::fmt::Display>::fmt
; Function Attrs: inlinehint nonlazybind uwtable
define internal zeroext i1 @_RNvXsq_NtCsdHhxNI3WGqv_5alloc6stringNtB5_6StringNtNtCsl1Y3iNB2xjl_4core3fmt7Display3fmtCskjFhZNFXKrT_13simple_vtable(ptr align 8 %self, ptr align 8 %f) unnamed_addr #0 {
start:
  %0 = getelementptr inbounds i8, ptr %self, i64 8
  %_8 = load ptr, ptr %0, align 8
  %1 = getelementptr inbounds i8, ptr %self, i64 16
  %_7 = load i64, ptr %1, align 8
; call <str as core::fmt::Display>::fmt
  %_0 = call zeroext i1 @_RNvXsi_NtCsl1Y3iNB2xjl_4core3fmteNtB5_7Display3fmt(ptr align 1 %_8, i64 %_7, ptr align 8 %f)
  ret i1 %_0
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #4

; <u32 as core::fmt::Display>::fmt
; Function Attrs: nonlazybind uwtable
declare zeroext i1 @_RNvXs8_NtNtNtCsl1Y3iNB2xjl_4core3fmt3num3impmNtB9_7Display3fmt(ptr align 4, ptr align 8) unnamed_addr #1

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: read)
declare ptr @llvm.load.relative.i32(ptr, i32) #5

; Function Attrs: nounwind nonlazybind uwtable
declare i32 @rust_eh_personality(i32, i32, i64, ptr, ptr) unnamed_addr #6

; <alloc::vec::Vec<u8> as core::ops::drop::Drop>::drop
; Function Attrs: nonlazybind uwtable
declare void @_RNvXso_NtCsdHhxNI3WGqv_5alloc3vecINtB5_3VechENtNtNtCsl1Y3iNB2xjl_4core3ops4drop4Drop4dropCs7XHCnmxDBD7_5gimli(ptr align 8) unnamed_addr #1

; core::panicking::panic_in_cleanup
; Function Attrs: cold minsize noinline noreturn nounwind nonlazybind optsize uwtable
declare void @_RNvNtCsl1Y3iNB2xjl_4core9panicking16panic_in_cleanup() unnamed_addr #7

; <alloc::raw_vec::RawVec<u8> as core::ops::drop::Drop>::drop
; Function Attrs: nonlazybind uwtable
declare void @_RNvXs1_NtCsdHhxNI3WGqv_5alloc7raw_vecINtB5_6RawVechENtNtNtCsl1Y3iNB2xjl_4core3ops4drop4Drop4dropCs7XHCnmxDBD7_5gimli(ptr align 8) unnamed_addr #1

; __rustc::__rust_no_alloc_shim_is_unstable_v2
; Function Attrs: nounwind nonlazybind uwtable
declare void @_RNvCs2fcwfXhWpkc_7___rustc35___rust_no_alloc_shim_is_unstable_v2() unnamed_addr #6

; __rustc::__rust_alloc
; Function Attrs: nounwind nonlazybind allockind("alloc,uninitialized,aligned") allocsize(0) uwtable
declare noalias ptr @_RNvCs2fcwfXhWpkc_7___rustc12___rust_alloc(i64, i64 allocalign) unnamed_addr #8

; __rustc::__rust_alloc_zeroed
; Function Attrs: nounwind nonlazybind allockind("alloc,zeroed,aligned") allocsize(0) uwtable
declare noalias ptr @_RNvCs2fcwfXhWpkc_7___rustc19___rust_alloc_zeroed(i64, i64 allocalign) unnamed_addr #9

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.ctpop.i64(i64) #10

; core::panicking::panic_const::panic_const_sub_overflow
; Function Attrs: cold noinline noreturn nonlazybind uwtable
declare void @_RNvNtNtCsl1Y3iNB2xjl_4core9panicking11panic_const24panic_const_sub_overflow(ptr align 8) unnamed_addr #11

; core::panicking::panic_fmt
; Function Attrs: cold noinline noreturn nonlazybind uwtable
declare void @_RNvNtCsl1Y3iNB2xjl_4core9panicking9panic_fmt(ptr, ptr, ptr align 8) unnamed_addr #11

; <alloc::raw_vec::RawVecInner>::try_allocate_in
; Function Attrs: nonlazybind uwtable
declare void @_RNvMs4_NtCsdHhxNI3WGqv_5alloc7raw_vecNtB5_11RawVecInner15try_allocate_inCs7XHCnmxDBD7_5gimli(ptr sret([24 x i8]) align 8, i64, i1 zeroext, i64, i64) unnamed_addr #1

; alloc::raw_vec::handle_error
; Function Attrs: cold minsize noreturn nonlazybind optsize uwtable
declare void @_RNvNtCsdHhxNI3WGqv_5alloc7raw_vec12handle_error(i64, i64) unnamed_addr #12

; alloc::alloc::handle_alloc_error
; Function Attrs: cold minsize noreturn nonlazybind optsize uwtable
declare void @_RNvNtCsdHhxNI3WGqv_5alloc5alloc18handle_alloc_error(i64, i64) unnamed_addr #12

; core::panicking::panic_nounwind_fmt
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtCsl1Y3iNB2xjl_4core9panicking18panic_nounwind_fmt(ptr, ptr, i1 zeroext, ptr align 8) unnamed_addr #13

; core::panicking::panic_cannot_unwind
; Function Attrs: cold minsize noinline noreturn nounwind nonlazybind optsize uwtable
declare void @_RNvNtCsl1Y3iNB2xjl_4core9panicking19panic_cannot_unwind() unnamed_addr #7

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare { i64, i1 } @llvm.umul.with.overflow.i64(i64, i64) #10

; core::panicking::panic_nounwind
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtCsl1Y3iNB2xjl_4core9panicking14panic_nounwind(ptr align 1, i64) unnamed_addr #13

; std::io::stdio::_print
; Function Attrs: nonlazybind uwtable
declare void @_RNvNtNtCscuvkGynyuSZ_3std2io5stdio6__print(ptr, ptr) unnamed_addr #1

; __rustc::__rust_dealloc
; Function Attrs: nounwind nonlazybind allockind("free") uwtable
declare void @_RNvCs2fcwfXhWpkc_7___rustc14___rust_dealloc(ptr allocptr captures(address), i64, i64) unnamed_addr #14

; <str as core::fmt::Display>::fmt
; Function Attrs: nonlazybind uwtable
declare zeroext i1 @_RNvXsi_NtCsl1Y3iNB2xjl_4core3fmteNtB5_7Display3fmt(ptr align 1, i64, ptr align 8) unnamed_addr #1

attributes #0 = { inlinehint nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { cold nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { inlinehint nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #4 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #5 = { nocallback nofree nosync nounwind willreturn memory(argmem: read) }
attributes #6 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #7 = { cold minsize noinline noreturn nounwind nonlazybind optsize uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #8 = { nounwind nonlazybind allockind("alloc,uninitialized,aligned") allocsize(0) uwtable "alloc-family"="__rust_alloc" "alloc-variant-zeroed"="_RNvCs2fcwfXhWpkc_7___rustc19___rust_alloc_zeroed" "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #9 = { nounwind nonlazybind allockind("alloc,zeroed,aligned") allocsize(0) uwtable "alloc-family"="__rust_alloc" "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #10 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }
attributes #11 = { cold noinline noreturn nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #12 = { cold minsize noreturn nonlazybind optsize uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #13 = { cold noinline noreturn nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #14 = { nounwind nonlazybind allockind("free") uwtable "alloc-family"="__rust_alloc" "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #15 = { inlinehint }
attributes #16 = { cold }
attributes #17 = { cold noreturn nounwind }
attributes #18 = { inlinehint nounwind }
attributes #19 = { nounwind }
attributes #20 = { noinline noreturn }
attributes #21 = { noreturn }
attributes #22 = { noinline noreturn nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{!"rustc version 1.95.0-dev"}
!3 = !{}
