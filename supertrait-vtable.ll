; ModuleID = 'supertrait_vtable.b68e0f2d2ecabe1e-cgu.0'
source_filename = "supertrait_vtable.b68e0f2d2ecabe1e-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@vtable.0 = private unnamed_addr constant [8 x i32] [i32 0, i32 0, i32 1, i32 trunc (i64 sub (i64 ptrtoint (ptr dso_local_equivalent @_RNvXCsfFJBsiz42Ac_17supertrait_vtableNtB2_1SNtB2_4Base4base to i64), i64 ptrtoint (ptr @vtable.0 to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr dso_local_equivalent @_RNvXs_CsfFJBsiz42Ac_17supertrait_vtableNtB4_1SNtB4_1A1a to i64), i64 ptrtoint (ptr @vtable.0 to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr dso_local_equivalent @_RNvXs0_CsfFJBsiz42Ac_17supertrait_vtableNtB5_1SNtB5_1B1b to i64), i64 ptrtoint (ptr @vtable.0 to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr @vtable.1 to i64), i64 ptrtoint (ptr @vtable.0 to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr dso_local_equivalent @_RNvXs1_CsfFJBsiz42Ac_17supertrait_vtableNtB5_1SNtB5_7Diamond7diamond to i64), i64 ptrtoint (ptr @vtable.0 to i64)) to i32)], align 4
@vtable.1 = private unnamed_addr constant [5 x i32] [i32 0, i32 0, i32 1, i32 trunc (i64 sub (i64 ptrtoint (ptr dso_local_equivalent @_RNvXCsfFJBsiz42Ac_17supertrait_vtableNtB2_1SNtB2_4Base4base to i64), i64 ptrtoint (ptr @vtable.1 to i64)) to i32), i32 trunc (i64 sub (i64 ptrtoint (ptr dso_local_equivalent @_RNvXs0_CsfFJBsiz42Ac_17supertrait_vtableNtB5_1SNtB5_1B1b to i64), i64 ptrtoint (ptr @vtable.1 to i64)) to i32)], align 4
@alloc_d9b93e2770fc27f14fdfffcf6febca6d = private unnamed_addr constant [33 x i8] c"library/core/src/ptr/non_null.rs\00", align 1
@alloc_4693b25d3eabde0252d3a3cfc0a04ff1 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_d9b93e2770fc27f14fdfffcf6febca6d, [16 x i8] c" \00\00\00\00\00\00\00\AA\05\00\00\12\00\00\00" }>, align 8
@anon.8d095a5e4ec33b3e631eb8fcc21eb960.0 = private unnamed_addr constant <{ [8 x i8], [8 x i8] }> <{ [8 x i8] zeroinitializer, [8 x i8] undef }>, align 8
@alloc_5ba1495433bc7bd4d57e2fc7e46f3ce7 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_d9b93e2770fc27f14fdfffcf6febca6d, [16 x i8] c" \00\00\00\00\00\00\00\10\01\00\00\1B\00\00\00" }>, align 8
@alloc_560a59ed819b9d9a5841f6e731c4c8e5 = private unnamed_addr constant [210 x i8] c"unsafe precondition(s) violated: NonNull::new_unchecked requires that the pointer is non-null\0A\0AThis indicates a bug in the program. This Undefined Behavior check is optional, and cannot be relied on for safety.", align 1

; supertrait_vtable::create_diamond
; Function Attrs: nonlazybind uwtable
define { ptr, ptr } @_RNvCsfFJBsiz42Ac_17supertrait_vtable14create_diamond() unnamed_addr #0 {
start:
; call <alloc::boxed::Box<supertrait_vtable::S>>::new
  %_1 = call align 1 ptr @_RNvMNtCsdHhxNI3WGqv_5alloc5boxedINtB2_3BoxNtCsfFJBsiz42Ac_17supertrait_vtable1SE3newBG_() #10
  %0 = insertvalue { ptr, ptr } poison, ptr %_1, 0
  %1 = insertvalue { ptr, ptr } %0, ptr @vtable.0, 1
  ret { ptr, ptr } %1
}

; <alloc::alloc::Global>::alloc_impl_runtime
; Function Attrs: inlinehint nonlazybind uwtable
define internal { ptr, i64 } @_RNvMNtCsdHhxNI3WGqv_5alloc5allocNtB2_6Global18alloc_impl_runtimeCsfFJBsiz42Ac_17supertrait_vtable(i64 %layout.0, i64 %layout.1, i1 zeroext %zeroed) unnamed_addr #1 {
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
  call void @_RNvNvMs1_NtNtCsl1Y3iNB2xjl_4core3ptr8non_nullINtB7_7NonNullpE13new_unchecked18precondition_checkCsfFJBsiz42Ac_17supertrait_vtable(ptr %_19, ptr align 8 @alloc_4693b25d3eabde0252d3a3cfc0a04ff1) #11
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
  call void @_RNvCs2fcwfXhWpkc_7___rustc35___rust_no_alloc_shim_is_unstable_v2() #12
; call __rustc::__rust_alloc
  %7 = call ptr @_RNvCs2fcwfXhWpkc_7___rustc12___rust_alloc(i64 %layout.1, i64 %layout.0) #12
  store ptr %7, ptr %raw_ptr, align 8
  br label %bb5

bb3:                                              ; preds = %bb1
; call __rustc::__rust_no_alloc_shim_is_unstable_v2
  call void @_RNvCs2fcwfXhWpkc_7___rustc35___rust_no_alloc_shim_is_unstable_v2() #12
; call __rustc::__rust_alloc_zeroed
  %8 = call ptr @_RNvCs2fcwfXhWpkc_7___rustc19___rust_alloc_zeroed(i64 %layout.1, i64 %layout.0) #12
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
  %11 = load ptr, ptr @anon.8d095a5e4ec33b3e631eb8fcc21eb960.0, align 8
  %12 = load i64, ptr getelementptr inbounds (i8, ptr @anon.8d095a5e4ec33b3e631eb8fcc21eb960.0, i64 8), align 8
  store ptr %11, ptr %_0, align 8
  %13 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %12, ptr %13, align 8
  br label %bb6

bb15:                                             ; preds = %bb5
  br label %bb16

bb16:                                             ; preds = %bb15
  %_31 = load ptr, ptr %raw_ptr, align 8
; call <core::ptr::non_null::NonNull<_>>::new_unchecked::precondition_check
  call void @_RNvNvMs1_NtNtCsl1Y3iNB2xjl_4core3ptr8non_nullINtB7_7NonNullpE13new_unchecked18precondition_checkCsfFJBsiz42Ac_17supertrait_vtable(ptr %_31, ptr align 8 @alloc_5ba1495433bc7bd4d57e2fc7e46f3ce7) #11
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
  call void @_RNvNvMs1_NtNtCsl1Y3iNB2xjl_4core3ptr8non_nullINtB7_7NonNullpE13new_unchecked18precondition_checkCsfFJBsiz42Ac_17supertrait_vtable(ptr %ptr, ptr align 8 @alloc_4693b25d3eabde0252d3a3cfc0a04ff1) #11
  br label %bb21

bb21:                                             ; preds = %bb19
  store ptr %ptr, ptr %_0, align 8
  %14 = getelementptr inbounds i8, ptr %_0, i64 8
  store i64 %layout.1, ptr %14, align 8
  br label %bb6
}

; <alloc::boxed::Box<supertrait_vtable::S>>::new
; Function Attrs: alwaysinline nonlazybind uwtable
define internal align 1 ptr @_RNvMNtCsdHhxNI3WGqv_5alloc5boxedINtB2_3BoxNtCsfFJBsiz42Ac_17supertrait_vtable1SE3newBG_() unnamed_addr #2 personality ptr @rust_eh_personality {
start:
  %0 = alloca [16 x i8], align 8
; invoke alloc::boxed::box_new_uninit
  %_3 = invoke ptr @_RNvNtCsdHhxNI3WGqv_5alloc5boxed14box_new_uninitCsfFJBsiz42Ac_17supertrait_vtable(i64 1, i64 0)
          to label %bb1 unwind label %cleanup

bb3:                                              ; preds = %cleanup
  %1 = load ptr, ptr %0, align 8
  %2 = getelementptr inbounds i8, ptr %0, i64 8
  %3 = load i32, ptr %2, align 8
  %4 = insertvalue { ptr, i32 } poison, ptr %1, 0
  %5 = insertvalue { ptr, i32 } %4, i32 %3, 1
  resume { ptr, i32 } %5

cleanup:                                          ; preds = %start
  %6 = landingpad { ptr, i32 }
          cleanup
  %7 = extractvalue { ptr, i32 } %6, 0
  %8 = extractvalue { ptr, i32 } %6, 1
  store ptr %7, ptr %0, align 8
  %9 = getelementptr inbounds i8, ptr %0, i64 8
  store i32 %8, ptr %9, align 8
  br label %bb3

bb1:                                              ; preds = %start
  ret ptr %_3
}

; alloc::boxed::box_new_uninit
; Function Attrs: inlinehint nonlazybind uwtable
define internal ptr @_RNvNtCsdHhxNI3WGqv_5alloc5boxed14box_new_uninitCsfFJBsiz42Ac_17supertrait_vtable(i64 %layout.0, i64 %layout.1) unnamed_addr #1 {
start:
  %_2 = alloca [16 x i8], align 8
; call <alloc::alloc::Global>::alloc_impl_runtime
  %0 = call { ptr, i64 } @_RNvMNtCsdHhxNI3WGqv_5alloc5allocNtB2_6Global18alloc_impl_runtimeCsfFJBsiz42Ac_17supertrait_vtable(i64 %layout.0, i64 %layout.1, i1 zeroext false) #13
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
  call void @_RNvNtCsdHhxNI3WGqv_5alloc5alloc18handle_alloc_error(i64 %layout.0, i64 %layout.1) #14
  unreachable

bb3:                                              ; preds = %start
  %ptr.0 = load ptr, ptr %_2, align 8
  %10 = getelementptr inbounds i8, ptr %_2, i64 8
  %ptr.1 = load i64, ptr %10, align 8
  ret ptr %ptr.0

bb1:                                              ; No predecessors!
  unreachable
}

; <core::ptr::non_null::NonNull<_>>::new_unchecked::precondition_check
; Function Attrs: inlinehint nounwind nonlazybind uwtable
define internal void @_RNvNvMs1_NtNtCsl1Y3iNB2xjl_4core3ptr8non_nullINtB7_7NonNullpE13new_unchecked18precondition_checkCsfFJBsiz42Ac_17supertrait_vtable(ptr %ptr, ptr align 8 %0) unnamed_addr #3 {
start:
  %_5 = ptrtoint ptr %ptr to i64
  %1 = icmp eq i64 %_5, 0
  br i1 %1, label %bb1, label %bb2

bb1:                                              ; preds = %start
; call core::panicking::panic_nounwind_fmt
  call void @_RNvNtCsl1Y3iNB2xjl_4core9panicking18panic_nounwind_fmt(ptr @alloc_560a59ed819b9d9a5841f6e731c4c8e5, ptr inttoptr (i64 421 to ptr), i1 zeroext false, ptr align 8 %0) #15
  unreachable

bb2:                                              ; preds = %start
  ret void
}

; <supertrait_vtable::S as supertrait_vtable::Base>::base
; Function Attrs: nonlazybind uwtable
define void @_RNvXCsfFJBsiz42Ac_17supertrait_vtableNtB2_1SNtB2_4Base4base(ptr align 1 %self) unnamed_addr #0 {
start:
  ret void
}

; <supertrait_vtable::S as supertrait_vtable::B>::b
; Function Attrs: nonlazybind uwtable
define void @_RNvXs0_CsfFJBsiz42Ac_17supertrait_vtableNtB5_1SNtB5_1B1b(ptr align 1 %self) unnamed_addr #0 {
start:
  ret void
}

; <supertrait_vtable::S as supertrait_vtable::Diamond>::diamond
; Function Attrs: nonlazybind uwtable
define void @_RNvXs1_CsfFJBsiz42Ac_17supertrait_vtableNtB5_1SNtB5_7Diamond7diamond(ptr align 1 %self) unnamed_addr #0 {
start:
  ret void
}

; <supertrait_vtable::S as supertrait_vtable::A>::a
; Function Attrs: nonlazybind uwtable
define void @_RNvXs_CsfFJBsiz42Ac_17supertrait_vtableNtB4_1SNtB4_1A1a(ptr align 1 %self) unnamed_addr #0 {
start:
  ret void
}

; Function Attrs: nonlazybind uwtable
define { ptr, ptr } @upcast_diamond_to_b(ptr align 1 %x.0, ptr align 4 %x.1) unnamed_addr #0 {
start:
  %_0.1 = call ptr @llvm.load.relative.i32(ptr %x.1, i32 24), !invariant.load !3
  %0 = insertvalue { ptr, ptr } poison, ptr %x.0, 0
  %1 = insertvalue { ptr, ptr } %0, ptr %_0.1, 1
  ret { ptr, ptr } %1
}

; __rustc::__rust_no_alloc_shim_is_unstable_v2
; Function Attrs: nounwind nonlazybind uwtable
declare void @_RNvCs2fcwfXhWpkc_7___rustc35___rust_no_alloc_shim_is_unstable_v2() unnamed_addr #4

; __rustc::__rust_alloc
; Function Attrs: nounwind nonlazybind allockind("alloc,uninitialized,aligned") allocsize(0) uwtable
declare noalias ptr @_RNvCs2fcwfXhWpkc_7___rustc12___rust_alloc(i64, i64 allocalign) unnamed_addr #5

; __rustc::__rust_alloc_zeroed
; Function Attrs: nounwind nonlazybind allockind("alloc,zeroed,aligned") allocsize(0) uwtable
declare noalias ptr @_RNvCs2fcwfXhWpkc_7___rustc19___rust_alloc_zeroed(i64, i64 allocalign) unnamed_addr #6

; Function Attrs: nounwind nonlazybind uwtable
declare i32 @rust_eh_personality(i32, i32, i64, ptr, ptr) unnamed_addr #4

; alloc::alloc::handle_alloc_error
; Function Attrs: cold minsize noreturn nonlazybind optsize uwtable
declare void @_RNvNtCsdHhxNI3WGqv_5alloc5alloc18handle_alloc_error(i64, i64) unnamed_addr #7

; core::panicking::panic_nounwind_fmt
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtCsl1Y3iNB2xjl_4core9panicking18panic_nounwind_fmt(ptr, ptr, i1 zeroext, ptr align 8) unnamed_addr #8

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: read)
declare ptr @llvm.load.relative.i32(ptr, i32) #9

attributes #0 = { nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { inlinehint nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { alwaysinline nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { inlinehint nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #4 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #5 = { nounwind nonlazybind allockind("alloc,uninitialized,aligned") allocsize(0) uwtable "alloc-family"="__rust_alloc" "alloc-variant-zeroed"="_RNvCs2fcwfXhWpkc_7___rustc19___rust_alloc_zeroed" "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #6 = { nounwind nonlazybind allockind("alloc,zeroed,aligned") allocsize(0) uwtable "alloc-family"="__rust_alloc" "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #7 = { cold minsize noreturn nonlazybind optsize uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #8 = { cold noinline noreturn nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #9 = { nocallback nofree nosync nounwind willreturn memory(argmem: read) }
attributes #10 = { alwaysinline }
attributes #11 = { inlinehint nounwind }
attributes #12 = { nounwind }
attributes #13 = { inlinehint }
attributes #14 = { noreturn }
attributes #15 = { noinline noreturn nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{!"rustc version 1.95.0-dev"}
!3 = !{}
