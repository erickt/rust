; ModuleID = 'test_fuchsia.1f4395d86e2e4329-cgu.0'
source_filename = "test_fuchsia.1f4395d86e2e4329-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; test_fuchsia::use_foo
; Function Attrs: nonlazybind uwtable
define void @_RNvCs2GpT7HjIhWD_12test_fuchsia7use_foo(ptr align 1 %x.0, ptr align 8 %x.1) unnamed_addr #0 {
start:
  %0 = getelementptr inbounds i8, ptr %x.1, i64 24
  %1 = load ptr, ptr %0, align 8, !invariant.load !3, !nonnull !3
  call void %1(ptr align 1 %x.0) #1
  ret void
}

; <() as test_fuchsia::Foo>::bar
; Function Attrs: nonlazybind uwtable
define void @_RNvXCs2GpT7HjIhWD_12test_fuchsiauNtB2_3Foo3bar(ptr align 1 %self) unnamed_addr #0 {
start:
  ret void
}

attributes #0 = { nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { inlinehint }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{!"rustc version 1.95.0-dev"}
!3 = !{}
