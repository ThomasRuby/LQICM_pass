; ModuleID = './LICMtest/llvmIR/tmp.ll'
source_filename = "LICMtest/files/Fact.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@.str = private unnamed_addr constant [13 x i8] c"blabla %d %d\00", align 1

; Function Attrs: noinline nounwind uwtable
define i32 @main() local_unnamed_addr #0 {
entry:
  %call = tail call i64 @time(i64* null) #2
  %conv = trunc i64 %call to i32
  tail call void @srand(i32 %conv) #2
  %call1 = tail call i32 @rand() #2
  %rem = srem i32 %call1, 100
  %cmp47 = icmp sgt i32 %rem, 1
  br i1 %cmp47, label %while.cond3.preheader.us.preheader, label %while.end8

while.cond3.preheader.us.preheader:               ; preds = %entry
  %0 = add nsw i32 %rem, -1
  %1 = add nsw i32 %rem, -9
  %2 = lshr i32 %1, 3
  %3 = add nuw nsw i32 %2, 1
  %min.iters.check = icmp ult i32 %0, 8
  %n.vec = and i32 %0, -8
  %cmp.zero = icmp eq i32 %n.vec, 0
  %ind.end = or i32 %n.vec, 1
  %xtraiter = and i32 %3, 3
  %lcmp.mod = icmp eq i32 %xtraiter, 0
  %4 = icmp ult i32 %1, 24
  %cmp.n = icmp eq i32 %0, %n.vec
  br label %while.cond3.preheader.us

while.cond3.preheader.us:                         ; preds = %while.cond3.preheader.us.preheader, %while.cond3.while.end_crit_edge.us
  %j.011.us = phi i32 [ %add7.us, %while.cond3.while.end_crit_edge.us ], [ 0, %while.cond3.preheader.us.preheader ]
  br i1 %min.iters.check, label %while.body6.us.preheader, label %min.iters.checked

min.iters.checked:                                ; preds = %while.cond3.preheader.us
  br i1 %cmp.zero, label %while.body6.us.preheader, label %vector.body.preheader

vector.body.preheader:                            ; preds = %min.iters.checked
  br i1 %lcmp.mod, label %vector.body.prol.loopexit, label %vector.body.prol.preheader

vector.body.prol.preheader:                       ; preds = %vector.body.preheader
  br label %vector.body.prol

vector.body.prol:                                 ; preds = %vector.body.prol, %vector.body.prol.preheader
  %index.prol = phi i32 [ %index.next.prol, %vector.body.prol ], [ 0, %vector.body.prol.preheader ]
  %vec.ind.prol = phi <4 x i32> [ %vec.ind.next.prol, %vector.body.prol ], [ <i32 1, i32 2, i32 3, i32 4>, %vector.body.prol.preheader ]
  %vec.phi.prol = phi <4 x i32> [ %5, %vector.body.prol ], [ <i32 1, i32 1, i32 1, i32 1>, %vector.body.prol.preheader ]
  %vec.phi16.prol = phi <4 x i32> [ %6, %vector.body.prol ], [ <i32 1, i32 1, i32 1, i32 1>, %vector.body.prol.preheader ]
  %prol.iter = phi i32 [ %prol.iter.sub, %vector.body.prol ], [ %xtraiter, %vector.body.prol.preheader ]
  %step.add.prol = add <4 x i32> %vec.ind.prol, <i32 4, i32 4, i32 4, i32 4>
  %5 = mul nsw <4 x i32> %vec.ind.prol, %vec.phi.prol
  %6 = mul nsw <4 x i32> %step.add.prol, %vec.phi16.prol
  %index.next.prol = add i32 %index.prol, 8
  %vec.ind.next.prol = add <4 x i32> %vec.ind.prol, <i32 8, i32 8, i32 8, i32 8>
  %prol.iter.sub = add i32 %prol.iter, -1
  %prol.iter.cmp = icmp eq i32 %prol.iter.sub, 0
  br i1 %prol.iter.cmp, label %vector.body.prol.loopexit.unr-lcssa, label %vector.body.prol, !llvm.loop !1

vector.body.prol.loopexit.unr-lcssa:              ; preds = %vector.body.prol
  br label %vector.body.prol.loopexit

vector.body.prol.loopexit:                        ; preds = %vector.body.preheader, %vector.body.prol.loopexit.unr-lcssa
  %.lcssa20.unr = phi <4 x i32> [ undef, %vector.body.preheader ], [ %5, %vector.body.prol.loopexit.unr-lcssa ]
  %.lcssa.unr = phi <4 x i32> [ undef, %vector.body.preheader ], [ %6, %vector.body.prol.loopexit.unr-lcssa ]
  %index.unr = phi i32 [ 0, %vector.body.preheader ], [ %index.next.prol, %vector.body.prol.loopexit.unr-lcssa ]
  %vec.ind.unr = phi <4 x i32> [ <i32 1, i32 2, i32 3, i32 4>, %vector.body.preheader ], [ %vec.ind.next.prol, %vector.body.prol.loopexit.unr-lcssa ]
  %vec.phi.unr = phi <4 x i32> [ <i32 1, i32 1, i32 1, i32 1>, %vector.body.preheader ], [ %5, %vector.body.prol.loopexit.unr-lcssa ]
  %vec.phi16.unr = phi <4 x i32> [ <i32 1, i32 1, i32 1, i32 1>, %vector.body.preheader ], [ %6, %vector.body.prol.loopexit.unr-lcssa ]
  br i1 %4, label %middle.block, label %vector.body.preheader.new

vector.body.preheader.new:                        ; preds = %vector.body.prol.loopexit
  br label %vector.body

vector.body:                                      ; preds = %vector.body, %vector.body.preheader.new
  %index = phi i32 [ %index.unr, %vector.body.preheader.new ], [ %index.next.3, %vector.body ]
  %vec.ind = phi <4 x i32> [ %vec.ind.unr, %vector.body.preheader.new ], [ %vec.ind.next.3, %vector.body ]
  %vec.phi = phi <4 x i32> [ %vec.phi.unr, %vector.body.preheader.new ], [ %13, %vector.body ]
  %vec.phi16 = phi <4 x i32> [ %vec.phi16.unr, %vector.body.preheader.new ], [ %14, %vector.body ]
  %step.add = add <4 x i32> %vec.ind, <i32 4, i32 4, i32 4, i32 4>
  %7 = mul nsw <4 x i32> %vec.ind, %vec.phi
  %8 = mul nsw <4 x i32> %step.add, %vec.phi16
  %vec.ind.next = add <4 x i32> %vec.ind, <i32 8, i32 8, i32 8, i32 8>
  %step.add.1 = add <4 x i32> %vec.ind, <i32 12, i32 12, i32 12, i32 12>
  %9 = mul nsw <4 x i32> %vec.ind.next, %7
  %10 = mul nsw <4 x i32> %step.add.1, %8
  %vec.ind.next.1 = add <4 x i32> %vec.ind, <i32 16, i32 16, i32 16, i32 16>
  %step.add.2 = add <4 x i32> %vec.ind, <i32 20, i32 20, i32 20, i32 20>
  %11 = mul nsw <4 x i32> %vec.ind.next.1, %9
  %12 = mul nsw <4 x i32> %step.add.2, %10
  %vec.ind.next.2 = add <4 x i32> %vec.ind, <i32 24, i32 24, i32 24, i32 24>
  %step.add.3 = add <4 x i32> %vec.ind, <i32 28, i32 28, i32 28, i32 28>
  %13 = mul nsw <4 x i32> %vec.ind.next.2, %11
  %14 = mul nsw <4 x i32> %step.add.3, %12
  %index.next.3 = add i32 %index, 32
  %vec.ind.next.3 = add <4 x i32> %vec.ind, <i32 32, i32 32, i32 32, i32 32>
  %15 = icmp eq i32 %index.next.3, %n.vec
  br i1 %15, label %middle.block.unr-lcssa, label %vector.body, !llvm.loop !3

middle.block.unr-lcssa:                           ; preds = %vector.body
  br label %middle.block

middle.block:                                     ; preds = %vector.body.prol.loopexit, %middle.block.unr-lcssa
  %.lcssa20 = phi <4 x i32> [ %.lcssa20.unr, %vector.body.prol.loopexit ], [ %13, %middle.block.unr-lcssa ]
  %.lcssa = phi <4 x i32> [ %.lcssa.unr, %vector.body.prol.loopexit ], [ %14, %middle.block.unr-lcssa ]
  %bin.rdx = mul <4 x i32> %.lcssa, %.lcssa20
  %rdx.shuf = shufflevector <4 x i32> %bin.rdx, <4 x i32> undef, <4 x i32> <i32 2, i32 3, i32 undef, i32 undef>
  %bin.rdx17 = mul <4 x i32> %bin.rdx, %rdx.shuf
  %rdx.shuf18 = shufflevector <4 x i32> %bin.rdx17, <4 x i32> undef, <4 x i32> <i32 1, i32 undef, i32 undef, i32 undef>
  %bin.rdx19 = mul <4 x i32> %bin.rdx17, %rdx.shuf18
  %16 = extractelement <4 x i32> %bin.rdx19, i32 0
  br i1 %cmp.n, label %while.cond3.while.end_crit_edge.us, label %while.body6.us.preheader

while.body6.us.preheader:                         ; preds = %middle.block, %min.iters.checked, %while.cond3.preheader.us
  %i.19.us.ph = phi i32 [ 1, %min.iters.checked ], [ 1, %while.cond3.preheader.us ], [ %ind.end, %middle.block ]
  %fact.18.us.ph = phi i32 [ 1, %min.iters.checked ], [ 1, %while.cond3.preheader.us ], [ %16, %middle.block ]
  br label %while.body6.us

while.body6.us:                                   ; preds = %while.body6.us.preheader, %while.body6.us
  %i.19.us = phi i32 [ %add.us, %while.body6.us ], [ %i.19.us.ph, %while.body6.us.preheader ]
  %fact.18.us = phi i32 [ %mul.us, %while.body6.us ], [ %fact.18.us.ph, %while.body6.us.preheader ]
  %mul.us = mul nsw i32 %i.19.us, %fact.18.us
  %add.us = add nuw nsw i32 %i.19.us, 1
  %exitcond = icmp eq i32 %add.us, %rem
  br i1 %exitcond, label %while.cond3.while.end_crit_edge.us.loopexit, label %while.body6.us, !llvm.loop !6

while.cond3.while.end_crit_edge.us.loopexit:      ; preds = %while.body6.us
  br label %while.cond3.while.end_crit_edge.us

while.cond3.while.end_crit_edge.us:               ; preds = %while.cond3.while.end_crit_edge.us.loopexit, %middle.block
  %mul.us.lcssa = phi i32 [ %16, %middle.block ], [ %mul.us, %while.cond3.while.end_crit_edge.us.loopexit ]
  %add7.us = add nuw nsw i32 %j.011.us, 1
  %exitcond13 = icmp eq i32 %add7.us, 100
  br i1 %exitcond13, label %while.end8.loopexit, label %while.cond3.preheader.us

while.end8.loopexit:                              ; preds = %while.cond3.while.end_crit_edge.us
  br label %while.end8

while.end8:                                       ; preds = %while.end8.loopexit, %entry
  %fact.0.lcssa = phi i32 [ 1, %entry ], [ %mul.us.lcssa, %while.end8.loopexit ]
  %i.0.lcssa = phi i32 [ 1, %entry ], [ %rem, %while.end8.loopexit ]
  %call9 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([13 x i8], [13 x i8]* @.str, i64 0, i64 0), i32 %i.0.lcssa, i32 %fact.0.lcssa)
  ret i32 %i.0.lcssa
}

; Function Attrs: nounwind
declare void @srand(i32) local_unnamed_addr #1

; Function Attrs: nounwind
declare i64 @time(i64*) local_unnamed_addr #1

; Function Attrs: nounwind
declare i32 @rand() local_unnamed_addr #1

; Function Attrs: nounwind
declare i32 @printf(i8* nocapture readonly, ...) local_unnamed_addr #1

attributes #0 = { noinline nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind }

!llvm.ident = !{!0}

!0 = !{!"clang version 4.0.0 (http://llvm.org/git/clang.git c311b06da6522cfdf2e28000e70ed4dfeb390b37)"}
!1 = distinct !{!1, !2}
!2 = !{!"llvm.loop.unroll.disable"}
!3 = distinct !{!3, !4, !5}
!4 = !{!"llvm.loop.vectorize.width", i32 1}
!5 = !{!"llvm.loop.interleave.count", i32 1}
!6 = distinct !{!6, !7, !4, !5}
!7 = !{!"llvm.loop.unroll.runtime.disable"}
