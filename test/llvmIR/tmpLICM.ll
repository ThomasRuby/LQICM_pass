; ModuleID = './LICMtest/llvmIR/tmp.ll'
source_filename = "LICMtest/files/Fact.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@.str = private unnamed_addr constant [13 x i8] c"blabla %d %d\00", align 1

; Function Attrs: noinline nounwind uwtable
define i32 @main() #0 {
entry:
  %call = call i64 @time(i64* null) #3
  %conv = trunc i64 %call to i32
  call void @srand(i32 %conv) #3
  %call1 = call i32 @rand() #3
  %rem = srem i32 %call1, 100
  br label %while.cond

while.cond:                                       ; preds = %while.end, %entry
  %fact.0 = phi i32 [ 1, %entry ], [ %fact.1.lcssa, %while.end ]
  %i.0 = phi i32 [ 1, %entry ], [ %i.1.lcssa, %while.end ]
  %j.0 = phi i32 [ 0, %entry ], [ %add7, %while.end ]
  %cmp = icmp slt i32 %j.0, 100
  br i1 %cmp, label %while.cond3.preheader, label %while.end8

while.cond3.preheader:                            ; preds = %while.cond
  br label %while.cond3

while.cond3:                                      ; preds = %while.cond3.preheader, %while.body6
  %fact.1 = phi i32 [ %mul, %while.body6 ], [ 1, %while.cond3.preheader ]
  %i.1 = phi i32 [ %add, %while.body6 ], [ 1, %while.cond3.preheader ]
  %cmp4 = icmp slt i32 %i.1, %rem
  br i1 %cmp4, label %while.body6, label %while.end

while.body6:                                      ; preds = %while.cond3
  %mul = mul nsw i32 %fact.1, %i.1
  %add = add nsw i32 %i.1, 1
  br label %while.cond3

while.end:                                        ; preds = %while.cond3
  %fact.1.lcssa = phi i32 [ %fact.1, %while.cond3 ]
  %i.1.lcssa = phi i32 [ %i.1, %while.cond3 ]
  %add7 = add nsw i32 %j.0, 1
  br label %while.cond

while.end8:                                       ; preds = %while.cond
  %fact.0.lcssa = phi i32 [ %fact.0, %while.cond ]
  %i.0.lcssa = phi i32 [ %i.0, %while.cond ]
  %call9 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([13 x i8], [13 x i8]* @.str, i32 0, i32 0), i32 %i.0.lcssa, i32 %fact.0.lcssa)
  ret i32 %i.0.lcssa
}

; Function Attrs: nounwind
declare void @srand(i32) #1

; Function Attrs: nounwind
declare i64 @time(i64*) #1

; Function Attrs: nounwind
declare i32 @rand() #1

declare i32 @printf(i8*, ...) #2

attributes #0 = { noinline nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.ident = !{!0}

!0 = !{!"clang version 4.0.0 (http://llvm.org/git/clang.git c311b06da6522cfdf2e28000e70ed4dfeb390b37)"}
