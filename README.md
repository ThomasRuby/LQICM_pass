# Loop Quasi-Ivariant Chunk Motion (LQICM) LLVM Pass

This pass is a draft prototype! 

**For the moment**, it provides an invariance degrees for
instructions, inner branches and loops (we call them *chunks*). It can
also peel (disabled by default because it's not stable yet) the
*chunks* regarding to the degrees computed previously.

## Prerequisites

You need [LLVM](http://llvm.org/git/llvm.git) with
[clang](http://llvm.org/git/clang.git), I use the `release_40` branch.

## Install and use

Build:

    $ cd lqicm_pass
    $ edit build.sh → give the right LLVM-DIR path to cmake
    $ ./build.sh

To use `initialize…Pass(…)` registration I added
`initializeLegacyLQICMPassPass(PassRegistry*);` in
`include/llvm/InitializePasses.h` it should exist a better way…

Run:

    $ edit run.sh → give the right LLVM_BUILD path
    $ ./run.sh something.(c|ll)

Example:

    $ ./run.sh test/files/Fact.c

↑ This is a basic same factorial computed *n* times. This pass detects
the invariance of the entire loop and can peel it (see also `Fact4.c`
which has the same factorial but of invariance degree equal to 4,
means that the loop needs to be peeled four times before hoisting the
factorial loop).

The pass is enabled by default when the `libLQICMPass.so` is loaded to
`opt` or directly into `clang` (using `-load` option).

Registered as `EP_ModuleOptimizerEarly` it can provides statistics
(with `-mllvm -stats` flags) on quasi-invariants detected before loop
optimizations.

## First Statistics 

By adding the `lqicm` analysis pass before each iteration of `licm` we
can compare the number of invariants detected. 
We decided to compare them with the `-Oz` optimization level to avoid
loop rotations (`lqicm` can't analyze this form of loop for the
moment).  Here we compile `vim` with the flags `-fno-vectorize
-fno-slp-vectorize -Oz`:

First, it's important to know that, at `-Oz`, `licm` is performed 3
times and hoists ~1500 instructions less than at `-O3`.

7m45,496s | user time
--- | ---
3808 | number of loops at `EP_ModuleOptimizerEarly`
13178 | total number of times `lqicm LoopPass` was launched
8062 | number of all *Instructions* hoisted by `licm`
160 | number of instructions sunk by `licm`
6525 | total number of times `lqicm` has analyzed the loop (over 13178)
7632 | number of *all* quasi-invariants detected
808 | number of quasi-invariants *Chunk* detected
6824 | number of quasi-invariants *Instructions*
43 | number of chunks with invariance degree >= 2

We can suppose that over half of the times `licm` is performed, we
find 6824 quasi-invariants instructions which is ~85% of the total
invariants hoisted by `licm`. Plus we found 808 quasi-invariants
chunks.

## Remarks

Note that there are some restrictions on the form of the loop: some of
the loops with several exit blocks, latches, rotated or without header
are not analyzed.  See that ~50% of the time, loops are not analyzed
in the previous statistics, this is why results are biased (it's
probably more). We are currently working for the flexibility of our
analysis.
