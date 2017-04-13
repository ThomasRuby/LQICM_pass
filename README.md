# Loop Quasi-Ivariant Chunk Motion (LQICM) LLVM Pass

This pass is a draft prototype! 

**For the moment**, it provides an invariance degree for instructions,
inner branches and loops (we call them *chunks*). It also peels
(disabled by default) the previous *chunks* regarding to the degrees
computed previously.

Build:

    $ cd lqicm_pass
    $ edit build.sh → give the right LLVM-DIR path to cmake
    $ ./build.sh

Run:

    $ edit run.sh → give the right LLVM_BUILD path
    $ ./run.sh something.c/ll

Example:

    $ ./run.sh test/files/Fact.c

↑ This is a basic same factorial computed *n* times. This pass detects
the invariance of the entire loop and can peel it (see also `Fact4.c`
which has the same factorial but of invariance degree equal to 2,
means that the loop can be peeled twice).

## Statistics 

The pass is enabled by default when the `libLQICMPass.so` is loaded to
`opt` or directly into `clang` (using `-load` option).

Registered as `EP_ModuleOptimizerEarly` it can provides statistics
(with `-mllvm -stats` flags) on quasi-invariants detected before loop
optimizations as here for `vim`:

11m16,296s | vim -O3 ModuleOptimizerEarly
--- | ---
3808 | number of loops
32111 | number of instructions hoisted by LICM
2266 | number of loops with several exit blocks
125 | number of loops not well formed
2391 | sum of loop not analyzed
1417 | sum of loop analyzed by LQICM
2480 | number of quasi-invariants detected
333 | number of quasi-invariants Chunk detected
24 | Number of chunks with deg >= 2

## Remarks

Note that there are some restrictions on the form of the loop: loops
with several exit blocks, latches or without header are not analyzed.
See that ~63% of the loops are not analyzed in the previous
statistics, this is why results are biased (it's probably be more) and
it's worse if `LQICM` is placed after the loop optimizations. We are
currently working for the flexibility of our analysis.
