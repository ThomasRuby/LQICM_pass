# Loop Quasi-Ivariant Chunk Motion LLVM Pass

This pass is a prototype! 

For the moment, it provides an invariance degree for instructions and
inner loops. In the near future it *will* peel the loop regarding to
the degrees computed previously.

Build:

    $ cd lqicm_pass
    $ edit build.sh → give the right LLVM-DIR path to cmake
    $ ./build.sh

Run:

    $ edit run.sh → give the right LLVM_BUILD path
    $ ./run.sh something.c
