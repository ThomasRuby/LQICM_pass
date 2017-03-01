# Loop Quasi-Ivariant Chunk Motion LLVM Pass

This pass is a prototype! 

For the moment, it provides an invariance degree for instructions,
inner branches and loops (we call them *chunks*). It also peels the
previous *chunks* regarding to the degrees computed previously.

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
the invariance of the entire loop and peels it.
