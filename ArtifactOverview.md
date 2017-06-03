# Getting Started Guide

- Load the VMDK into VirtualBox v5.1.22 (other VM players may work but have not been tested).
- The password, should you need it, is `icfp17aec`.

## Basic usage

LiquidHaskell+FUSION is run using `stack exec -- liquid FILE`. Try this with the examples from Figure 2 of the paper:

    cd ~/liquidhaskell/benchmarks/icfp17
    stack exec -- liquid Fig2Examples.hs

The output will end in "**** RESULT: SAFE ****", indicating that the tool has determined the code meets its specification. Next, re-run the command with FUSION disabled:

    stack exec -- liquid Fig2Examples.hs --eliminate=none

This time it will say UNSAFE because regular liquid inference is insufficient to verify any of the examples. (You'll see that our examples 1 and 2 are slightly different from the paper - this is because we have to prevent ghc from simplifying those on its own).

Try modifying the examples. For example, if you change `inc` to `dec` on line 30, `liquid` should now return UNSAFE (with or without FUSION) because the program now fails to meet its specification.

# Step-by-Step Instructions

## Replicating the LOC/Time results in Table 1

    cd ~/liquidhaskell
    python scripts/metrics.py
    cat metrics.csv

This should take ~40 minutes. It will run LiquidHaskell on all the benchmarks twice - first with FUSION turned on and then with it off. Note that in the run without FUSION, some benchmarks will FAIL. The table produced at the end will still have times recorded for the failing benchmarks; we replace these time-to-fail values with asterisks below.

You will see several discrepancies between the table you just generated and Table 1 from the original paper submission. This is because several tests were deprecated and also the code was optimized between then and now; the table appearing in the final version of the paper (and the metrics.csv file you produce) should look more like this:

Benchmark, Files, Code, Spec, Time (L), Time (F)
DATA-STRUCT, 8, 1818, 408, 137, 99
VEC-ALGOS, 11, 1252, 279, 79, 62
BYTESTRING, 11, 4811, 726, 357, 193
TEXT, 17, 3157, 818, 397, 256
ARITH, 2, 270, 46, *, 7
FOLD, 1, 73, 29, 1, 1
MONOID, 2, 85, 16, 1, 1
FUNCTOR, 3, 137, 28, 2, 2
APPLICATIVE, 2, 146, 36, *, 2
MONAD, 3, 180, 42, 3, 3
SAT-SOLVER, 1, 98, 31, *, 1
UNIFICATION, 1, 144, 53, 3, 3

## Replicating the qualifier results in Table 1

Finding the minimal sets of qualifiers takes many hours, because we have to run each query repeatedly with different sets of qualifiers in a "delta debugging" fashion until we find a minimal set for which the file can still be verified. Thus, we have not made this step automated in `metrics.py` above. However, if you want to see this process in action, you can do the following:

    cd ~/liquidhaskell/benchmarks/icfp17
    stack exec -- liquid data-structs/Splay.hs --save
    stack exec -- fixpoint data-structs/.liquid/Splay.hs.bfq --minimizeqs

This should take a total of ~2 minutes, and in the end inform you that verifying this file requires 5 qualifiers (without FUSION). Now run the last command again with FUSION turned on:

    stack exec -- fixpoint data-structs/.liquid/Splay.hs.bfq --minimizeqs --eliminate

This time it should take <1 minute to inform you that only 3 qualifiers are now required.

You can run the same process with files other than Splay.hs, but beware that some take a very long time, some require additional flags to run (see `extraOptions` in our test script `tests/test.hs`), and some will fail entirely without FUSION. To replicate our results, you could first run the benchmark suite, telling it to dump all query files (and other temporary files) to disk as it runs:

    cd ~/liquidhaskell/benchmarks/icfp17
    stack test liquidhaskell --test-arguments="--liquid-opts \"--save\""

Then run `--minimizeqs` on each `.bfq` file that was produced:

    find . -name "*hs.bfq" | xargs -n1 stack exec -- fixpoint --minimizeqs --eliminate
    find . -name "*hs.bfq" | xargs -n1 stack exec -- fixpoint --minimizeqs

This gets you the results with then without FUSION.

(The code still calls FUSION by its original working name `eliminate`. It is ON by default in `liquid` and OFF by default in `fixpoint` - hence the flags that appear in this document include liquid's flag `--eliminate=none` to turn it off, and fixpoint's flag `--eliminate` to turn it on.)
