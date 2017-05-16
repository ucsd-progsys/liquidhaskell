# Getting Started Guide

- Load the VMDK into VirtualBox v5.1.22 (other VM players may work but have not been tested).
- The password, should you need it, is `icfp17aec`.

## Basic usage

LiquidHaskell+FUSION is run using `stack exec -- liquid FILE`. Try this with the examples from Figure 2 of the paper:

    cd ~/liquidhaskell/benchmarks/icfp17
    stack exec -- liquid Fig2Examples.hs

The output will end in "**** RESULT: SAFE ****", indicating that the tool has determined the code meets its specification. Next, re-run the command with FUSION disabled:

    stack exec -- liquid Fig2Examples.hs --no-eliminate

This time it will say UNSAFE because regular liquid inference is insufficient to verify any of the examples. (You'll see that our examples 1 and 2 are slightly different from the paper - this is because we have to prevent ghc from simplifying those on its own).

Try modifying the examples. For example, if you change `inc` to `dec` on line 30, `liquid` should now return UNSAFE (with or without FUSION) because the program now fails to meet its specification.

# Step-by-Step Instructions

## Replicating the LOC/Time results in Table 1

    cd ~/liquidhaskell
    python scripts/metrics.py
    cat metrics.csv

This should take ~40 minutes. It will run LiquidHaskell on all the benchmarks twice - first with FUSION turned on and then with it off. Note that in the run without FUSION, some benchmarks will FAIL (including ApplicativeReader, which is set to automatically fail so you don't have to wait for it to time out). The table produced at the end will still have times recorded for the failing benchmarks; in Table 1 of the paper we replaced these time-to-fail values with asterisks.

You will see a discrepancy between the "Code" value you get for the TEXT benchmark and the one in the paper: in preparing this artifact, we noticed that the paper's value incorrectly counts some extra files; this value will be fixed in the final version.

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

(The code still calls FUSION by its original working name `eliminate`. It is ON by default in `liquid` and OFF by default in `fixpoint` - hence the respective flags `--no-eliminate` and `--eliminate` appearing in this document.)
