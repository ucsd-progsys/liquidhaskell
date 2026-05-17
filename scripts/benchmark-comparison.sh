#!/usr/bin/env bash
#
# benchmark-comparison.sh $1
#
# Builds benchmark comparison charts for $1 vs the current branch.

set -euo pipefail

BEFORE_BRANCH=$1
AFTER_BRANCH=$(git rev-parse HEAD)

clean_run_collect() {
    local run_label="$1"  # "before" or "after"
    echo "Running benchmarks for $run_label branch..."
    find dist-newstyle -name "tests-*" -o -name "prover-ple-lib-*" | xargs rm -rf
    ./scripts/test/test_plugin.sh --measure-timings-j1
    rm -rf tmp tmp-${run_label}
    cabal build ghc-timings
    cabal exec ghc-timings dist-newstyle
    mv tmp tmp-${run_label}
    cabal run benchmark-timings -- tmp-${run_label}/*.json --phase LiquidHaskellCPU -o summary-${run_label}.csv
}

clean_run_collect after

echo "Checking out BEFORE branch: $BEFORE_BRANCH"
git checkout "$BEFORE_BRANCH"
git submodule update --init --recursive
clean_run_collect before
echo "Checking out AFTER branch: $AFTER_BRANCH"
git checkout "$AFTER_BRANCH"
git submodule update --init --recursive

cabal run plot-performance -- -b summary-before.csv -a summary-after.csv -s 50
