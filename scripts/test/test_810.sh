#!/usr/bin/env bash

TASTY_GLOB_PATTERN=$1

RUNNER="\"stack exec -- liquid -v0 -hide-package ghc-prim -hide-package containers -hide-package vector -hide-package bytestring\""

stack build --fast --test --no-run-tests && 
    stack test --fast -j1 liquidhaskell:test \
    --ta="-p /$TASTY_GLOB_PATTERN/" \
    --ta="--liquid-runner $RUNNER"
