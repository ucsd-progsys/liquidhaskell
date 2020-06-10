#!/usr/bin/env bash

TASTY_GLOB_PATTERN=$1

cabal v2-build all && \
liquidhaskell_datadir=$PWD cabal v2-test -j1 liquidhaskell:test \
  --flag plugin --flag include --flag devel --test-show-details=streaming \
  --test-option="-p /$TASTY_GLOB_PATTERN/" \
  --test-option="--liquid-runner=cabal -v0 v2-exec liquid -- -v0 \
                          -package-env=$(./scripts/generate_testing_ghc_env) \
                          -package=liquidhaskell -package=Cabal " \
