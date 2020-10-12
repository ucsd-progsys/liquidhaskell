#!/usr/bin/env bash

TASTY_GLOB_PATTERN=$1

cabal v2-build --project-file cabal.ghc9.project all && \
liquidhaskell_datadir=$PWD cabal v2-test --project-file cabal.ghc9.project -j1 liquidhaskell:test \
  --flag include --flag devel --test-show-details=streaming \
  --test-option="-p /$TASTY_GLOB_PATTERN/" \
  --test-option="--liquid-runner=cabal -v0 v2-exec --project-file cabal.ghc9.project liquidhaskell -- -v0 \
                          -package-env=$(./scripts/generate_testing_ghc_env cabal.ghc9.project) \
                          -package=liquidhaskell -package=liquid-base -package=Cabal " \
