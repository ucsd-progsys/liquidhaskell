#!/usr/bin/env bash

TEST_GROUPS="$@"

LIQUID_CABAL_PROJECT_FILE=cabal.ghc9.project liquidhaskell_datadir=$PWD cabal v2-run --project-file cabal.ghc9.project tests:test-driver -- "$TEST_GROUPS"
