#!/usr/bin/env bash

TEST_GROUPS="$@"

liquidhaskell_datadir=$PWD cabal v2-run tests:test-driver -- "$TEST_GROUPS"
