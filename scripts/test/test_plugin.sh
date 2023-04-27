#!/usr/bin/env bash

TEST_GROUPS="$@"

liquidhaskell_boot_datadir=$PWD/liquidhaskell-boot cabal v2-run tests:test-driver -- $TEST_GROUPS
