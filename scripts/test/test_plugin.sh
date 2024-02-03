#!/usr/bin/env bash

TEST_GROUPS="$@"

cabal v2-run tests:test-driver -- $TEST_GROUPS
