#!/usr/bin/env bash

TASTY_GLOB_PATTERN=$1

RUNNER="\"stack --silent exec -- liquid-legacy\""

stack build --flag liquidhaskell:no-plugin --flag liquid-platform:legacy --test --no-run-tests &&
    stack test -j1 liquidhaskell:test --flag liquidhaskell:include \
    --flag liquid-platform:legacy --flag liquid-platform:devel --flag liquidhaskell:no-plugin \
    --ta="-p /$TASTY_GLOB_PATTERN/" \
    --ta="--liquid-runner $RUNNER"
