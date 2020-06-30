#!/usr/bin/env bash

TASTY_GLOB_PATTERN=$1

RUNNER="\"stack --silent exec -- liquidhaskell -v0 \""

stack test -j1 liquidhaskell:test liquid-platform:liquidhaskell \
    --ta="-p /$TASTY_GLOB_PATTERN/" \
    --ta="--liquid-runner $RUNNER"
