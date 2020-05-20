#!/usr/bin/env bash

TASTY_GLOB_PATTERN=$1

RUNNER="\"stack --silent exec -- liquid -v0 \""

stack build --fast --test --no-run-tests && 
    stack test --fast -j1 liquidhaskell:test \
    --ta="-p /$TASTY_GLOB_PATTERN/" \
    --ta="--liquid-runner $RUNNER"
