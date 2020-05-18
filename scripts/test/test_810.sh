#!/usr/bin/env bash

TASTY_GLOB_PATTERN=$1

stack build --fast --test --no-run-tests && 
    stack test --fast -j1 liquidhaskell:test \
    --ta="-p /$TASTY_GLOB_PATTERN/"
