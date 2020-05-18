#!/usr/bin/env bash

TASTY_GLOB_PATTERN=$1

stack build --fast liquid-base && 
    stack test -j1 liquidhaskell:test \
    --flag liquidhaskell:devel \
    --ta="-p /$TASTY_GLOB_PATTERN/" --fast
