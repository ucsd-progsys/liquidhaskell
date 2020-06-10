#!/usr/bin/env bash

TASTY_GLOB_PATTERN=$1

stack build --test --no-run-tests --stack-yaml=stack-8.6.5.yaml && \
    stack test --stack-yaml=stack-8.6.5.yaml -j1 liquidhaskell:test \
    --flag liquidhaskell:include --flag liquidhaskell:-testNewExecutable \
    --ta="--liquid-runner \"stack --stack-yaml=$PWD/stack-8.6.5.yaml exec -- liquid-legacy\"" \
    --ta="-p /$TASTY_GLOB_PATTERN/"
