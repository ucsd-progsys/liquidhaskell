#!/usr/bin/env bash

TASTY_GLOB_PATTERN=$1

stack build --test --no-run-tests --stack-yaml=stack-8.8.4.yaml && \
    stack test --stack-yaml=stack-8.8.4.yaml -j1 liquidhaskell:test \
    --flag liquidhaskell:include \
    --ta="--liquid-runner \"stack --stack-yaml=$PWD/stack-8.8.4.yaml exec -- liquid\"" \
    --ta="-p /$TASTY_GLOB_PATTERN/"
