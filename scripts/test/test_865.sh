#!/usr/bin/env bash

TASTY_GLOB_PATTERN=$1

stack build --stack-yaml=stack-8.6.5.yaml --fast liquidhaskell:exe:liquid-legacy && \
    stack test --stack-yaml=stack-8.6.5.yaml -j1 liquidhaskell:test \
    --flag liquidhaskell:include --flag liquidhaskell:devel \
    --ta="--liquid-runner \"stack --stack-yaml=$PWD/stack-8.6.5.yaml exec -- liquid \"" \
    --ta="-p /$TASTY_GLOB_PATTERN/" --fast
