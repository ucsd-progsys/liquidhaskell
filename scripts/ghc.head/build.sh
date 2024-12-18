#!/usr/bin/env bash
set -eux
git clone https://gitlab.haskell.org/ghc/ghc.git ghc.head
cd ghc.head
git submodule update --init --recursive
NIX_SHELL="nix-shell -p haskell.compiler.ghc982 happy alex ncurses python3 gmp cabal-install autoconf automake --run"
$NIX_SHELL "./boot"
$NIX_SHELL "./configure"
$NIX_SHELL "./hadrian/build -j"
