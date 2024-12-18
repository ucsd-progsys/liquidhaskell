#!/usr/bin/env bash
set -eux
git clone https://github.com/ucsd-progsys/liquidhaskell.git liquidhaskell.ci.ghc.head
cd liquidhaskell.ci.ghc.head
git submodule update --init --recursive
curl https://ghc.gitlab.haskell.org/head.hackage/cabal.project | grep -v liquidhaskell-boot > cabal.project.local
NIX_SHELL="nix-shell -p z3 cabal-install ncurses gmp --run"
$NIX_SHELL "PATH=$PWD/../ghc.head/_build/stage1/bin:$PATH ./scripts/test/test_plugin.sh"
