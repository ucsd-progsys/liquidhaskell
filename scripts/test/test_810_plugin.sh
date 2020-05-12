cabal v2-build all && \
liquidhaskell_datadir=$PWD cabal v2-test -j1 liquidhaskell:test \
  --flag plugin --flag include --flag devel --test-show-details=streaming \
  --test-option="--liquid-runner=cabal -v0 v2-exec ghc -- -v0 --make -no-link \
                          -Wno-inline-rule-shadowing \
                          -package-env=$(./scripts/generate_testing_ghc_env) \
                          -package liquid-base -package liquid-prelude -package liquid-vector \
                          -package liquid-containers -package liquid-bytestring -package liquidhaskell \
                          -package Cabal \
                          -fplugin=Language.Haskell.Liquid.GHC.Plugin " \
  --test-option="-p /$1/"
