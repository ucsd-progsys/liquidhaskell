cabal v2-build all && \
liquidhaskell_datadir=$PWD cabal v2-test -j1 liquidhaskell:test \
  --flag plugin --flag include --flag devel --test-show-details=streaming \
  --test-option="--liquid-runner=cabal v2-exec ghc -- --make -no-link \
                          -package-env=$(./scripts/generate_testing_ghc_env) \
                          -package liquid-base -package liquid-prelude -package liquid-vector \
                          -package liquid-containers -package liquid-bytestring -package liquidhaskell \
                          -fplugin=Language.Haskell.Liquid.GHC.Plugin "
