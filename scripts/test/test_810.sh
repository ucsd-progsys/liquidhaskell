stack build --fast liquidhaskell:exe:liquid && stack test -j1 liquidhaskell:test --flag liquidhaskell:include --flag liquidhaskell:devel --ta="-p $1" --fast
