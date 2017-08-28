GHC=~/.stack/programs/x86_64-osx/ghc-8.0.2/bin/ghc 

cabal:
	cabal sandbox init
	cabal install --enable-tests -w $(GHC)
	cabal configure -w $(GHC)
	cabal test

tags:
	hasktags -c src/
	hasktags -e src/
	hasktags -x -c src/
