include config.make

##############################################################################
##############################################################################
##############################################################################

API=ghc-7.4.1
THREADS=1
GHC=$(GHCHOME)/ghc
GPG=$(GHCHOME)/ghc-pkg

OPTS="-W -O2 -XStandaloneDeriving -XDeriveDataTypeable"
PROFOPTS="-O2 -rtsopts -prof -auto-all -caf-all -XStandaloneDeriving -XDeriveDataTypeable"

#CABAL=cabal --with-ghc=$(GHC) 
CABAL=cabal

CABALI=$(CABAL) install --ghc-options=$(OPTS)
#CABALI=$(CABAL) install --force-reinstalls --reinstall --ghc-options=$(OPTS)
#CABALP=$(CABALI) -p

CABALP=$(CABAL) install --reinstall --ghc-options=$(OPTS) -p

DEPS=unix-compat transformers mtl filemanip text syb parsec ghc-paths deepseq comonad contravariant semigroupoids semigroups bifunctors hscolour ansi-terminal

all:
	$(CABAL) install --ghc-options=$(OPTS) 

rebuild:
	cd external/fixpoint/ && make clean && make && cd ../../
	make

igoto:
	$(CABAL) configure --ghc-options=$(OPTS) 

goto:
	$(CABAL) build --ghc-options=$(OPTS) 
	cp dist/build/liquid/liquid ~/.cabal/bin/

prof:
	$(CABAL) install --enable-executable-profiling --enable-library-profiling --ghc-options=$(PROFOPTS)


clean:
	cabal clean

vector:
	$(CABAL) install vector

ansi-terminal:
	$(CABAL) install ansi-terminal 


bytestring:
	$(CABAL) install bytestring 
	$(CABAL) install bytestring-lexing

hscolour:
	$(CABAL) install --with-ghc=$(GHC) hscolour 

hsannot:
	$(GHC) --make HsAnnot

dexpose:
	$(GPG) expose $(API)

docs:
	$(CABAL) hscolour
	$(CABAL) haddock --hoogle

deps:
	$(CABALI) $(DEPS)

pdeps:
	$(CABALP) $(DEPS)

test:
	cd tests && ./regrtest.py -t $(THREADS) && cd ../

lint:
	hlint --colour --report .
