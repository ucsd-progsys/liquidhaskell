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
CABAL=cabal --with-ghc=$(GHC) 

CABALI=$(CABAL) install --force-reinstalls --reinstall --ghc-options=$(OPTS)
#CABALP=$(CABALI) -p

CABALP=$(CABAL) install --reinstall --ghc-options=$(OPTS) -p

DEPS=unix-compat transformers mtl filemanip cmdargs text syb parsec ghc-paths deepseq comonad contravariant semigroupoids semigroups bifunctors hscolour

all:
	$(CABAL) install --ghc-options=$(OPTS) 

prof:
	$(CABAL) install --enable-executable-profiling --enable-library-profiling --ghc-options=$(PROFOPTS)

oldschool:
	$(GHC) --make Liquid 

clean:
	cabal clean

vector:
	$(CABAL) install vector

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
