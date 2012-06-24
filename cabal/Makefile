#BINPATH=/home/niki/src/ghc/bin
#BINPATH=/home/rjhala/research/ghc-working-local-new/bin
BINPATH=/usr/bin
API=ghc-7.4.1

##################################################

GHC=$(BINPATH)/ghc
GPG=$(BINPATH)/ghc-pkg

#OPTS="-XStandaloneDeriving -XDeriveDataTypeable"
OPTS="-O2 -XStandaloneDeriving -XDeriveDataTypeable"
PROFOPTS="-O2 -rtsopts -prof -auto-all -caf-all -XStandaloneDeriving -XDeriveDataTypeable"
CABAL=cabal --with-ghc=$(GHC) 
#CABAL=cabal --with-ghc=$(GHC) --enable-executable-profiling --enable-library-profiling --reinstall
CABALPROF= $(CABAL) install --reinstall --ghc-options=$(OPTS) -p 

all:
	$(CABAL) install --ghc-options=$(OPTS) 

prof:
	$(CABAL) install --enable-executable-profiling --enable-library-profiling --ghc-options=$(PROFOPTS)

oldschool:
	$(GHC) --make Liquid 

clean:
	cabal clean

dpackages:
	$(CABAL) install filemanip 
	$(CABAL) install transformers 
	$(CABAL) install cmdargs 
	$(CABAL) install deepseq
	$(CABAL) install transformers
	$(CABAL) install mtl
	$(CABAL) install parsec
	$(CABAL) install ghc-paths
	$(CABAL) install --ghc-options=$(OPTS) syb 
	$(CABAL) install --with-ghc=$(GHC) hscolour 
	$(CABAL) install vector

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

profdpackages:
	$(CABALPROF) unix-compat
	$(CABALPROF) transformers
	$(CABALPROF) mtl
	$(CABALPROF) filemanip
	$(CABALPROF) cmdargs
	$(CABALPROF) text
	$(CABALPROF) syb
	$(CABALPROF) comonad
	$(CABALPROF) contravariant
	$(CABALPROF) semigroupoids
	$(CABALPROF) semigroups
	$(CABALPROF) bifunctors
