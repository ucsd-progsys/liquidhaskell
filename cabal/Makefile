BINPATH=/home/rjhala/research/ghc-working-local-new/bin
API=ghc-7.4.1

##################################################

GHC=$(BINPATH)/ghc
GPG=$(BINPATH)/ghc-pkg
OPTS="-O2 -XStandaloneDeriving -XDeriveDataTypeable"
PROFOPTS="-O2 -rtsopts -prof -auto-all -caf-all -XStandaloneDeriving -XDeriveDataTypeable"
CABAL=cabal --with-ghc=$(GHC) 

#CABAL=cabal --with-ghc=$(GHC) --enable-executable-profiling --enable-library-profiling --reinstall

all:
	$(CABAL) install --ghc-options=$(OPTS) 

prof:
	$(CABAL) install --enable-executable-profiling --enable-library-profiling --ghc-options=$(PROFOPTS)

oldschool:
	$(GHC) --make Liquid 

clean:
	cabal clean

dpackages:
	$(CABAL) install deepseq
	$(CABAL) install transformers
	$(CABAL) install mtl
	$(CABAL) install parsec
	$(CABAL) install ghc-paths
	$(CABAL) install --ghc-options=$(OPTS) syb 
	$(CABAL) install --with-ghc=$(GHC) hscolour 

vector:
	$(CABAL) install vector-0.7.0.1

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
