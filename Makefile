#include config.make

#SERVERHOME=$(ROOTHOME)/_site/
SERVERHOME=/home/rjhala/public_html/liquid/haskell/demo
##############################################################################
##############################################################################
##############################################################################

API=ghc-7.4.1
THREADS=1
GHC=$(GHCHOME)/ghc
GPG=$(GHCHOME)/ghc-pkg

#OPTS="-W -O2 -XStandaloneDeriving -XDeriveDataTypeable"

FOPTS=""
OPTS="-W -O2 -XStandaloneDeriving"
PROFOPTS="-O2 -rtsopts -prof -auto-all -caf-all -XStandaloneDeriving -XDeriveDataTypeable"

CABAL=cabal -j
CABALI=$(CABAL) install --ghc-options=$(OPTS)
CABALP=$(CABAL) install --ghc-options=$(OPTS) -p

DEPS=unix-compat transformers mtl filemanip text parsec ghc-paths deepseq comonad contravariant semigroupoids semigroups bifunctors hscolour ansi-terminal hashable unordered-containers

all:
	$(CABAL) install --ghc-options=$(OPTS) 

fast: 
	$(CABAL) build 

prof:
	$(CABAL) install --enable-executable-profiling --enable-library-profiling --ghc-options=$(PROFOPTS) 

rebuild:
	cd external/fixpoint/ && make clean && make && cd ../../
	make

site: all web
	cp dist_liquid/build/liquid/liquid $(SERVERHOME)/liquid
	cp -rf external $(SERVERHOME)/
	cp -rf include $(SERVERHOME)/
	cp -rf syntax $(SERVERHOME)/

web:
	cp -rf web/* $(SERVERHOME)/


siteperms:
	sudo chgrp -R www-data $(SERVERHOME)
	sudo chmod -R g+rx $(SERVERHOME)
	sudo chmod    g+rwx $(SERVERHOME)/
	sudo chmod -R g+rwx $(SERVERHOME)/include/
	sudo chmod -R g+rwx $(SERVERHOME)/saved/

igoto:
	$(CABAL) configure --ghc-options=$(OPTS) 

goto:
	$(CABAL) build --ghc-options=$(OPTS) 
	cp dist/build/liquid/liquid ~/.cabal/bin/


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

all-test:
	cd tests && ./regrtest.py -a -t $(THREADS) && cd ../

test:
	cd tests && ./regrtest.py -t $(THREADS) && cd ../

lint:
	hlint --colour --report .
