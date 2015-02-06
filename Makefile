
OPTS="-W -O2 -XStandaloneDeriving"
PROFOPTS="-O2 -rtsopts -prof -auto-all -caf-all -XStandaloneDeriving -XDeriveDataTypeable"

CABAL=cabal
CABALI=$(CABAL) install --ghc-options=$(OPTS)
CABALP=$(CABAL) install --ghc-options=$(OPTS) -p

DEPS=unix-compat transformers mtl filemanip text parsec ghc-paths deepseq comonad contravariant semigroupoids semigroups bifunctors hscolour ansi-terminal hashable unordered-containers

all:
	$(CABAL) install --ghc-options=$(OPTS) 

force:
	$(CABAL) install --force-reinstalls --ghc-options=$(OPTS) 

rebuild: ocaml
	make

ocaml:
	cd external/ocamlgraph && make clean && ./configure && make && cd ../..
	cd external/fixpoint/ && make clean && make -e && cd ../..

ocaml-windows:
	OCAMLLIB=/usr/i686-w64-mingw32/lib/ocaml/ OCAMLC=i686-w64-mingw32-ocamlc OCAMLOPT=i686-w64-mingw32-ocamlopt make ocaml	

igoto:
	$(CABAL) configure --ghc-options=$(OPTS) 

goto:
	$(CABAL) build --ghc-options=$(OPTS) 
	cp dist/build/liquid/liquid ~/.cabal/bin/

prof:
	$(CABAL) install --enable-executable-profiling --enable-library-profiling --ghc-options=$(PROFOPTS)

clean:
	cabal clean

docs:
	$(CABAL) haddock --executables --internal --hoogle --hyperlink-source #--html-location=http://goto.ucsd.edu/~rjhala/llvm-haskell/


deps:
	$(CABALI) $(DEPS)

pdeps:
	$(CABALP) $(DEPS)

lint:
	hlint --colour --report .

tags:
	hasktags -c src/
