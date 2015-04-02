
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
	./configure
	cd external/ocamlgraph && ./configure && make clean && make && cd ../..
	cd external/fixpoint/ && make clean && make -e && cd ../..

binaries:
	vagrant up
	make ocaml
	cp external/fixpoint/fixpoint.native external/fixpoint/fixpoint.native-x86_64-darwin
	vagrant ssh -c "make -C /vagrant ocaml" 64
	cp external/fixpoint/fixpoint.native external/fixpoint/fixpoint.native-x86_64-linux
	vagrant ssh -c "make -C /vagrant ocaml" 32
	cp external/fixpoint/fixpoint.native external/fixpoint/fixpoint.native-i386-linux
	vagrant ssh -c "make -C /vagrant ocaml OCAMLLIB=/usr/i686-w64-mingw32/lib/ocaml/ OCAMLC=i686-w64-mingw32-ocamlc OCAMLOPT=i686-w64-mingw32-ocamlopt" 64
	cp external/fixpoint/fixpoint.native external/fixpoint/fixpoint.native-i686-w64-mingw32
	vagrant halt

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
	hasktags -e src/
