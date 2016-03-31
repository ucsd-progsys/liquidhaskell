THREADS=1
SMTSOLVER=z3

FASTOPTS=-O0
DISTOPTS=-O2
PROFOPTS=-O2 --enable-library-profiling --enable-executable-profiling
LIQUIDOPTS=

CABAL=cabal
CABALI=$(CABAL) install
CABALP=$(CABAL) install --enable-library-profiling

# to deal with cabal sandboxes using dist/dist-sandbox-xxxxxx/build/test/test
# TASTY=find dist -type f -name test | head -n1
TASTY=./dist/build/test/test

DEPS=--dependencies-only

##############################################################################
##############################################################################
##############################################################################

fast:
	$(CABAL) install -fdevel $(FASTOPTS)

first:
	$(CABAL) install $(FASTOPTS) --only-dependencies --enable-tests --enable-benchmarks

dist:
	# $(CABAL) install $(DISTOPTS)
	$(CABAL) configure -fdevel --enable-tests --disable-library-profiling -O2
	$(CABAL) build
	
prof:
	$(CABAL) install $(PROFOPTS)

igotgoto:
	$(CABAL) build $(OPTS)
	cp dist/build/liquid/liquid ~/.cabal/bin/

clean:
	cabal clean

docs:
	$(CABAL) hscolour
	$(CABAL) haddock --hoogle

deps:
	$(CABALI) $(DEPS)

pdeps:
	$(CABALP) $(DEPS)

all-test-py:
	cd tests && ./regrtest.py -a -t $(THREADS) && cd ../

test-py:
	cd tests && ./regrtest.py -t $(THREADS) && cd ../

test:
	$(CABAL) configure -fdevel --enable-tests --disable-library-profiling -O2
	$(CABAL) build
	$(CABAL) exec $(TASTY) -- --smtsolver $(SMTSOLVER) --hide-successes --rerun-update -p 'Unit/' -j$(THREADS) +RTS -N$(THREADS) -RTS
	# $(CABAL) exec $(TASTY) -- --smtsolver $(SMTSOLVER) --liquid-opts='$(LIQUIDOPTS)' --hide-successes --rerun-update -p 'Unit/' -j$(THREADS) +RTS -N$(THREADS) -RTS

test710:
	$(CABAL) configure -fdevel --enable-tests --disable-library-profiling -O2
	$(CABAL) build
	$(TASTY) --smtsolver $(SMTSOLVER) --hide-successes --rerun-update -p 'Unit/' -j$(THREADS) +RTS -N$(THREADS) -RTS


retest:
	cabal configure -fdevel --enable-tests --disable-library-profiling -O2
	cabal build
	cabal exec $(TASTY) -- --smtsolver $(SMTSOLVER) --hide-successes --rerun-filter "exceptions,failures,new" --rerun-update -p 'Unit/' -j$(THREADS) +RTS -N$(THREADS) -RTS

all-test:
	cabal configure -fdevel --enable-tests --disable-library-profiling -O2
	cabal build
	cabal exec $(TASTY) -- --smtsolver $(SMTSOLVER) --hide-successes --rerun-update -j$(THREADS) +RTS -N$(THREADS) -RTS

all-test-710:
	cabal configure -fdevel --enable-tests --disable-library-profiling -O2
	cabal build
	$(TASTY) --smtsolver $(SMTSOLVER) --hide-successes --rerun-update -j$(THREADS) +RTS -N$(THREADS) -RTS



all-retest:
	cabal configure -fdevel --enable-tests --disable-library-profiling -O2
	cabal build
	cabal exec $(TASTY) -- --smtsolver $(SMTSOLVER) --hide-successes --rerun-filter "exceptions,failures,new" --rerun-update -j$(THREADS) +RTS -N$(THREADS) -RTS

all-retest-710:
	cabal configure -fdevel --enable-tests --disable-library-profiling -O2
	cabal build
	$(TASTY) --smtsolver $(SMTSOLVER) --hide-successes --rerun-filter "exceptions,failures,new" --rerun-update -j$(THREADS) +RTS -N$(THREADS) -RTS



lint:
	hlint --colour --report .

tags:
	hasktags -x -c src/
	# hasktags -c src/
	# hasktags -e src/

ghcid:
	ghcid --command "stack ghci --main-is liquidhaskell:exe:liquid"
