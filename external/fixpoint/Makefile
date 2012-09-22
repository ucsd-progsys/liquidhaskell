include ../../config.make

LIBS=-libs unix,str,z3,graph

DIRS=-I misc

IFLAGS=-lflags -I,$(OCAMLGRAPHHOME) \
       -lflags -I,$(Z3HOME)/lib \
       -lflags -I,$(Z3HOME)/ocaml 

LFLAGS=-lflags -cc,g++ \
       -lflags -cclib,-L$(OCAMLLIBHOME) \
       -lflags -cclib,-L$(Z3HOME)/lib \
       -lflags -cclib,-lz3 \
       -lflags -cclib,-lstdc++ \
       -lflags -cclib,-lz3stubs \
       -lflags -cclib,-lcamlidl \
			 -lflags -cclib,-fopenmp

CFLAGS=-cflags -dtypes,-annot \
       -cflags -I,$(Z3HOME)/ocaml \
       -cflags -I,$(OCAMLGRAPHHOME) \
			 -cflags -thread

OFLAGS=$(DIRS) $(IFLAGS) $(LFLAGS) $(CFLAGS)

all:
	ln -sf ../misc
	ocamlbuild -r $(LIBS) $(OFLAGS) -tags thread fixpoint.native
	ocamlbuild -r $(OFLAGS) fix.cmxa
	cp _build/fixpoint.native .

clean:
	rm -rf *.byte *.native _build _log
