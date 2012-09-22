include ../../config.make

LIBS=-libs unix,str

IFLAGS=-lflags -I,$(OCAMLGRAPHHOME) 

CFLAGS=-cflags -dtypes \
       -cflags -I,$(OCAMLGRAPHHOME)

TARGETS=misc.cma misc.cmxa \
	bNstats.cma bNstats.cmxa \
	tagtime.cma tagtime.cmxa \
	timer.cma timer.cmxa \
	constants.cma constants.cmxa \
	fcommon.cma fcommon.cmxa \
	heaps.cma heaps.cmxa \
	errorline.cma errorline.cmxa # z3dummy.cma z3dummy.cmxa

all:
	ocamlbuild -r $(IFLAGS) $(CFLAGS) $(TARGETS)

clean:
	rm -rf *.byte *.native _build _log

test:
	ocamlbuild -r $(LIBS) $(IFLAGS) $(CFLAGS) -tags thread timetest.native
