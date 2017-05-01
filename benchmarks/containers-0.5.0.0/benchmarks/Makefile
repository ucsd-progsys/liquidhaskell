all:

bench-%: %.hs force
	ghc -O2 -DTESTING $< -i../$(TOP) -o $@ -outputdir tmp -rtsopts

bench-%.csv: bench-%
	./bench-$* -v -u bench-$*.csv

.PHONY: force clean veryclean
force:

clean:
	rm -rf tmp $(patsubst %.hs, bench-%, $(wildcard *.hs))

veryclean: clean
	rm -rf *.csv
