PANDOC=pandoc --chapters --latex-engine=pdflatex --template=templates/default.latex 
LHS2TEX=pandoc --from=markdown+lhs --to=latex --chapters

lhsObjects  := $(wildcard src/*.lhs)

texObjects  := $(patsubst %.lhs,%.tex,$(wildcard src/*.lhs))

book: templates/book.tex $(texObjects) 
	cp templates/book.tex dist/
	cp src/*.tex dist/
	cd dist/ && pdflatex book.tex && cd ..

src/%.tex: src/%.lhs
	-$(LHS2TEX) $? -o $@ 

pbook: $(lhsObjects)
	cat $(lhsObjects) > dist/pbook.lhs
	$(PANDOC) dist/pbook.lhs -o dist/pbook.pdf

clean:
	rm -rf dist/*
