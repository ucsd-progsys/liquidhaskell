PANDOC=pandoc --template=templates/default.latex 

lhsObjects  := $(wildcard src/*.lhs)

all: book
	$(PANDOC) dist/book.lhs -o dist/book.pdf

book: $(lhsObjects)
	cat $(lhsObjects) > dist/book.lhs

clean:
	rm -rf dist/*
