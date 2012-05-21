TEXINPUTS=.:Styles//::
BSTINPUTS=.:Styles//::

TARGET=Theorems
STY = ndisplay.sty liquidHaskell.sty ngrammar.sty
TEX = rules.tex Theorems.tex preservation.tex progress.tex soundness.tex
BIB = myrefs
SRCFILES = Makefile  ${TEX} ${STY} ${BIB}.bib  

# make pdf by default
all: ${TARGET}.pdf

rules: rules.pdf

theorems: Theorems.pds

# it doesn't really need the .dvi, but this way all the refs are right
%.pdf : %.dvi
	pdflatex $*

#${TARGET}.bbl: paper.bib
# in case we don't already have a .aux file listing citations
# this should probably be a separate makefile target/dependency instead
# of doing it every time... but *shrug*
#	latex ${TARGET}.tex
# get the citations out of the bibliography
#	bibtex ${TARGET}
# do it again in case there are out-of-order cross-references
#	bibtex ${TARGET}
#	latex ${TARGET}.tex

#${TARGET}.dvi: ${TARGET}.bbl ${TARGET}.tex
%.dvi: %.tex
	@latex $*.tex

# shortcut, so we can say "make ps"
ps: ${TARGET}.ps

%.ps: %.dvi
	@dvips -t a4 $*.dvi

clean:
	$(RM) *.log *.aux *.ps *.dvi *.bbl *.blg *.bak *.fdb_latexmk *~

reallyclean: clean
	$(RM) *.ps *.pdf

distclean: reallyclean

pdfshow: $(TARGET).pdf
	xpdf $(TARGET).pdf

acroshow: $(TARGET).pdf
	acroread $(TARGET).pdf

pack: reallyclean
	tar cvfz liquidHaskell_tex.tar.gz ${SRCFILES}

PHONY : ps all clean reallyclean distclean
