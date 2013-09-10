TARGET= main

TECH=main
URL=nvazou@goto.ucsd.edu:~/public_html/lazytechreport.pdf

STY = liquidHaskell.sty commands.sty
TEX = main.tex language.tex typeInference.tex 
BIB = sw.bib
CLS = sigplanconf.cls
SRCFILES = Makefile ${TEX} ${STY} ${CLS}


all: ${TEX}
	pdflatex main
	bibtex main
	pdflatex main
	bibtex main
	pdflatex main

tech: ${SRCFILES}
	cp $(SHOWPROOFS) $(PROOFCNF)
	pdflatex ${TECH}
	bibtex ${TECH}
	pdflatex ${TECH}
	bibtex ${TECH}
	pdflatex ${TECH}
	cp $(HIDEPROOFS) $(PROOFCNF)


uploadtech: ${TECH}.pdf
	scp ${TECH}.pdf ${URL}
withproofs:
	cp $(SHOWPROOFS) $(PROOFCNF)

noproofs:
	cp $(HIDEPROOFS) $(PROOFCNF)

clean:
	$(RM) *.log *.aux *.ps *.dvi *.bbl *.blg *.bak *.fdb_latexmk *.out *~ proofs/*.log

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
