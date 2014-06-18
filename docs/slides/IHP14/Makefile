####################################################################
SERVERHOME=nvazou@goto.ucsd.edu:~/public_html/liquidtutorial/
RJSERVER=rjhala@goto.ucsd.edu:~/public_html/liquid/haskell/plpv/lhs/
####################################################################

# REVEAL=$(PANDOC) -t revealjs -V revealjs-url=../_support/reveal -V theme=serif

REVEAL=pandoc \
	   --from=markdown+simple_tables 		\
	   --to=html5                           \
	   --standalone                         \
	   --mathjax \
	   --section-divs                       \
	   --template=_support/template.reveal  \
	   --variable reveal=../_support/reveal

PANDOC=pandoc --columns=80  -s --mathjax --slide-level=2
SLIDY=$(PANDOC) -t slidy
DZSLIDES=$(PANDOC) --highlight-style tango --css=slides.css -w dzslides
HANDOUT=$(PANDOC) --highlight-style tango --css=text.css -w html5
WEBTEX=$(PANDOC) -s --webtex -i -t slidy
BEAMER=pandoc -t beamer
LIQUID=liquid --short-names 

mdObjects   := $(patsubst %.lhs,%.lhs.markdown,$(wildcard lhs/*.lhs))
htmlObjects := $(patsubst %.lhs,%.lhs.slides.html,$(wildcard lhs/*.lhs))
pdfObjects  := $(patsubst %.lhs,%.lhs.slides.pdf,$(wildcard lhs/*.lhs))

####################################################################

pdfOne: lhs/00_Index.lhs.slides.pdf

all: slides 

one: $(mdObjects)
	$(REVEAL) lhs/.liquid/00_Index.lhs.markdown > lhs/index.html

tut: $(mdObjects)
	$(REVEAL) lhs/.liquid/*.markdown > lhs/tutorial.html 


slides: $(htmlObjects)


pdfslides: $(pdfObjects)

plpv: slides
	scp lhs/*.html $(RJSERVER)

lhs/.liquid/%.lhs.markdown: lhs/%.lhs
	-$(LIQUID) $?

lhs/%.lhs.slides.html: lhs/.liquid/%.lhs.markdown
	$(REVEAL) $? -o $@ 

lhs/%.lhs.slides.pdf: lhs/.liquid/%.lhs.markdown
	$(BEAMER) $? -o $@


copy:
	cp lhs/*lhs.html html/
	cp lhs/*lhs.slides.html html/
	cp css/*.css html/
	cp -r fonts html/
	cp index.html html/
	cp Benchmarks.html html/

clean:
	cd lhs/ && ../cleanup && cd ../
#	cd html/ && rm -rf * && cd ../
#	cp index.html html/

upload: 
	scp -r html/* $(SERVERHOME)
