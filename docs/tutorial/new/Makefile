####################################################################
SERVERHOME=nvazou@goto.ucsd.edu:~/public_html/liquidtutorial/
####################################################################


PANDOC=pandoc --columns=80  -s --mathjax --slide-level=2
SLIDY=$(PANDOC) -t slidy
REVEAL=$(PANDOC) -t revealjs -V revealjs-url=../reveal.js -V theme=serif
DZSLIDES=$(PANDOC) --highlight-style tango --css=slides.css -w dzslides
HANDOUT=$(PANDOC) --highlight-style tango --css=text.css -w html5
WEBTEX=$(PANDOC) -s --webtex -i -t slidy
BEAMER=pandoc -t beamer
LIQUID=liquid

mdObjects   := $(patsubst %.lhs,%.lhs.markdown,$(wildcard lhs/*.lhs))
htmlObjects := $(patsubst %.lhs,%.lhs.slides.html,$(wildcard lhs/*.lhs))

####################################################################

tut: $(mdObjects)
	$(REVEAL) lhs/*.markdown > tutorial.html 

all: slides copy

slides: $(objects)

lhs/%.lhs.markdown: lhs/%.lhs
	-$(LIQUID) $?

lhs/%.lhs.slides.html: lhs/%.lhs.markdown
	$(REVEAL) $? -o $@ 

lhs/%.lhs.slides.pdf: lhs/%.lhs.markdown
	$(BEAMER) $? -o $@ 

foo:
	$(LIQUID) lhs/Foo.lhs
	$(REVEAL) lhs/Foo.lhs.markdown -o lhs/Foo.lhs.html

copy:
	cp lhs/*lhs.html html/
	cp lhs/*lhs.slides.html html/
	cp css/*.css html/
	cp -r fonts html/
	cp index.html html/
	cp Benchmarks.html html/

clean:
#	cd lhs/ && ../cleanup && cd ../
#	cd html/ && rm -rf * && cd ../
#	cp index.html html/

upload: 
	scp -r html/* $(SERVERHOME)
