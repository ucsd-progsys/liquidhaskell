PANDOC=pandoc --columns=80  -s --mathjax --slide-level=2
SLIDY=$(PANDOC) -t slidy
DZSLIDES=$(PANDOC) --highlight-style tango --css=slides.css -w dzslides
HANDOUT=$(PANDOC) --highlight-style tango --css=text.css -w html5
WEBTEX=$(PANDOC) -s --webtex -i -t slidy
BEAMER=pandoc -t beamer
LIQUID=liquid

objects := $(patsubst %.lhs,%.lhs.slides.html,$(wildcard lhs/*.lhs))

####################################################################

all: slides copy

slides: $(objects)

lhs/%.lhs.markdown: lhs/%.lhs
	-$(LIQUID) $?

lhs/%.lhs.slides.html: lhs/%.lhs.markdown
	$(DZSLIDES) $? -o $@ 

copy:
	cp lhs/*lhs.html html/
	cp lhs/*lhs.slides.html html/
	cp css/*.css html/
	cp -r fonts html/
 
clean:
	cd lhs/ && ../cleanup && cd ../
	cd html/ && rm -rf * && cd ../

upload: 
	scp -r html/* rjhala@goto.ucsd.edu:~/public_html/liquid/haskell/tutorial/
