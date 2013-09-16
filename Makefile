export TEXINPUTS := ./imgs:./pfsteps:${TEXINPUTS}
# export TEXINPUTS="./imgs:./pfsteps:${TEXINPUTS}"
CURRENT=paper
CONTENT=cpcf
LAYOUT=llncs

WGETDVANHORNBIB=curl -o dvanhorn.bib "http://www.citeulike.org/bibtex/user/dvanhorn?fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=comment:comment&fieldmap=booktitle:booktitle&fieldmap=abstract:x-abstract&fieldmap=pages:pages&volume:volume"

WGETIANJBIB=curl -o ianj.bib "http://www.citeulike.org/bibtex/user/ianjohnson?fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=comment:comment&fieldmap=booktitle:booktitle&fieldmap=abstract:x-abstract&fieldmap=pages:pages&volume:volume"

default: $(CURRENT)$(LAYOUT).tex bench-overview.tex
	rubber ${opts} -v -d $(CURRENT)$(LAYOUT).tex; ./bin/weasel-all

sigplan sig: $(CURRENT)sigplan.tex
	rubber ${opts} -v -d $(CURRENT)sigplan.tex

lncs: $(CURRENT)llncs.tex
	rubber ${opts} -v -d $(CURRENT)llncs.tex

bench-overview.tex: 
	racket bench-gen.rkt

show: $(CURRENT)$(LAYOUT).pdf
	xdg-open $(CURRENT)$(LAYOUT).pdf

showsig: $(CURRENT)sigplan.pdf
	xdg-open $(CURRENT)sigplan.pdf


getbib:
	$(WGETDVANHORNBIB)
	$(WGETIANJBIB)
	-bibclean dvanhorn.bib > dvh-bibliography.bib.clean
	-bibclean ianj.bib > ianj.bib.clean
	cat ianj.bib.clean dvh-bibliography.bib.clean > bibliography.bib

bibtex:
	bibtex $(CURRENT)$(LAYOUT)

edit:
	sex emacs $(CONTENT).tex

clean:
	rm -f $(CURRENT)$(LAYOUT).{dvi,ps,pdf,log,toc,blg,bbl,aux,rel} *.log *~ *.out reviews.txt
