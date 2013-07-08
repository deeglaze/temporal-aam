export TEXINPUTS := ./imgs:${TEXINPUTS}
CURRENT=cpcf

WGETDVANHORNBIB=curl -o dvanhorn.bib "http://www.citeulike.org/bibtex/user/dvanhorn?fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=comment:comment&fieldmap=booktitle:booktitle&fieldmap=abstract:x-abstract&fieldmap=pages:pages&volume:volume"

WGETIANJBIB=curl -o ianj.bib "http://www.citeulike.org/bibtex/user/ianjohnson?fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=comment:comment&fieldmap=booktitle:booktitle&fieldmap=abstract:x-abstract&fieldmap=pages:pages&volume:volume"

default: $(CURRENT).tex
	rubber ${opts} -v -d $(CURRENT).tex

show: $(CURRENT).pdf
	xdg-open $(CURRENT).pdf

getbib:
	$(WGETDVANHORNBIB)
	$(WGETIANJBIB)
	-bibclean dvanhorn.bib > dvh-bibliography.bib.clean
	-bibclean ianj.bib > ianj.bib.clean
	cat ianj.bib.clean dvh-bibliography.bib.clean > bibliography.bib

bibtex:
	bibtex $(CURRENT)

edit:
	sex emacs $(CURRENT).tex

clean:
	rm -f $(CURRENT).{dvi,ps,pdf,log,toc,blg,bbl,aux,rel} *.log *~ *.out reviews.txt
