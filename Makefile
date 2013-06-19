CURRENT=cpcf

default: $(CURRENT).tex
	rubber -d $(CURRENT).tex

show: $(CURRENT).pdf
	xdg-open $(CURRENT).pdf