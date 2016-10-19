include agda_stdlib.mk

LATEX=latexmk -pdf -use-make
MAIN=jcc
IDIR=code
LHSFILE=$(wildcard $(IDIR)/*.lagda)

all:
	for file in $(LHSFILE) ; do \
	    	agda --latex  $$file --include-path=$(AGDA_STDLIB) --include-path=$(IDIR) ; \
	done	
	$(LATEX) $(MAIN).tex

quick:
	$(LATEX) $(MAIN).tex

clean:
	rm -f *.aux *.out *.log *.dvi *.ps *.pdf *~ *.bbl *.blg *.toc *.tdo *.fdb_latexmk *.fls *.ptb *.nav *.snm *.vrb
	rm -f code/*.agdai
	rm -fr latex/
