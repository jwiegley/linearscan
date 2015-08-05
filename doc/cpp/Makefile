latexfile = linearscan
figures = 
TEX = pdflatex
LATEX_FILES = linearscan.tex
BIB_FILES = linearscan.bib
BIBLIOGRAPHIES = $(latexfile)
BIBLIOGRAPHIES_bbl = $(BIBLIOGRAPHIES:=.bbl)
BIBLIOGRAPHIES_aux = $(BIBLIOGRAPHIES:=.aux)
.PHONY : clean

# prevent make from deleting .aux files in the course of compilation
.PRECIOUS: %.aux %.bbl

default: $(latexfile).pdf

$(latexfile).pdf : $(figures) $(LATEX_FILES) $(BIBLIOGRAPHIES_bbl)
	while ($(TEX) $(latexfile) && \
	grep -q "Rerun to get" $(latexfile).log ) do true ; \
	done
	@ test -e $@

%.aux: $(LATEX_FILES) $(BIB_FILES)
	$(TEX) $(latexfile)

%.bbl : $(BIB_FILES) $(BIBLIOGRAPHIES_aux)
	bibtex $(@:.bbl=)

bib : $(BIBLIOGRAPHIES_bbl)

once : 
	$(TEX) $(latexfile) 

clean:
	rm -f *.aux *.bbl *.blg *.log *.dvi *.out *.idx *.bak *~ *.toc *.lof
	rm -f $(latexfile).pdf
