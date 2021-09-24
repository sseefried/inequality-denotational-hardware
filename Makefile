PAPER=inequality

all: latex/$(PAPER).pdf

AGDA_DEPENDENCIES:=$(patsubst %,latex/%.tex,$(MODULES))
.SECONDARY: $(AGDA_DEPENDENCIES)

LATEX_DEPENDENCIES:= \
  latex/bib.bib \
  latex/macros.tex \
  latex/unicode.tex \
  latex/commands.tex \
  $(AGDA_DEPENDENCIES)

latex/%.pdf: $(LATEX_DEPENDENCIES) latex/%.tex
	cd latex && latexmk -xelatex -bibtex $*.tex
	@touch $@
