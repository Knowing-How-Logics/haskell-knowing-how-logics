.PHONY: all build run test clean

TEXDIR=tex
MAIN=KHora

all: $(TEXDIR)/$(MAIN).pdf build

$(TEXDIR)/$(MAIN).pdf: $(TEXDIR)/*.tex $(TEXDIR)/*.bib lib/*.lhs test/*.lhs exec/*.lhs
	latexmk -pdf -output-directory=$(TEXDIR) -interaction=nonstopmode $(TEXDIR)/$(MAIN).tex

build:
	stack build

run:
	stack build && stack run

test:
	stack test --coverage

clean:
	stack clean
	rm -f $(TEXDIR)/*.aux $(TEXDIR)/*.log $(TEXDIR)/*.out $(TEXDIR)/*.snm $(TEXDIR)/*.toc $(TEXDIR)/*.vrb $(TEXDIR)/*.nav $(TEXDIR)/*.synctex.gz $(TEXDIR)/*.blg $(TEXDIR)/*.bbl $(TEXDIR)/*.fdb_latexmk $(TEXDIR)/*.fls $(TEXDIR)/*.ind $(TEXDIR)/*.idx $(TEXDIR)/*.ilg $(TEXDIR)/*.bcf $(TEXDIR)/*.run.xml $(TEXDIR)/*.xdv
