LATEXMK ?= latexmk
SECTIONS := $(wildcard sections/*.tex)

.PHONY: all clean

all: main.pdf

main.pdf: main.tex references.bib $(SECTIONS)
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error main.tex

clean:
	$(LATEXMK) -C main.tex
