LATEXMK ?= latexmk
DOCKER_IMAGE ?= texlive/texlive:latest
SECTIONS := $(wildcard sections/*.tex)

LATEXMK_ARGS := -pdf -interaction=nonstopmode -halt-on-error main.tex

.PHONY: all clean

all: main.pdf

main.pdf: main.tex references.bib $(SECTIONS)
ifneq (,$(shell command -v $(LATEXMK)))
	$(LATEXMK) $(LATEXMK_ARGS)
else
	docker run --rm -v "$(CURDIR)":/work -w /work $(DOCKER_IMAGE) \
	  latexmk $(LATEXMK_ARGS)
endif

clean:
ifneq (,$(shell command -v $(LATEXMK)))
	$(LATEXMK) -C main.tex
else
	docker run --rm -v "$(CURDIR)":/work -w /work $(DOCKER_IMAGE) \
	  latexmk -C main.tex
endif
