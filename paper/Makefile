SHELL := /bin/sh
OUT := ../output/pdf

.PHONY: all clean
all:
	mkdir -p $(OUT)
	latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=$(OUT) blowup_density.tex

clean:
	latexmk -c -outdir=$(OUT) blowup_density.tex
