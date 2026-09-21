SHELL := /bin/sh
OUT := ../output/pdf

.PHONY: all readers clean
all: readers

readers:
	mkdir -p $(OUT)
	cd revised && latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=../../output/pdf blowup_density_revised.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=$(OUT) formalization_guide.tex
	python3 ../experiments/check_reader_documents.py

clean:
	cd revised && latexmk -c -outdir=../../output/pdf blowup_density_revised.tex
	latexmk -c -outdir=$(OUT) formalization_guide.tex
