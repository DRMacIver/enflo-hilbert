PYTHON ?= python3
LATEXMK ?= latexmk
# Fixed draft date, 2026-11-24 UTC; also fixes PDF metadata timestamps.
export SOURCE_DATE_EPOCH ?= 1795478400
export FORCE_SOURCE_DATE = 1
export PYTHONDONTWRITEBYTECODE = 1

.PHONY: help lean check pdf notes verify clean

help:
	@echo 'make lean    - check the Lean proofs (install dependencies first)'
	@echo 'make check   - run numerical identity checks; override PYTHON if needed'
	@echo 'make pdf     - build the committed standalone PDF'
	@echo 'make notes   - build the supplementary research notes'
	@echo 'make verify  - run lean, check, and pdf'
	@echo 'make clean   - remove generated build files'

lean:
	lake build

check:
	$(PYTHON) experiments/check_core.py

pdf:
	mkdir -p build/tex output/pdf
	cd tex && $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error -outdir=../build/tex refutation.tex
	cp build/tex/refutation.pdf output/pdf/refutation.pdf

notes:
	mkdir -p build/tex
	cd tex && $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error -outdir=../build/tex main.tex

verify: lean check pdf

clean:
	rm -rf build tex/build
