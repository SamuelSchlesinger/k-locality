.DEFAULT_GOAL := help

PYTHON ?= python3
LAKE ?= lake
LATEXMK ?= latexmk
SAGE ?= sage
SAGE_STATE_DIR ?= $(CURDIR)/output/sage
PDF_DIR := output/pdf
LATEX_FLAGS := -pdf -interaction=nonstopmode -halt-on-error -outdir=$(PDF_DIR)

.PHONY: help all check check-source check-lean check-finite check-sage paper notes archive

help:
	@printf '%s\n' \
	  'make check         Source/manifest checks, Lean build and axiom audit, finite validators' \
	  'make paper         Build output/pdf/main.pdf and check the TeX log' \
	  'make notes         Build output/pdf/explicit-lower-bounds.pdf and check the TeX log' \
	  'make all           Run check, paper, and notes' \
	  'make check-source  Check theorem coverage, links, imports, and proof placeholders' \
	  'make check-lean    Build Lean and run the axiom and executable identity checks' \
	  'make check-finite  Run the seven standard-library Python validators' \
	  'make check-sage    Run optional seeded block-parity experiments (requires SageMath)' \
	  'make archive       Build the historical counterexample writeup'

all: check paper notes

check: check-source check-lean check-finite

check-source:
	$(PYTHON) scripts/check_repository.py
	$(PYTHON) -m unittest discover -s tests -v

check-lean:
	$(LAKE) build -KwarningAsError=true
	$(LAKE) env lean -DwarningAsError=true scripts/check_axioms.lean
	$(LAKE) env lean -DwarningAsError=true research/check_universal_marginal.lean

check-finite:
	PYTHONOPTIMIZE=0 $(PYTHON) research/validate_robust_parity.py
	PYTHONOPTIMIZE=0 $(PYTHON) research/generate_sextic_matching.py --check
	PYTHONOPTIMIZE=0 $(PYTHON) research/literature-transfer/quadratization/data/validate_block_lift.py
	PYTHONOPTIMIZE=0 $(PYTHON) research/literature-transfer/rbm/data/check_bounds.py
	PYTHONOPTIMIZE=0 $(PYTHON) research/literature-transfer/flagship-routes/data/validate_eisenstein_radial.py
	PYTHONOPTIMIZE=0 $(PYTHON) research/literature-transfer/flagship-routes/data/validate_selector_block_layers.py
	PYTHONOPTIMIZE=0 $(PYTHON) research/literature-transfer/flagship-routes/data/validate_full_support_recognition_reduction.py

check-sage:
	mkdir -p "$(SAGE_STATE_DIR)"
	$(SAGE) --version
	DOT_SAGE="$(SAGE_STATE_DIR)" $(SAGE) -python research/analyze_block_parity_fiber.py --prefix-bits 2 --seed 0
	DOT_SAGE="$(SAGE_STATE_DIR)" $(SAGE) -python research/analyze_block_parity_fiber.py --prefix-bits 3 --samples 280 --seed 0

paper:
	mkdir -p $(PDF_DIR)
	$(LATEXMK) $(LATEX_FLAGS) main.tex
	$(PYTHON) scripts/check_repository.py --tex-log $(PDF_DIR)/main.log

notes:
	mkdir -p $(PDF_DIR)
	$(LATEXMK) $(LATEX_FLAGS) notes/explicit-lower-bounds.tex
	$(PYTHON) scripts/check_repository.py --tex-log $(PDF_DIR)/explicit-lower-bounds.log

archive:
	mkdir -p $(PDF_DIR)
	$(LATEXMK) $(LATEX_FLAGS) research/archive/interior-feasibility.tex
