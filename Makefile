# Makefile — Build, verification, and audit pipeline for Logos 4

SHELL := /bin/bash
export PATH := $(HOME)/.elan/bin:$(PATH)
PYTHON ?= python3

.PHONY: all build cli run audit consistency deduction test clean help

# Default target: build Lean modules, verify consistency, run footprint audit, and generate deduction
all: build consistency audit deduction
	@echo ""
	@echo "================================================================================"
	@echo "  Logos 4 Pipeline: 100% Machine-Checked and Verified (0 errors)"
	@echo "================================================================================"

# Build the Lean 4 formalization in formal/
build:
	@echo "=== Building Lean 4 formal modules (formal/) ==="
	cd formal && lake build

# Run the interactive CLI visualizer
cli run: build
	@cd formal && lake exe logos

# Verify kernel consistency (ensures False is not derivable and axioms are bounded)
consistency:
	@echo "=== Running consistency guard ==="
	$(PYTHON) scripts/check_consistency.py

# Audit kernel axiom footprints (#print axioms)
audit: build
	@echo "=== Auditing kernel axiom footprints ==="
	$(PYTHON) scripts/audit_footprints.py

# Regenerate reader-facing deduction and ledger (README.md and investigations/ledger.md)
deduction: audit
	@echo "=== Generating canonical argument and audit ledger ==="
	$(PYTHON) scripts/build_deduction.py

# Run all verification checks
test: consistency audit deduction
	@echo "=== Running automated regression test suite ==="
	$(PYTHON) scripts/test_pipeline.py
	@echo "=== All tests passed successfully ==="

# Clean build artifacts
clean:
	@echo "=== Cleaning build artifacts ==="
	cd formal && lake clean
	rm -rf __pycache__ scripts/__pycache__

# Display help
help:
	@echo "Logos 4 Build System Commands:"
	@echo "  make all          - Run full verification pipeline (build, consistency, audit, deduction)"
	@echo "  make build        - Compile Lean 4 formalization with lake"
	@echo "  make run (or cli) - Launch the interactive CLI terminal auditor"
	@echo "  make consistency  - Check theoretical consistency and axiom bounds"
	@echo "  make audit        - Audit exact transitive axiom footprints"
	@echo "  make deduction    - Regenerate README.md and investigations/ledger.md"
	@echo "  make test         - Run all automated checks"
	@echo "  make clean        - Remove Lake build cache and Python artifacts"
