# Makefile — Build, audit, deduction generation, and verification pipeline for Γ / Logos.

SHELL := /bin/bash
export PATH := $(HOME)/.elan/bin:$(PATH)

PYTHON ?= python3

.PHONY: all build depviz audit sync taxonomy deduction test check clean zip help

# Default target runs the complete formal build, audit, deduction generation, and test verification.
all: build depviz audit deduction test
	@echo "=== Γ / Logos: Full build and verification pipeline complete (0 errors) ==="

# Build the formal Lean 4 library in formal/
build:
	@echo "=== Building Lean 4 formal library in formal/ ==="
	cd formal && lake build

# Generate kernel dependency graph (depgraph.json and depgraph.dot) via LeanDepViz
depviz: build
	@echo "=== Generating kernel dependency graph via LeanDepViz ==="
	cd formal && lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot

# Audit transitive kernel axiom footprints (#print axioms), then verify that
# every docstring Footprint marker / inline footprint copy matches the audit
# (sync needs axiom_audit.json, hence it runs after audit_footprints.py).
audit: build
	@echo "=== Auditing kernel axiom footprints ==="
	$(PYTHON) scripts/audit_footprints.py
	@echo "=== Verifying docstring footprint markers vs formal/axiom_audit.json ==="
	$(PYTHON) scripts/sync_docstring_footprints.py
	@$(MAKE) --no-print-directory taxonomy

# Verify that GAPMAP.md's hand-written taxonomy tallies (the corpus's last
# status-like numbers) still match the kernel; needs axiom_audit.json.
taxonomy:
	@echo "=== Verifying GAPMAP taxonomy tallies vs the kernel ==="
	$(PYTHON) scripts/gapmap_taxonomy.py --check

# Standalone convenience: verify docstring footprint markers against a
# pre-existing formal/axiom_audit.json (run scripts/audit_footprints.py first).
sync:
	@echo "=== Verifying docstring footprint markers vs formal/axiom_audit.json ==="
	$(PYTHON) scripts/sync_docstring_footprints.py

# Generate README.md and investigations/kernel-audit.md
deduction: audit depviz
	@echo "=== Compiling README.md and investigations/kernel-audit.md ==="
	$(PYTHON) scripts/build_deduction.py

# Run test suites: dependency correspondence and compiler genericity/provenance/sensitivity
test: deduction
	@echo "=== Running dependency correspondence and sensitivity tests ==="
	$(PYTHON) scripts/test_deduction_dependencies.py
	@echo "=== Running compiler genericity, provenance, and sensitivity tests ==="
	$(PYTHON) scripts/test_deduction_compiler.py

# Quick alias for running tests
check: test

# Clean Lake build cache and python bytecode cache
clean:
	@echo "=== Cleaning build artifacts ==="
	cd formal && lake clean
	find . -type d -name "__pycache__" -exec rm -rf {} +
	find . -name "*.pyc" -delete

# Package source code via dedicated packaging makefile
zip:
	@echo "=== Packaging source code via Makefile-zip ==="
	$(MAKE) -f Makefile-zip zip

help:
	@echo "Γ / Logos Build System"
	@echo ""
	@echo "Targets:"
	@echo "  all        Run full pipeline: build, depviz, audit, deduction, test (default)"
	@echo "  build      Build Lean 4 library in formal/ via lake build"
	@echo "  depviz     Generate formal/depgraph.json and formal/depgraph.dot"
	@echo "  audit      Audit transitive kernel footprints via scripts/audit_footprints.py + verify docstring footprint markers (scripts/sync_docstring_footprints.py) + GAPMAP taxonomy tally (scripts/gapmap_taxonomy.py --check)"
	@echo "  taxonomy   Verify GAPMAP taxonomy tallies vs the kernel (scripts/gapmap_taxonomy.py --check)"
	@echo "  sync       Verify docstring footprint markers vs formal/axiom_audit.json only"
	@echo "  deduction  Compile README.md and investigations/kernel-audit.md"
	@echo "  test       Run verification test suites"
	@echo "  check      Alias for test"
	@echo "  clean      Clean Lake build artifacts and python cache"
	@echo "  zip        Package source code into zip archive via Makefile-zip"
	@echo "  help       Display this help message"
