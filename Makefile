# Makefile — Build, audit, deduction generation, and verification pipeline for Γ / Logos.

SHELL := /bin/bash
export PATH := $(HOME)/.elan/bin:$(PATH)

PYTHON ?= python3

.PHONY: all build depviz audit stip stipdef sync taxonomy deduction test check clean zip help

# Default target runs the complete formal build, audit, deduction generation, and test verification.
all: build depviz audit stip stipdef census deduction test
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

# Verify the definitional-stipulation registry (Stipulations.lean) against the
# sources and the kernel graph, emitting formal/stipulation_audit.json (needs
# depgraph.json, hence runs after depviz).
stip: depviz
	@echo "=== Verifying definitional stipulation registry ==="
	$(PYTHON) scripts/audit_stipulations.py

# Enforce the ◈ discipline for `def`s used as premises (F-2, AsietyFreedom.md
# §0.5/§0.6.4). Needs formal/axiom_audit.json, hence runs after `audit`. FAILS on
# any asserted Prop used as a bare-name premise that has neither a Stipulations.lean
# entry nor an entry in scripts/stipulated_def_allowlist.json. Entries in that
# baseline are all reviewed:false -- they record INHERITED DEBT, so a passing run
# means "no NEW undisclosed bridge and the inherited set has not grown", never
# "the corpus is clean".
stipdef: audit
	@echo "=== Auditing asserted Props used as premises (F-2) ==="
	$(PYTHON) scripts/audit_stipulated_defs.py

# Two censuses, both of figures the prose quotes.
#
# (1) F15 multiplicity, quoted in SemanticFinitude.lean's justification,
# ClaimMeanings.lean, base.txt and theorems/T24.txt. FAILS if the figures those
# four files quote no longer match the kernel: a refactor that moves the bound
# would otherwise leave a stale "paid N times" in the axiom's own justification.
#
# (2) Inherited `def`-as-bridge debt (VISIBILITY.md Phase 7), quoted in the
# ledger's disclosure section and in README's score block. FAILS if the allowlist
# and the ledger disagree about which bridges are disclosed, or if the quoted
# totals drift -- the hand-written `gapmap` field of each entry is a maintained
# field asserting a fact, so the check derives it instead of trusting it.
census:
	@echo "=== Checking the F15 multiplicity census against the kernel ==="
	$(PYTHON) scripts/census_semantic_finitude.py --check
	@echo "=== Checking the inherited def-as-bridge census against the ledger ==="
	$(PYTHON) scripts/census_stipulated_defs.py --check

# Generate README.md and investigations/kernel-audit.md
deduction: audit depviz stip
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
	@echo "  audit      Audit transitive kernel footprints + docstring markers + GAPMAP taxonomy"
	@echo "  stip       Verify stipulation registry (audit_stipulations.py → stipulation_audit.json)"
	@echo "  stipdef    Enforce ◈ discipline for premise-defs (audit_stipulated_defs.py; F-2)"
	@echo "  taxonomy   Verify GAPMAP taxonomy tallies vs the kernel (scripts/gapmap_taxonomy.py --check)"
	@echo "  sync       Verify docstring footprint markers vs formal/axiom_audit.json only"
	@echo "  deduction  Compile README.md and investigations/kernel-audit.md"
	@echo "  test       Run verification test suites"
	@echo "  check      Alias for test"
	@echo "  clean      Clean Lake build artifacts and python cache"
	@echo "  zip        Package source code into zip archive via Makefile-zip"
	@echo "  help       Display this help message"
