# Reading and Auditing Path: $\Gamma$ / Logos 4

**A Guide for Analytic Metaphysicians, Mathematicians, and Logicians**

Welcome to **Logos 4**, a machine-checked, formal ontological deduction in the **Lean 4** kernel.
This document outlines the recommended sequence for reading, verifying, and auditing the repository.

---

## 1. Quick Navigation Matrix

Depending on your objective, follow one of these paths:

| Reader Profile | Recommended Starting Point | Primary Files | Approximate Time |
|---|---|---|---|
| **Executive / High-Level** | `README.md` | `README.md` | 5 minutes |
| **Interactive Terminal Auditor** | `lake exe logos` | `formal/Main.lean` | 2 minutes |
| **Analytic Philosopher / Theologian** | `investigations/` | `investigations/philosophical_foundations_free_personal_source.md` | 30 minutes |
| **Formal Logician / Lean 4 Specialist** | Unified Metatheorem & Modules | `OntologicalIncompletenessTheorem.lean` $\to$ `formal/Logos/*.lean` | 45 minutes |

---

## 2. Recommended Reading Sequence

### Step 1: The Canonical Argument Surface (`README.md`)
* **What it is:** The ~500-line, fully visible living deduction.
* **Key Focus Areas:**
  - The governing elimination question and thesis;
  - The native **Mermaid Architectural Flowchart**;
  - The **10-Step Deductive Chain** (plain English, skeptic objections, deductive replies, and formal anchors);
  - The **15 Derived Divine Characteristics** of `DivineReality`;
  - The **11 Canonical Cremations** of competing philosophies (C1–C11);
  - The **Headline Verified Theorems** table.

### Step 2: The Interactive Terminal Auditor (`make run` / `lake exe logos`)
* **What it is:** A fast, colorful CLI terminal visualizer built in pure Lean 4.
* **Usage:**
  ```sh
  cd formal && lake exe logos [OPTION]
  ```
  - `lake exe logos --steps` $\to$ Inspect only the 10 deductive steps;
  - `lake exe logos --attributes` $\to$ Inspect the 15 divine characteristics;
  - `lake exe logos --cremations` $\to$ Inspect the 11 philosophical cremations;
  - `lake exe logos --check` $\to$ Fast quiet verification.

### Step 3: The Unified Master Metatheorem (`OntologicalIncompletenessTheorem.lean`)
* **What it is:** The single top-level metatheorem in the repository root.
* **Core Theorem:**
  ```lean
  theorem ontological_incompleteness_master_metatheorem
      (S : ConcreteSystem.{0})
      (T : CandidateGround S)
      (hCont : ContingentSystem S)
      (hGrounds : T.GroundsConcreteActuality T.ground S.actualWorld)
      (hFPS : FreePersonalSource S T)
      (hCorr : TranscendentAgentialActionCorrespondence S T) :
      DivineReality S T ∧ (¬ ModalCollapse S)
  ```
  Synthesizes the entire argument in one verifiable statement: establishing the complete 15-characteristic `DivineReality` and strictly refuting van Inwagen's fatalistic modal collapse.

### Step 4: The Four Clean Modules (`formal/Logos/`)
The mathematical engine is partitioned into exactly four cleanly factored Lean 4 modules:

1. **`System.lean` (Structural Foundations & Impossibility Topologies):**
   - Formalizes atemporal constitutive priority as a strict, well-founded partial order (`prior_irrefl`).
   - Refutes internal closed cycles (`closed_cycle_violates_ontological_priority`) and infinite regress (`infinite_regress_cannot_self_ground`).
   - Proves the existence of an internal boundary node (`closed_system_has_unexplained_boundary`).
   - Strictly deduces that any ground of the totality must be structurally external (`candidate_ground_must_be_structurally_external`).

2. **`Elimination.lean` (Modal Contingency & Contrastive PSR):**
   - Formalizes possible worlds modal semantics (`World`, `Accessible`, `InstantiatedIn`).
   - Defines the `GeneralContrastivePSR` without baking necessity into the definition.
   - Refutes rigid impersonal necessitation (`necessary_ground_cannot_rigidly_necessitate_contingent_system`) and consequence-dependent circularity (`consequence_dependent_mode_fails_well_foundedness`).

3. **`Agency.lean` (Action Theory & Tier 1 Master Theorem):**
   - Connects modal contrast with intentional action theory (`SelectsIntentionally`).
   - Constructs positive libertarian freedom (`agential_freedom_derived` deriving `ActsFreely S T`).
   - Proves the **Tier 1 Master Eliminative Theorem** (`eliminative_existential_derives_unforced_personal_agent`).

4. **`Source.lean` (Transmission, Divine Reality, and the 11 Cremations):**
   - Formalizes explanatory transmission and concurrent causation (`ExplanatoryTransmission`).
   - Proves the **Tier 2** (`intermediate_existential_derives_unforced_personal_source`) and **Tier 3** (`eliminative_foundation_derives_free_personal_source_under_transmission`) master theorems.
   - Proves the **Master Characterization Theorem** (`free_personal_source_instantiates_divine_reality`).
   - Proves the **11 Canonical Cremations** (Normative Nihilism, Physicalism, Spinozism, Leibnizianism, Humean Brute Fact, Infinite Regress, Coherentism, Voluntarism, Unitarianism, Deism, Occasionalism).
   - Proves the resolution of the Omnipotence Paradox, *Ex Nihilo Nihil Fit*, the Argument from Reason, and *Creatio Continua*.

### Step 5: Philosophical Treatises (`investigations/`)
For deep philosophical analysis:
- `philosophical_foundations_free_personal_source.md`: Comprehensive 1,200-line analytical treatise.
- `comparative_divine_attributes_audit.md`: Systematic comparative audit of the 40 classical attributes from $\Gamma$.
- `trinitarian_plurality_and_divine_goodness.md`: Deep exploration of Aquinas vs. Richard of St. Victor on divine goodness and hypostatic plurality.
- `ledger.md`: Authoritative declaration-by-declaration audit trail with full ASCII flowchart.

---

## 3. How to Verify and Audit the Codebase

From the root of `logos4`:

```sh
# Full build, consistency check, footprint audit, and ledger generation:
make all

# Run automated regression test suite:
make test

# Launch the interactive terminal auditor:
make run

# Clean build cache and temporary artifacts:
make clean
```

All theorems are verified directly by the **Lean 4 kernel with 0 errors, 0 warnings, and 0 sorrys**.
