# Architectural Audit & Consolidation Roadmap for Logos (Γ)

## 1. Executive Summary

With the successful verification and isolation of the master proof for the Free Subject in `best.lean` and `formal/Logos/CompleteLibertarianFreedomArgument.lean` (148 declarations, zero substantive axioms, standalone deductive pipeline), this document addresses code dispersion across the repository:
1. **Clean Workspace Hygiene:** Identification and cleanup of disposable scratch files created during the exploration of the freedom lemmas.
2. **Comprehensive Inventory:** Categorization of all 110 Lean modules in `formal/Logos/`.
3. **Coupling & Blast-Radius Analysis:** Identification of the automated gates, generation pipelines, and consistency guards that constrain module refactoring.
4. **Concrete Consolidation Roadmap:** A safe, phased architecture for consolidating the ~30 Divine Characteristics modules into unified files without breaking the repository's derivation surface.

---

## 2. Workspace Hygiene & Root Scratch Audit

### 2.1 Removed Scratch Test Files (Phase 1)
During the derivation of the final freedom lemmas in `best.lean`, multiple scratchpad files were created in the repository root to test candidate solvers and heterogeneous equality closers. These throwaway files have been removed:
- `test_cand_inr.lean`
- `test_cand_sol2_0.lean`
- `test_heq_close.lean`
- `test_inr_close.lean`
- `test_inr_close2.lean`
- `test_inr_sub_0.lean`
- `test_solve.py`
- Transient one-off build scripts in `scripts/`: `apply_clarity.py`, `build_clean_best.py`, `build_reorganized.py`, `refine_best.py`, `reorganize_clean.py`, `reorganize_file.py`.

### 2.2 Root Markdown Scratch Audit
The repository root contains several untracked markdown documents authored during prior exploratory phases:
1. **Purely Superseded Freedom Scratchpads:**
   - `DET.md` (15 KB): Authored 2026-10-06 to plan determination chains. Fully superseded by `DeterminationSystem` and `JudgmentDeterminationChain` in `best.lean`. Safe to remove or archive.
   - `FOUND.md` (23 KB): Authored 2026-10-06 to plan verdict-justification separation. Fully superseded by the finalized `best.lean`. Safe to remove or archive.
   - `PLAN.md` (10 KB): Authored for §XXIV impossibility retorsion in `best.lean`. Fully superseded. Safe to remove or archive.
   - `SEP.md` (16 KB): Authored 2026-10-06 for `GroundedJudgment`. Fully superseded by `best.lean`. Safe to remove or archive.
2. **Historical Milestone Documentation:**
   - `DISAMB.md` (9 KB): Documents the 2026-10-01 strict monotheism / numerical unitarianism disambiguation (C212 vs C320).
   - `LOVE-4.md` (50 KB): Documents the derivation of C587 in `NoMeanerNoFalsity.lean`.
   - `ISSUE_C_PLAN.md`, `ISSUE_J_PLAN.md`, `ISSUE_K_PLAN.md`: Strategic plans for retorsion, personhood polarity, and countermodel meaning-coherence.
   - `STUPID_SIMON_SAYS.md` (4 KB): Investigation notes on goal-audit performance.
- **Recommendation:** Purely superseded scratchpads (`DET.md`, `FOUND.md`, `PLAN.md`, `SEP.md`) can be relocated to `investigations/archived_plans/` or deleted, while historical milestones (`DISAMB.md`, `LOVE-4.md`, `ISSUE_*.md`) should be kept under `investigations/` to maintain clean repository root hygiene.

---

## 3. Comprehensive Inventory of formal/Logos/ (110 Modules)

The 110 Lean modules divide into 5 clear conceptual and functional categories:

### Category A: The Self-Contained Master Freedom Proof (1 module)
- `CompleteLibertarianFreedomArgument.lean` (mirrored standalone in `best.lean`):
  - 148 declarations, zero substantive axioms (`CL` only), 100% verified.
  - Establishes `ProofExists C → ∃ s : Subject, FreeSubject C s` directly from `JudgmentDeterminationChain`.
  - Self-contained: defines its own `Semantics`, `DeterminationSystem`, and the 10-step deductive pipeline.
  - Locked and completely untouched.

### Category B: Historical / Intermediate Freedom Routes (~35 modules)
These modules represent the earlier developmental steps, intermediate frontiers, and exploratory iterations to derive freedom before the unified determination chain was formulated:
- `Agency.lean` (contains core agential axioms: `Subject`, `Means`, `Initiates`, `State`, etc.)
- `Choice.lean` (contains `AxIntentionalChoice`, `AxActPolarity`)
- `Alternatives.lean`, `Initiation.lean`, `ActionChoiceDefinitions.lean`, `StrongActionChoice.lean`
- `NormativeTruth.lean`, `DirectNormativeFreeWill.lean`, `ConstitutiveNormativeFreeWill.lean`
- `IndubitableNormativeFreeWill.lean`, `UndeniableNormativeDerivation.lean`
- `AgencyFrontierAudit.lean`, `AgencyDeterminismConsequences.lean`, `ChoiceRepair.lean`
- `FreeWillIndependence.lean`, `FreeWillInvariance.lean`, `JointForcing.lean`, `WillIndividuationAudit.lean`
- `A14DerivationAudit.lean`, `A14SemanticAudit.lean`, `PostA14Frontier.lean`, `DefinitiveAgencyFrontier.lean`
- `CognitiveDiscrimination.lean`, `CognitiveToAgencyFrontier.lean`, `DeterministicReductioFrontier.lean`
- `ExecutiveDeliberativeFrontier.lean`, `DeepContrastiveFrontier.lean`, `ProofSpecificContrast.lean`
- `SubContrastFoundations.lean`, `ModalCreationAgency.lean`, `NonLibertarianCreation.lean`
- `AsieticChoice.lean`, `AsietyFreedom.lean`
*Status:* While philosophically superseded by `CompleteLibertarianFreedomArgument.lean`, several of these modules still supply foundational types (`Agency.lean` defines `Subject`) or are referenced by intermediate sections in `investigations/ledger.md`.

### Category C: Divine Characteristics & Classical Attributes (~30 modules)
These modules establish the 19 primary characteristics and 40 classical attributes of the Ultimate Ground:
- **Core Classical Attributes:**
  - `NecessityEternity.lean` (Necessity, Everlasting Eternity, Atemporality)
  - `CanonicalAseity.lean` (Aseity of the Ground)
  - `FoundationalUnicity.lean` (Foundational Unicity, Universal Modal Grounding, Structural Monotheism)
  - `Precedence.lean` (Precedence of the Ground to the Right/Wrong Distinction)
  - `DivineSimplicity.lean` & `CharacteristicClosure.lean` (Divine Simplicity)
  - `DivineTranscendence.lean` (Ontological Transcendence, Ground is not the Universe)
  - `DivineImmutability.lean` & `ImmutabilitySoleBearer.lean` (Divine Immutability, Transition Invariance)
  - `FoundationalOmnipresence.lean` (Foundational Omnipresence)
  - `DivinePureActuality.lean` (Divine Pure Actuality, Maximal Capacity)
  - `DivineOmniscience.lean` (Foundational Omniscience)
  - `DivineOmnipotence.lean` (Foundational Omnipotence)
- **Causal & Production Batches:**
  - `ThomisticAct.lean` (Produces relation, Love→Act bridge, Love→Production bridge)
  - `ProductionCountermodel.lean` (Production vs Form Satisfiability separation)
  - `CosmicExistence.lean` (Cosmic existence datum)
  - `SuccessionAudit.lean` & `SuccessionCountermodel.lean` (Disjointness from Succession)
- **Trinitarian & Personal Ground Attributes:**
  - `DivineAgape.lean` (Agape, Procession of Word, Procession of Spirit, Tripersonality)
  - `TrinitySeparations.lean` (Separation from Narcissism, Creature-Love, Attribute-Love, Binitarianism)
  - `TrinitarianPersonalGround.lean` (GroundByBeing, OneEssence, PersonalGround, Perichoresis)
  - `TrinitarianSubjectBridge.lean` (DivineSubjectRole, TrinitarianPersonalBridge)
  - `SinglePersonDenial.lean` (Refutation of single-person contingency argument)
  - `TwoNecessaryPersonalCentres.lean`, `GoodDenial.lean`, `SecondPersonGoodAttempt.lean`
  - `CharacteristicSoleBearer.lean` (Sole-bearer master theorem for 6 footprint characteristics)
  - `NecessaryKindAudit.lean` (The necessary kind and the profile of the second necessary being)
  - `LovesAsGround.lean` (GroundBearsGood relation)
  - `BoundedMeaning.lean`, `SemanticFinitude.lean` (Semantic finitude bound)

### Category D: Defeated Philosophies / The Cremation Suite (~12 modules)
These modules implement Section 13's machine-checked refutations and countermodel terminations:
- `MeaningRetorsion.lean` (Refutation of NoMeaning thesis)
- `NoMeanerNoFalsity.lean` (Unconditional refutation of meaninglessness and grounding of polarity)
- `BipolarityRetorsion.lean` (Refutation of ungrounded normativity)
- `DirectNormativeRetorsion.lean` (Direct retorsion on normative denial)
- `OughtRetorsion.lean` (Refutation of self-grounded ought and impersonal Platonism)
- `ProofPresentationRetorsion.lean` (Performative retorsion on proof criticism and machine checker separation)
- `HostileSemantics.lean` (Semantic defenses against nihilistic and relativistic countermodels)
- `DefinitionalMeaningRetorsion.lean`, `AdversarialReductioAudit.lean`, `NegativeRetorsionAudit.lean`

### Category E: Core Semantic Infrastructure & Utilities (~10 modules)
- `Core.lean`, `Semantics.lean`, `Entity.lean`, `Modal.lean`, `Person.lean`, `Order.lean`, `Value.lean`, `Plurality.lean`, `Love.lean`
- `Stipulations.lean` (Definitional stipulations registry)
- `ClaimMeanings.lean`, `CountermodelMeanings.lean` (Docstring and gloss registries)
- `RealityHookAudit.lean`, `MoralFrontierAudit.lean`, `PersonhoodOntologyAudit.lean`, `AxiomNegationAudit.lean`
- `EpistemicNecessity.lean`, `EpistemicPersonalGround.lean`

---

## 4. Coupling & Blast-Radius Analysis for Consolidation

Attempting to consolidate or merge modules without respecting the repository's automated infrastructure will trigger immediate gate failures. The critical integration couplings are:

### 4.1 Pinned Axiom Census (`scripts/check_consistency.py`)
- The repository enforces a hard pin of **EXACTLY 39 declared axioms**:
  `EXPECTED_AXIOM_STATEMENTS = 39` (18 VOCAB, 6 SEM, 13 META, 2 TRANS).
- Any axiom merged, moved, or deleted must preserve its exact docstring header (`Tag: VOCAB`, `Tag: SEM`, etc.).
- The axiom scanner uses whole-file tokenization (`lean_code_lines`) to skip block comments.

### 4.2 Negative-Compilation Consistency Guard (`formal/consistency/FalseNotDerivable.lean`)
- The consistency guard explicitly imports:
  ```lean
  import Logos.TrinitarianSubjectBridge
  import Logos.FoundationalUnicity
  ```
- If either file is renamed or merged, `FalseNotDerivable.lean` will fail with an import error, which `check_consistency.py` treats as an invalid test run.

### 4.3 Hand-Authored Declaration Lists in `scripts/build_deduction.py`
`scripts/build_deduction.py` contains 16 hand-authored lists of declaration identifiers that gate `README.md` and `investigations/ledger.md`:
1. `CLASSICAL_ATTRIBUTES` (40 attribute rows defining targets and anchors)
2. `PILLAR_ROWS` (7 philosophical pillars)
3. `ASIETY_FREEDOM_STEPS`
4. `SEMANTIC_FINITUDE_STEPS`
5. `LOVE_STEPS`
6. `TWO_KINDS_STEPS`
7. `MEANING_RETORSION_STEPS`
8. `PRECEDENCE_STEPS`
9. `TEMPORALITY_STEPS`
10. `SOLE_BEARER_STEPS`
11. `INHABITED_STEPS`
12. `SUCCESSION_AUDIT_STEPS`
13. `THOMISTIC_ACT_STEPS`
14. `ACT_CASCADE_STEPS`
15. `CHARACTERISTIC_CLOSURE_STEPS`
16. `NECESSARY_KIND_AUDIT_STEPS`
Each item in these lists references a fully-qualified Lean declaration name (e.g. `Logos.FoundationalUnicity.ofGround_foundational_unicity`).
**Crucial Invariant:** Merging files must preserve the exact declaration namespaces (e.g. by using `namespace Logos.FoundationalUnicity ... end Logos.FoundationalUnicity` within consolidated files), otherwise every step in these 16 lists will fail to resolve.

### 4.4 Ledger Mapping & Claim Indexing (`formal/GAPMAP.md`)
- `formal/GAPMAP.md` indexes every claim (C1–C590+) with its declaration and file provenance.
- `scripts/test_deduction_dependencies.py` runs `test_claim_kernel_existence_walk`, verifying that all 442 `PROVEN` / `PROVEN↑` rows resolve to live kernel declarations.

### 4.5 Dependency Graph (`formal/depgraph.json`)
- Generated via `lake exe depviz --roots Logos`.
- Downstream audits (`audit_footprints.py`, `audit_goals.py`) depend on `depgraph.json`. Moving declarations between modules alters module nodes and transitive import edges.

---

## 5. Concrete Consolidation Roadmap

To reduce code dispersion while strictly preserving mathematical validity and pipeline integrity:

### Phase A: Workspace Cleanliness (Executed)
- Transient test files deleted from root (`test_cand_*.lean`, `test_inr_*.lean`, `test_solve.py`, etc.).
- Superseded root scratchpads (`DET.md`, `FOUND.md`, `PLAN.md`, `SEP.md`) documented and ready for archiving.
- Working tree clean.

### Phase B: Recommended Grouping Strategy for Divine Characteristics
Rather than a single unmaintainable 15,000-line monolithic file (which breaks Lean's multi-core parallel replay and incremental build times), consolidate the ~30 characteristics modules into **three thematic aggregate modules**:
1. `formal/Logos/DivineClassicalAttributes.lean`:
   - Consolidates: `NecessityEternity`, `CanonicalAseity`, `FoundationalUnicity`, `Precedence`, `DivineSimplicity`, `DivineTranscendence`, `DivineImmutability`, `FoundationalOmnipresence`, `DivinePureActuality`, `DivineOmniscience`, `DivineOmnipotence`, `CharacteristicSoleBearer`, `CharacteristicClosure`, `ImmutabilitySoleBearer`, `SuccessionAudit`, `SuccessionCountermodel`.
2. `formal/Logos/DivineTrinitarianAttributes.lean`:
   - Consolidates: `DivineAgape`, `TrinitySeparations`, `TrinitarianPersonalGround`, `TrinitarianSubjectBridge`, `SinglePersonDenial`, `TwoNecessaryPersonalCentres`, `GoodDenial`, `SecondPersonGoodAttempt`, `LovesAsGround`.
3. `formal/Logos/DivineThomisticProduction.lean`:
   - Consolidates: `ThomisticAct`, `ProductionCountermodel`, `CosmicExistence`, `NecessaryKindAudit`.

### Phase C: Exact Step-by-Step Migration Protocol
For each consolidated batch:
1. Wrap each constituent section in its historical namespace (e.g. `namespace Logos.FoundationalUnicity ... end Logos.FoundationalUnicity`) to maintain 100% backward compatibility for all 16 `build_deduction.py` declaration lists.
2. Ensure all 39 declared axioms maintain their exact docstrings, tags (`Tag: VOCAB`, `Tag: META`), and syntax.
3. Update imports in `formal/Logos.lean` and `formal/consistency/FalseNotDerivable.lean`.
4. Rebuild kernel: `cd formal && lake build`.
5. Re-run dependency and audit pipeline:
   ```sh
   cd formal && lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot
   cd .. && python3 scripts/audit_footprints.py && python3 scripts/audit_goals.py
   python3 scripts/build_deduction.py
   ```
6. Run all test gates:
   ```sh
   python3 scripts/check_consistency.py
   python3 scripts/test_axiom_census.py
   python3 scripts/sync_docstring_footprints.py
   python3 scripts/test_deduction_dependencies.py
   python3 scripts/test_argument_surface.py
   python3 scripts/test_no_linearity.py best.lean
   python3 scripts/test_best_standalone.py best.lean
   ```
