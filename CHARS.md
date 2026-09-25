# CHARS.md — Characteristics Formalization Roadmap

> ⚠️ **HISTORICAL ROADMAP NOTICE:** This document (`CHARS.md`) records a research and implementation roadmap. For the authoritative, machine-checked state of the deduction and classical attributes, see [`README.md`](README.md), [`formal/GAPMAP.md`](formal/GAPMAP.md), and [`formal/Logos/`](formal/Logos/).

> **Purpose:** A reusable research and implementation plan for the characteristics discussed in `CHARACTERISTICS.md`.
>
> **Snapshot:** updated against the live working tree after the 2026-09-25 C182/C184/C183 batch. Re-audit the live files before changing anything; this document is a roadmap, not an authority over `formal/axiom_audit.json`, `formal/GAPMAP.md`, or the Lean kernel.
>
> **Important:** This file is deliberately not a generated deduction artifact. It records the state of the project and the safest next experiments. It does not promote a candidate to a theorem, and it does not make a blocked bridge sound by describing it optimistically.

## 1. How to use this document

Read this file before starting a new characteristics milestone. The canonical sources, in order of authority, are:

1. `formal/Logos/*.lean` — actual declarations and proofs;
2. `formal/axiom_audit.json` — exact transitive `#print axioms` footprints;
3. `formal/GAPMAP.md` — theorem ledger and status;
4. `theorems/*.txt` and `base.txt` — Portuguese prose claims, which must reflect the formal status;
5. `CHARACTERISTICS.md` — inventory of the original arguments and their current formal correspondence;
6. generated `README.md` and `investigations/kernel-audit.md` — corroborating output only, never a source to edit by hand.

The project status vocabulary is:

- `PROVEN`: kernel-checked with no substantive named axioms; vocabulary and `CL` footprints must still be reported honestly;
- `PROVEN↑`: kernel-checked under a disclosed `SEM` or `META` axiom; reader-facing output calls this `AXIOMATIC`, not “proved without premises”;
- `AXIOM`: the claim itself is declared;
- `BLOCKED`: the exact missing lemma or vocabulary bridge is recorded;
- `DEFERRED`: intentionally outside the current milestone;
- `COUNTERMODEL`: the machine witness shows the proposed implication is not entailed.

`T p := p` in `Logos.Core` is a definitional consistency choice, not a general theory of truth. Several apparently strong results are therefore purely logical or vocabulary-level results. Do not describe them as transcendental discoveries without an explicit bridge.

## 2. Current strategic conclusion

The project has a strong formal performative core and has established Canonical Aseity (`conditional_canonical_aseity`, `{Means, Subject}`) and atom exclusion (`atom_cannot_ground_the_ground`), but it does **not** yet have a cheap route to positive divine characteristics such as transcendence, strict monotheism, simplicity, omniscience, omnipotence, benevolence, or ordinary personhood.

The easiest remaining work is therefore mostly one of the following:

1. close a small logical bundle of already-proved results;
2. formalize a countermodel or non-entailment that prevents an overclaim;
3. make a new semantic or metaphysical bridge explicit and price its footprint;
4. leave a characteristic deferred until its vocabulary is actually defined.

The completed small batch is:

1. **C182**: prove that generic `Aseity` does not entail the existence of a `Level3_VolitionAlternative` (`Unit`/`False` countermodel);
2. **C184**: prove that a volitional alternative does not entail `Aseity` (`ExtDepAt := True` countermodel); together these give two-way logical independence at the generic frontier;
3. **C183**: bundle the already-proved `greatResult` and `noBothTrueAndFalse` (`Core.lean`);
4. audit, synchronize prose and ledgers, regenerate outputs, and run the full `make` pipeline;
5. only then choose a bridge for a genuinely positive characteristic.

The next work is no longer to re-prove these three generic boundary results. It is to decide whether their logical separation is philosophically useful and, if so, propose an explicit, priced bridge for one positive characteristic.

## 3. Immediate proof queue

### 3.1 C182 — Aseity does not force volitional alternatives

**Current status:** ✅ **PROVEN** in `formal/Logos/ModalPossibilityFrontier.lean:463`; audited footprint `{}` at the `#print axioms` line `:626`.

**Target location:** implemented at `formal/Logos/ModalPossibilityFrontier.lean:463-483`, near the `Aseity` and `Level3_VolitionAlternative` definitions.

**Target statement:**

```lean
theorem aseity_does_not_force_any_volition_alternatives :
    ∃ (World Entity Subject : Type)
      (ExtDepAt : World → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity),
      Aseity World Entity ExtDepAt g ∧
        ¬ ∃ (s : Subject) (a : Prop) (v u : World),
          Level3_VolitionAlternative World Subject WillsAt s a v u
```

**Proof model:** use `Unit` for all three sorts, `fun _ _ => False` for external dependence, and `fun _ _ _ => False` for will. Aseity then reduces to a tautology, while any alleged volitional alternative begins with a false premise.

**Audited footprint:** `{}`. The model uses no substantive axioms; this is now an audited result, not an expectation.

**What it proves:** generic predicate separation only. It does not prove that `Entity.ofGround` is aseitous, does not define causal dependence, and does not establish a divine metaphysics.

**Status after the batch:** ✅ C182 is a generic countermodel with `Unit`/`False`; C184 is the complementary model with `Bool`/`True`. The pair is machine-checked with `{}` footprints. Together they show two-way non-entailment, not aseity of `Entity.ofGround`.

### 3.2 C184 — Volitional alternatives do not imply aseity

**Current status:** ✅ **PROVEN** in `formal/Logos/ModalPossibilityFrontier.lean:485`; audited footprint `{}` at the `#print axioms` line `:627`. The companion received ledger ID C184.

**Target statement shape:**

```lean
theorem volitional_alternative_does_not_force_aseity :
    ∃ (World Entity Subject : Type)
      (ExtDepAt : World → Entity → Prop)
      (WillsAt : World → Subject → Prop → Prop)
      (g : Entity) (s : Subject) (a : Prop) (v u : World),
      Level3_VolitionAlternative World Subject WillsAt s a v u ∧
        ¬ Aseity World Entity ExtDepAt g
```

**Proof model:** `World := Bool`, `Entity := Subject := Unit`, `ExtDepAt := fun _ _ => True`, and `WillsAt := fun w _ _ => w = true`. Use worlds `true` and `false`. The will relation supplies the first conjunct and `Aseity` is refuted by applying it to `true`.

**Audited footprint:** `{}`. The model uses `World := Bool`, `Entity := Subject := Unit`, `ExtDepAt := fun _ _ => True`, and `WillsAt := fun w _ _ => w = true`.

**Logical consequence:** C182 plus C184 establishes both non-entailments:

- `Aseity ↛ ∃ Level3_VolitionAlternative`;
- `∃ Level3_VolitionAlternative ↛ Aseity`.

This is a frontier theorem about independently chosen generic predicates, not a claim about the canonical foundation. C182 and C184 are now assigned and audited as C182 and C184 respectively.

### 3.3 C183 — Nonempty and nonconflating truth/falsity bundle

**Current status:** ✅ **PROVEN** in `formal/Logos/Core.lean:170`; audited footprint `{}` at the `#print axioms` line `:209`.

**Target location:** implemented at `formal/Logos/Core.lean:170-176`, immediately after `greatResult` and `noBothTrueAndFalse`.

**Target statement:**

```lean
theorem rightWrong_nonempty_and_nonconflating :
    (∃ p q : Prop, T p ∧ IsFalse q) ∧
      ∀ p : Prop, ¬ (T p ∧ IsFalse p)
```

**Proof:**

```lean
exact ⟨greatResult, noBothTrueAndFalse⟩
```

**Audited footprint:** `{}`. The declaration is a mechanical bundle of the already-proved C8 and C9 results.

**Value:** mechanically safe and useful as a closure of the Level-0 logical spine. It bundles C8 and C9 only. Because `T p := p`, it is not a new truth theorem, not a new transcendence argument, and not a divine characteristic.

**Decision:** C183 has been implemented because the goal was to close the queued logical batch. It is a bookkeeping closure, not a substantive philosophical advance.

## 4. Characteristic-by-characteristic status and next action

### 1. Transcendence and externality

- **Prose source:** `CHARACTERISTICS.md:21-55`; original argument is strong prose but formally absent.
- **Live nearest results:** `NecessityEternity.ofGround_ground_of_reality` (`formal/Logos/NecessityEternity.lean:140-142`) is thin definitional grounding; `PersonalGroundOfReality.the_person_supports_the_reality_of_right` is grounding the reality of Right/Wrong, not externality to every system.
- **Ledger status:** ultimate-ground and quantifier-swap routes C78/C79/C88 are blocked or retired (`formal/GAPMAP.md:440-444`).
- **Easy next proof:** none from current vocabulary. A generic countermodel could show that “grounds every actual entity” does not imply “external to every formal/evaluative system,” but this requires first defining the two notions separately.
- **Required design decision:** define whether externality is logical, ontological, causal, or hierarchical. Do not encode all four under one name.
- **Stop condition:** until that definition and a bridge are approved, keep the characteristic `❌ absent`.

### 2. Aseity

- **Current source:** `ModalPossibilityFrontier.lean:122-124` and `CanonicalAseity.lean`.
- **Current distinction:** generic `Aseity` exists; C182/C184 provide two-way independence with volitional alternatives (`{}`); canonical external grounding `ExternalGrounding` and `CanonicalAseity` are formalized in `Logos.CanonicalAseity`.
- **Current result:** C185 (`{}`) establishes generic meaning exclusion; C186 (`{Means, Subject}`) proves `CanonicalAseity Entity.ofGround` conditional on discriminating subjects (`∀ s, ∃ p, ¬ Means s p`); unconditional atom exclusion is proven (`atom_cannot_ground_the_ground`, `{Means, Subject}`); and `unconditional_aseity_independent_of_bare_agency` (`{}`) isolates the exact independence boundary showing that unconstrained `Means` does not entail unconditional aseity without a finite-subjectivity premise.
- **Do not claim:** that unconditional aseity is proved for the ultimate foundation without the discriminating-subject premise, or that the current formalization establishes uncausedness in an efficient-causal sense.

### 3. Necessity and non-contingency

- **Live result:** `ofGround_necessary` and `ofGround_necessary_ground_of_reality` are definitional consequences of the world-rigid `Entity.ofGround` constructor.
- **Additional separation:** `PersonhoodOntologyAudit.faithful_contingent_person_fails_necessary_subject` (`formal/Logos/PersonhoodOntologyAudit.lean:216-227`) refutes the unqualified implication from personhood to necessary personhood.
- **Next work:** no new positive theorem is cheap. C181 is already the generic stage-uniformity transport (`NecessityEternity.lean:101-121`); do not add a duplicate canonical corollary merely to increase the theorem count.
- **Boundary:** performative necessity in the prose is not automatically the same thing as modal `NecessaryEntity` or `NecessarySubject`.

### 4. Normative sovereignty and authority

- **Live result:** C179, `DirectNormativeRetorsion.no_correct_claim_of_no_right_can_be_true`, is a local interpreted-signature result with footprint `{}`. The broader personal-ground and reality-hook results are conditional or vocabulary-priced.
- **Ledger:** C102–C105 remain the direct retorsion route; the canonical attribution to the ultimate foundation is not automatic.
- **Easy next proof:** none that establishes divine sovereignty. A local theorem can only show that a particular normative denial cannot be both correctly claimed and true.
- **Missing bridge:** a justified connection from the local retorsion/judicative structure to the canonical `Entity.ofGround` or an explicit foundational subject.
- **Do not claim:** C179 alone proves that the foundation is sovereign, authoritative, or God.

### 5. Freedom, personality, and minimal subjecthood

- **Live positive results:** the conditional route through `GenuineNormativity` and `Chooses → FreeWill`; `Person.free_subject_is_person`; A14 route `Choice.freeWill_exists` is `PROVEN↑` under `AxIntentionalChoice`.
- **Exact blocker:** `Choice.rejectedHornCoMeant` (`formal/Logos/Choice.lean:231-246`), specifically `∃ s p, Means s p ∧ Means s (¬ p)`, for unconditional genuine choice.
- **Existing countermodel:** the veridical-meaning model shows that the performative datum, plurality, and Right/Wrong do not force a subject to co-mean both horns.
- **Next work:** do not prove F1b by weakening the target or silently declaring the rejected-horn datum. Either formulate a new explicit semantic bridge or retain `BLOCKED`.
- **Do not claim:** that minimal structural subjecthood is ordinary consciousness, psychological personality, or necessary divine personhood.

### 6. Unity and oneness

- **Completed live layer:** ✅ **PROVEN** in `formal/Logos/FoundationalUnicity.lean` (C207–C213; audited footprints `{}` and `{CL, Means, Subject}`).
- **Results:**
  1. Master Metaphysical Unicity: `universal_ground_unicity` (C207, `{CL, Means, Subject}`) — two distinct entities cannot both be universal modal grounds under asymmetric grounding;
  2. Concrete Atom Exclusion: `no_atom_is_universal_modal_ground` (C208, `{Means, Subject}`) — no atomic factual state can ground all reality;
  3. Discriminating Subject Exclusion: `no_discriminating_subject_is_universal_modal_ground` (C209, `{Means, Subject}`) — no finite subject can ground all reality;
  4. Sole Universal Ground: `ofGround_sole_universal_ground` (C210, `{Means, Subject}`) — `Entity.ofGround` is the unique universal ground candidate in Γ;
  5. The Master Synthesis: `ofGround_foundational_unicity` (C211, `{CL, Means, Subject}`, 0 substantive axioms);
  6. Metatheoretic Independence: `unicity_does_not_force_unitarian_monad` (C212, `{}`) — foundational unicity of universal grounding does not force a solitary, relationless monad, keeping the Trinitarian frontier open;
  7. Ontological Transcendence: `unicity_strictly_transcends_world` (C213, `{Subject}`) — strictly excludes pantheistic conflation with the world.
- **Honest boundary:** establishes foundational unicity of universal grounding in reality (Aquinas *ST* I, q. 11, a. 3); strictly separated from numerical unitarianism (which would rule out Trinitarian relations, separated as `⊨ INDEPENDENT`) and theological identification (deferred).
- **Existing separation:** `TheologicalModalHardening.necessary_existence_not_entails_uniqueness` (`formal/Logos/TheologicalModalHardening.lean:405-414`) has footprint `{}` and supplies a two-ground countermodel for bare necessity.
- **Do not conflate:** foundational unicity (one universal ground of all reality) with numerical unitarianism (which collapses internal Trinitarian relations) or pantheism (which collapses the ground into the world).

### 7. Simplicity and non-compositeness

- **Current status:** ✅ **PROVEN** in `formal/Logos/DivineSimplicity.lean` (C192–C196; audited footprints `{}` and `{Means, Subject, propext}`).
- **Results:**
  1. `ProperPart p e := p ≠ e ∧ GroundsEntity p e`, `NonComposite e := ¬ ∃ p, ProperPart p e`, proving `non_composite_iff_canonical_aseity` and `ofGround_non_composite` (`{Means, Subject, propext}`);
  2. Structural Inextension: `ofGround_has_no_internal_components` (C193, `{Subject}`);
  3. Intentional Simplicity: `ofGround_undivided_meaning` (C194, `{Means, Subject}`) and `discriminating_subject_not_undivided`;
  4. Ontological Transcendence: `ofGround_transcendent` (C195, `{Subject}`);
  5. The Master Synthesis: `ofGround_divine_simplicity` (C196, `{Means, Subject, propext}`, 0 substantive axioms);
  6. Metatheoretic Independence: `composite_entity_fails_simplicity` (C192, `{}`).
- **Honest boundary:** this establishes mereological, structural, and intentional simplicity of `Entity.ofGround` — it does not establish identity of essence and existence or exhaustive formal simplicity. Scholastic simplicity (essence-existence identity) is explicitly separated in the attributes table as `❌ NOT ESTABLISHED`.

### 8. Eternity, timelessness, and ontological precedence

- **Completed live layer:** C181 and canonical corollaries in `NecessityEternity.lean:101-188`: stage uniformity, everlasting, atemporal, and non-succession results.
- **Divine Immutability completed:** ✅ **PROVEN** in `formal/Logos/DivineImmutability.lean` (C197–C201; footprints `{}` and `{Initiates, Means, State, Subject}`). Results:
  1. `ModalInvariance` (`ofGround_modal_invariance`, C198, `{Subject}`);
  2. `StageInvariance` (`ofGround_stage_invariance`, C199, `{Subject}`);
  3. `TransitionInvariance` (`ofGround_transition_invariance`, C200, `{Initiates, State, Subject}`);
  4. `CapacityInvariance` (`ofGround_capacity_invariance`, `{Means, Subject}`);
  5. The Master Synthesis: `ofGround_divine_immutability` (C201, `{Initiates, Means, State, Subject}`, 0 substantive axioms);
  6. The Thomistic Principle: `necessity_and_atemporality_yield_immutability` (ST I q. 9 a. 1–2);
  7. Metatheoretic Independence: `contingent_entity_fails_immutability` (C197, `{}`).
- **Honest boundary:** establishes modal, temporal, process, and capacity unchangeability in Γ; does not claim psychological impassibility or constrain relational intentionality. Psychological impassibility is explicitly separated in the attributes table as `❌ NOT ESTABLISHED`.

### 9. Precedence to the true/false distinction

- **Current status:** no live precedence theorem (`CHARACTERISTICS.md:264-288`); only truth/falsity distinction and personal grounding results exist.
- **Next work:** define `Precedes` at the intended level. Logical precedence, ontological grounding, temporal precedence, and causal priority are different predicates.
- **Safe exploratory step:** a generic model separating “ground of the distinction” from “priority before the distinction” can be built only after those predicates are declared.
- **Do not claim:** that `ofGround_ground_of_reality` automatically means the ground precedes truth/falsity.

### 10. Non-conditioned and non-relative character

- **Completed architectural result:** C180, `HardenedInvariance.agent_invariant_core_is_strictly_inside_freewill_invariant_core` (`formal/Logos/HardenedInvariance.lean:223-237`), footprint `{}`.
- **Boundary:** it compares dependency-layer cores; it is not metaphysical non-relativity across systems, perspectives, or worlds.
- **Next work:** if desired, a generic countermodel can show that architectural invariance does not imply a canonical `Absolute`/`Unconditioned` predicate. Do not rename C180 as divine non-relativity.

### 11. Universality and infinity

- **Completed live layer:** ✅ **PROVEN** in `formal/Logos/FoundationalOmnipresence.lean` (C202–C206; footprints `{}` and `{Means, Subject}`). Results:
  1. `WorldRigidPresence` (`ofGround_world_rigid_presence`, C203, `{Subject}`);
  2. `UniversalModalGround` (`ofGround_universal_modal_ground`, C204, `{Means, Subject}`): grounds every entity in every possible world;
  3. `NonReciprocalGround` (`ofGround_non_reciprocal_ground`, C205, `{Means, Subject}`): asymmetric grounding, ungrounded by atoms or finite subjects;
  4. `MaximalCapacity` (`ofGround_maximal_capacity`, `{Means, Subject}`);
  5. The Master Synthesis: `ofGround_foundational_omnipresence` (C206, `{Means, Subject}`, 0 substantive axioms);
  6. The Thomistic Principle: `omnipresence_from_universal_ground_and_aseity` (ST I q. 8 a. 1–3);
  7. Metatheoretic Independence: `finite_entity_fails_omnipresence` (C202, `{}`).
- **Honest boundary:** establishes foundational sustaining presence across modal reality in Γ; explicitly distinguishes foundational omnipresence from physical spatial omnipresence or quantitative metric infinity (both of which are explicitly separated in the attributes table as `❌ NOT ESTABLISHED`).
- **Do not claim:** omniscience or omnipotence from universality; `CHARACTERISTICS.md` explicitly disclaims that inference.

### 12. Pure actuality

- **Completed live layer:** ✅ **PROVEN** in `formal/Logos/DivinePureActuality.lean` (C214–C220; footprints `{}` and `{Initiates, Means, State, Subject}`). Results:
  1. Absence of Passive Existential Potency (`ofGround_no_existential_potency`, C215, `{Subject}`): necessary existence across all possible worlds;
  2. Absence of Passive Grounding Potency (`ofGround_no_grounding_potency`, C216, `{Means, Subject}`): ungrounded by any external entity under finite subjectivity;
  3. Absence of Passive Transition Potency (`ofGround_no_transition_potency`, C217, `{Initiates, State, Subject}`): immune to temporal becoming and agential succession;
  4. Absence of Passive Intentional Potency (`ofGround_no_intentional_potency`, C218, `{Means, Subject}`): exhaustive propositional meaning capacity;
  5. The Master Synthesis: `ofGround_divine_pure_actuality` (C219, `{Initiates, Means, State, Subject}`, 0 substantive axioms);
  6. Divine Incorporeality and Immateriality: `ofGround_incorporeal` (C220, `{Subject}`, Aquinas ST I q. 3 a. 1–2: *Deus non est corpus*);
  7. The Thomistic Principle: `necessity_aseity_and_immutability_yield_pure_actuality` (ST I q. 3 a. 1–2, q. 4 a. 1);
  8. Metatheoretic Independence: `entity_with_potency_fails_pure_actuality` (C214, `{}`).
- **Honest boundary:** establishes metaphysical Pure Actuality (*Actus Purus* in Γ: zero passive potentiality and universal modal grounding); strictly distinguished from physical kinetic motion or thermodynamic energy (separated as `❌ NOT ESTABLISHED` in the attributes table).

### 13. Sovereignty over value and goodness

- **Separation already machine-checked:** `MoralFrontierAudit.epistemic_normativity_without_practical_obligation` (`formal/Logos/MoralFrontierAudit.lean:173-183`) has footprint `{}`.
- **Positive moral layer:** `Good` is a fair relational definition; `moral_good_obtains` is `PROVEN↑` under the disclosed `AxBenevolentBearingObtains` META bridge (`MoralFrontierAudit.lean:189-214`).
- **Next work:** the remaining gap is divine attribution and the negative `Evil` pole, not a new proof that logical normativity entails moral value.
- **Do not claim:** that a moral-good inhabitant is necessarily the ultimate foundation.

### 14. Omniscience

- **Current status:** only frontier definitions in `formal/Logos/DeepModalFrontier.lean:313-317`; no theorem.
- **Next work:** would require a knowledge predicate, a relation from normativity/truth to knowledge, and an unrestricted-knowledge premise.
- **Recommendation:** retain the explicit prose disclaimer; do not manufacture a divine knowledge bridge.

### 15. Omnipotence

- **Current status:** no live theorem or substantive predicate.
- **Next work:** would require a causal/creative-power vocabulary and a bridge from foundation to power over every possible state of affairs.
- **Recommendation:** keep independent from foundational scope; universality does not imply omnipotence.

### 16. Benevolence and ordinary moral perfection

- **Current status:** `moral_good_obtains` is only `PROVEN↑` under `AxBenevolentBearingObtains`; the divine attribution remains a frontier.
- **Next work:** a new positive claim needs an explicit relation from the canonical foundation to benevolent willing, not merely the existence of a good action.
- **Recommendation:** do not promote a META-priced moral pole to an unconditional divine attribute.

### 17. Founding all reality versus creation

- **Completed thin result:** `ofGround_ground_of_reality` is definitional grounding, not efficient causation.
- **Existing separation:** `ConditionalTheology.necessary_ground_not_entails_contingent_creation` (`formal/Logos/ConditionalTheology.lean:417-424`) is a countermodel.
- **Next work:** creation ex nihilo requires a creator/creation relation, temporal beginning or contingency semantics, and a bridge from necessary ground to production.
- **Do not claim:** that grounding validity creates entities.

### 18. Pantheism as the excluded alternative

- **Current status:** no formal universe-composition or contingency theorem supports the prose rejection.
- **Only nearby theorem:** `ofGround_ne_ofSubject` separates the ground from subject correlates, not from the universe as a whole.
- **Next work:** a formal pantheism model would first need a precise `Universe = Ground` or identity predicate and a definition of the universe.
- **Recommendation:** keep this as a documented boundary, not a derived rejection.

### 19. Trinity, incarnation, and biblical personal relations

- **Existing separations:** `preceding_theory_not_entails_trinity` and `preceding_theory_not_entains_incarnation` (`formal/Logos/ConditionalTheology.lean:336-355`, `:376-396`) are countermodel/independence results, not positive theology.
- **Ledger:** F6/F8 remain deferred.
- **Next work:** no cheap proof; a positive result would require explicit Trinitarian/incarnational structures and substantive premises.
- **Do not infer:** Trinity or incarnation from generic plurality, personhood, or necessary existence.

## 5. Existing negative results that should be reused, not re-proved

The following already provide useful boundaries for future work:

- `TheologicalModalHardening.necessary_existence_not_entails_uniqueness` — necessary existence does not imply one ground;
- `PersonhoodOntologyAudit.faithful_contingent_person_fails_necessary_subject` — personhood does not imply necessary personhood;
- `MoralFrontierAudit.epistemic_normativity_without_practical_obligation` — epistemic normativity does not imply practical obligation;
- `MoralFrontierAudit.moral_pole_postulate_is_not_a_consequence` — the moral poles are not forced by the relying structure;
- `ConditionalTheology.necessary_ground_not_entails_contingent_creation` — necessary grounding does not imply creation;
- `ConditionalTheology.preceding_theory_not_entails_trinity` and `preceding_theory_not_entails_incarnation` — the preceding theory does not entail those structures;
- `HardenedInvariance.agent_invariant_core_is_strictly_inside_freewill_invariant_core` — architectural invariance is not metaphysical non-relativity;
- `ModalPossibilityFrontier.model_MC21_consistent` — aseity and a selected volitional alternative can coexist.

These are not “failed attempts.” They are the current reason a positive theorem is blocked and should be cited in every new roadmap entry.

## 6. Recommended milestone sequence

### Milestone A — close the current generic frontier (completed 2026-09-25)

The batch is complete:

1. C182, the `Aseity`/`Level3_VolitionAlternative` separation;
2. C184, the companion non-entailment model;
3. C183, the truth/falsity bundle.

Each declaration has an English docstring, a nearby proof, a `#print axioms`
audit line, and the actual footprint `{}`. The synchronized records are in
`formal/GAPMAP.md`, `base.txt`, `theorems/T3.txt`, `theorems/T19.txt`, and
`CHARACTERISTICS.md`.

The result is deliberately narrow: C182/C184 are generic countermodels, while
C183 is nearly definitional. None is evidence for a positive divine
characteristic. The next milestone is bridge selection, not more packaging.

### Milestone B — decide whether the separation is philosophically useful

`CHARACTERISTICS.md` now states the two-way independence explicitly. If the
separation is useful, propose one explicit bridge; otherwise retain it as a
formal frontier theorem and move on. Do not manufacture a positive bridge
merely to make the table look complete.

### Milestone C — propose bridges one at a time

For any positive characteristic, write a short bridge proposal before adding Lean code. It must identify:

- the old predicate and the new predicate;
- the exact proposed implication;
- whether it is `VOCAB`, `SEM`, or `META`;
- a consistency model for its negation;
- the resulting theorem footprint;
- which prose claims would be strengthened or withdrawn.

Priority for bridge proposals, if the project wants the most philosophically load-bearing results:

1. canonical aseity/externality;
2. unconditional free will (`rejectedHornCoMeant`);
3. divine uniqueness;
4. moral or value attribution to the foundation.

Do not implement a bridge merely because it is easy to state. A transparent axiom is preferable to a hidden `sorry` or an overstated theorem.

### Milestone D — absent-vocabulary research

Only after Milestone C should the project add predicates for simplicity, pure actuality, infinity, omniscience, omnipotence, or logical precedence. Each new predicate needs:

1. a formal definition;
2. a neutral consistency model;
3. a non-entailment test against the existing theory;
4. an English gloss;
5. a ledger classification and exact footprint.

This prevents the vocabulary from being designed backwards from a desired theological conclusion.

## 7. Definition of done for any future characteristic theorem

A candidate is complete only when all applicable items are done:

- [x] Lean declaration exists in the correct module and namespace.
- [x] The statement matches the prose claim exactly; no stronger adjective is smuggled in.
- [x] The theorem has an English docstring explaining both the result and its boundary.
- [x] `#print axioms` is present and the actual footprint is audited.
- [x] `formal/GAPMAP.md` receives the correct ID, status, theorem name, and footprint.
- [x] `formal/axiom_audit.json` is regenerated, never hand-edited.
- [x] The matching `theorems/T*.txt` is created or updated, with the exact Lean dependency and axiom footprint.
- [x] `base.txt` is patched in Portuguese, including any “still requires proof” or countermodel note.
- [x] `CHARACTERISTICS.md` uses the new status and does not overstate divine scope.
- [x] `formal/Logos/ClaimMeanings.lean` needs no update: all three claims have kernel declarations.
- [x] Generated `README.md`, `investigations/kernel-audit.md`, and dependency artifacts are regenerated.
- [x] `make` passes from the repository root.
- [ ] No `sorry`, no staged secret, and no accidental generated-file edit is left behind.

From the repository root, the standard regeneration sequence is:

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal && lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot
cd .. && python3 scripts/audit_footprints.py && python3 scripts/build_deduction.py
make
```

`README.md` is auto-generated. Never edit it by hand.

## 8. Red flags for future agents

- “Necessary” in the prose does not automatically mean `NecessarySubject`.
- “Universal grounding” does not mean infinity, omnipresence, or omnipotence.
- “Normative authority” does not automatically mean benevolence.
- `Aseity` over an arbitrary relation does not prove aseity of `Entity.ofGround`.
- `Level3_VolitionAlternative` has no built-in accessibility, incompatibility, or distinct-world requirement.
- A countermodel is a positive formal result, but it is not a positive characteristic proof.
- A theorem with `{Means, Subject}` or `{Subject}` is vocabulary-priced even when its logical content is trivial.
- `PROVEN↑` is not unconditional proof; reader-facing output must say `AXIOMATIC`.
- A deferred claim is not an axiom unless it is explicitly declared and tagged.
- Do not resurrect deleted bridges (`ConstitutiveNormativeBridge`, retired manufactured ground witnesses, or old necessary-person theorems).
- Do not edit `README.md`, `kernel-audit.md`, or `axiom_audit.json` as a shortcut around the audit pipeline.

## 9. Source index

- `CHARACTERISTICS.md:1-765` — full prose inventory, formal-status layer, and current candidate checkpoints.
- `formal/Logos/Core.lean:35-199` — Level-0 truth/falsity definitions, C8/C9, and the C183 location.
- `formal/Logos/ModalPossibilityFrontier.lean:122-124,302-304,448-497` — `Aseity`, Level-3 alternatives, MC21, and the C182/C184 countermodels.
- `formal/Logos/NecessityEternity.lean:101-188` — C181 and canonical necessity/eternity corollaries.
- `formal/Logos/HardenedInvariance.lean:223-237` — C180 architectural invariance boundary.
- `formal/Logos/TheologicalModalHardening.lean:405-414` — necessary existence versus uniqueness countermodel.
- `formal/Logos/PersonhoodOntologyAudit.lean:216-227` — personhood versus necessary-subject countermodel.
- `formal/Logos/Choice.lean:231-268` — exact F1b missing resource and its consequence.
- `formal/Logos/MoralFrontierAudit.lean:173-214,255-269` — epistemic/practical separation and the priced moral-positive route.
- `formal/Logos/ConditionalTheology.lean:336-424` — Trinity, incarnation, and creation separations.
- `formal/GAPMAP.md:403-445,743-799` — Level-0/1 ledger and deferred/blocked frontier.
- `base.txt:1140-1146` — Portuguese formal-status boundary and C182/C184/C183 records.
- `theorems/T3.txt` — Level-0 truth/falsity theorem prose, including the C183 bundle record.
- `theorems/T19.txt` — Portuguese C182/C184 separation record and scope limitations.
- `theorems/T15.txt` — current necessity/eternity scope and honest limitations.
- `AGENTS.md:3-60` — synchronization, audit, regeneration, and generated-file rules.
