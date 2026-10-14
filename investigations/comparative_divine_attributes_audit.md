# Comparative Divine Attributes Audit: `logos` vs `logos4`

**Author:** Γ / Logos Verification Architecture  
**Date:** October 2026  
**Status:** Audit & Gap Analysis Document  
**Scope:** Ontological, Classical Theistic, and Trinitarian Characteristics  

---

## 1. Executive Summary

This investigation provides a rigorous, file-backed comparative audit between the primary repository (`~/logos`) and the streamlined, modularized repository (`~/logos4`).

The inquiry specifically examines:
> *"Look at ~/logos4 and at ~/logos. See if logos4 didn't miss anything important. Like some divine characteristics or something."*

### Key Finding
**Yes, `logos4` omitted a substantial portion of the classical theistic and Trinitarian attribute system.**

- In **`~/logos`**, there are **40 catalogued classical divine attribute rows** spanning over **8,500 lines** of dedicated Lean 4 formalization (`DivineClassicalAttributes.lean` and `DivineTrinitarianAttributes.lean`), backed by an audited ledger (`investigations/ledger.md:3385–4191`).
- In **`~/logos4`**, the system was consolidated into a 4-module architecture (`System.lean`, `Elimination.lean`, `Agency.lean`, `Source.lean`), bundling **8 core divine characteristics** inside `structure DivineReality` (`formal/Logos/Source.lean:2690–2730`).

While `logos4` successfully captures the core master deduction of the *Free Personal Source* (Aseity, Transcendence, Immanence, Unicity, Sovereign Freedom, Omniscience, Intentionality, and Trinitarian Communion), it omitted major pillars of classical theism that are fully formalized in `logos`:
1. **Divine Simplicity** (*Simplicitas Dei* — non-composite, undivided essence, zero internal parts);
2. **Divine Immutability** (*Immutabilitas Dei* — modal, temporal, process, and capacity invariance);
3. **Eternity and Atemporality** (*Aeternitas* — everlasting, atemporal, outside temporal succession);
4. **Pure Actuality** (*Actus Purus* — total absence of passive existential, grounding, transition, or intentional potency);
5. **Foundational Omnipotence** (*Omnipotentia* — gapless operative scope over non-contradictory states);
6. **Divine Love and Agape** (*Caritas Dei* — sovereign directed benevolence toward contingent reality);
7. **Precedence to Right/Wrong Distinction** (the ground conditions the moral order without being an individual moral actor);
8. **Exclusion of Pantheism** (the ground is strictly distinct from the totality of cosmic entities);
9. **Divine Incorporeality** (immaterial, disjoint from physical atomic configurations);
10. **Exclusion from Individual Person-Correlate** (Anti-Quaternity: the ground is personal divine reality indwelt by the Trinity, but not a fourth individual chooser).

---

## 2. The 40 Classical Attribute Rows in `~/logos`

In `~/logos`, the divine characteristics are rigorously mapped across **three distinct divine-adjacent scopes** to prevent category errors (see `investigations/ledger.md:3385–3400`):
1. **Divine Being / Ground:** Attributes of the ultimate ontological foundation as a nature/essence (`Entity.ofGround`);
2. **Divine Personhood:** Trinitarian hypostatic distinctions, relations of origin, and personal communion;
3. **Personal Ground / Person-Type:** The agential, normative, and intentional features established by the transcendental deduction of agency.

### Table of the 40 Catalogued Rows in `~/logos`

| # | Attribute Name | Scope | Formal Status in `logos` | Axiom Footprint / Price | Lean Anchor in `logos` |
|---|---|---|---|---|---|
| 1 | **Personal** (Ground-type) | Personal Ground | `✅ PROVEN` | 0 substantive axioms | `PersonalGroundOfReality.lean#personal_ground_of_right_wrong` |
| 2 | **Personal** (Epistemic sibling) | Personal Ground | `✅ PROVEN` | 0 substantive axioms | `EpistemicPersonalGround.lean#epistemic_ground_is_personal` |
| 3 | **Psychological Personality** | Personal Ground | `✅ PROVEN` (independent) | 0 substantive axioms (`{}`) | `PersonhoodOntologyAudit.lean#faithful_model_satisfies_free_will` |
| 4 | **Rational Nature** | Personal Ground | `✅ PROVEN` | 0 substantive axioms | `Person.lean#person_iff_thomisticCore` |
| 5 | **Free Will** | Personal Ground | `✅ PROVEN` (conditional) | 0 substantive axioms | `IndubitableNormativeFreeWill.lean#indubitable_normative_free_will` |
| 6 | **Asiety** (True Choice) | Personal Ground | `✅ PROVEN` (conditional) | 0 substantive axioms | `AsietyFreedom.lean#weakChoice_implies_asiety` |
| 7 | **Shared Freedom of Ground** | Divine Being | `✅ PROVEN` ◈ | 0 substantive axioms (◈ META def) | `AsietyFreedom.lean#asietyFreedom_yields_asietyFreeWill` |
| 8 | **Divine Love** (Lover of Cosmos) | Divine Being | `⚠️ AXIOMATIC` | 1 substantive (`AxGroundLovesContingentRealm`) | `DivineClassicalAttributes.lean#the_ground_is_a_necessary_and_chosen_lover` |
| 9 | **Independent Will** | Personal Ground | `✅ PROVEN` | 0 substantive axioms | `Person.lean#person_iff_freeIndependentWill` |
| 10 | **Dominion Over Acts** | Personal Ground | `📘 DEFINITIONAL` | 0 substantive axioms | `Person.lean#DominionOverActs` |
| 11 | **Ground of Normativity** | Personal Ground | `✅ PROVEN` (conditional) | 0 substantive axioms | `PersonalNormativeGround.lean#person_grounds_normative_polarity` |
| 12 | **Non-Relative Core** | Proof Architecture | `✅ PROVEN` | 0 substantive axioms (`{}`) | `AgencyAuditsAndFrontiers.lean#agent_invariant_core` |
| 13 | **Necessary Divine Ground** | Divine Being | `✅ PROVEN` | 0 substantive axioms | `DivineClassicalAttributes.lean#ofGround_necessary_ground_of_reality` |
| 14 | **Canonical Aseity** | Divine Being | `✅ PROVEN` (conditional) | 0 substantive axioms | `DivineClassicalAttributes.lean#conditional_canonical_aseity` |
| 15 | **Foundational Unicity** | Divine Being | `✅ PROVEN` | 0 substantive axioms (under F15 `VOCAB`) | `DivineClassicalAttributes.lean#ofGround_foundational_unicity` |
| 16 | **Numerical Unitarianism** | Divine Being | `🧱 COUNTERMODEL` | 0 substantive axioms (`{}`) | `DivineClassicalAttributes.lean#unicity_does_not_force_unitarian_monad` |
| 17 | **One God (Strict Monotheism)** | Divine Being | `✅ PROVEN` (conditional) | 0 substantive axioms | `DivineClassicalAttributes.lean#exactly_one_universal_modal_ground` |
| 18 | **Perfect (Moral) Goodness** | Divine Being | `🧱 INDEPENDENT` | Countermodel `M_amoral` (`{}`) | `MoralFrontierAudit.lean#moral_pole_postulate_is_not_a_consequence` |
| 19 | **Everlasting (Ever-present)** | Divine Being | `✅ PROVEN` | 0 substantive axioms | `DivineClassicalAttributes.lean#the_ground_everlasting` |
| 20 | **Atemporal (Outside Succession)** | Divine Being | `✅ PROVEN` | 0 substantive axioms | `DivineClassicalAttributes.lean#the_ground_atemporal` |
| 21 | **Precedence to Right/Wrong** | Divine Being | `✅ PROVEN` | 0 substantive axioms | `DivineTrinitarianAttributes.lean#ofGround_precedes_the_right_wrong_distinction` |
| 22 | **Exclusion of Pantheism** | Divine Being | `🧱 COUNTERMODEL` | 0 substantive axioms | `DivineClassicalAttributes.lean#the_ground_is_not_the_universe` |
| 23 | **Exclusion from Personhood** | Divine Being | `🧱 COUNTERMODEL` | 0 substantive axioms (Anti-Quaternity) | `DivineClassicalAttributes.lean#ofGround_not_a_person_correlate` |
| 24 | **Divine Simplicity** | Divine Being | `✅ PROVEN` (conditional) | 0 substantive axioms (sole bearer) | `DivineClassicalAttributes.lean#divine_simplicity_sole_bearer` |
| 25 | **Ontological Transcendence** | Divine Being | `✅ PROVEN` | 0 substantive axioms | `DivineClassicalAttributes.lean#ofGround_sole_transcendent_ground` |
| 26 | **Scholastic Simplicity** | Divine Being | `❌ NOT ESTABLISHED` | Distinction between essence & existence | — |
| 27 | **Divine Immutability** | Divine Being | `✅ PROVEN` | 0 substantive axioms | `DivineClassicalAttributes.lean#ofGround_divine_immutability` |
| 28 | **Psychological Impassibility** | Divine Being | `❌ NOT ESTABLISHED` | Not a person; person-level affect open | — |
| 29 | **Foundational Omnipresence** | Divine Being | `✅ PROVEN` | 0 substantive axioms | `DivineClassicalAttributes.lean#ofGround_foundational_omnipresence` |
| 30 | **Physical Omnipresence** | Divine Being | `❌ NOT ESTABLISHED` | Spacetime metric coordinates absent | — |
| 31 | **Quantitative Metric Infinity**| Divine Being | `❌ NOT ESTABLISHED` | Metric cardinal size disclaimed | — |
| 32 | **Divine Pure Actuality** | Divine Being | `✅ PROVEN` (conditional) | 0 substantive axioms (*Actus Purus*) | `DivineClassicalAttributes.lean#ofGround_divine_pure_actuality` |
| 33 | **Physical / Kinetic Energy** | Divine Being | `❌ NOT ESTABLISHED` | Thermodynamic energy disclaimed | — |
| 34 | **Foundational Omniscience** | Divine Being | `✅ PROVEN` | 0 substantive axioms (truth-exhaustive) | `DivineClassicalAttributes.lean#ofGround_foundational_omniscience` |
| 35 | **Infallible Omniscience** | Divine Being | `❌ NOT ESTABLISHED` | Refuted for bare ground (`¬TruthTracking`)| `DivineClassicalAttributes.lean#ofGround_not_truth_tracking` |
| 36 | **Foundational Omnipotence** | Divine Being | `✅ PROVEN` | 0 substantive axioms (gapless operative) | `DivineClassicalAttributes.lean#ofGround_foundational_omnipotence` |
| 37 | **Causal / Creative Omnipotence**| Divine Being | `◆ AXIOM` | 1 substantive (`ground_produces_every_satisfiable_form`) | `DivineThomisticProduction.lean#ground_produces_every_satisfiable_form` |
| 38 | **Creator of Contingent Realm**| Divine Being | `🧱 COUNTERMODEL` | Countermodel populated world (`{}`) | `ConditionalTheology.lean#the_creation_countermodel_is_a_populated_contingent_world` |
| 39 | **Three Divine Persons (Trinity)**| Divine Personhood | `⚠️ AXIOMATIC` | 3 substantive axioms (Agape, Spirit, Word)| `DivineTrinitarianAttributes.lean#agape_entails_tripersonality` |
| 40 | **Incarnation** | Divine Personhood | `🧱 COUNTERMODEL` | Unincarnate model (`{}`) | `ConditionalTheology.lean#preceding_theory_not_entails_incarnation` |

---

## 3. What `logos4` Currently Bundles

In `/home/quirinpa/logos4/formal/Logos/Source.lean:2690–2730`, the divine reality is encapsulated in a single Lean structure:

```lean
structure DivineReality (S : ConcreteSystem.{0}) (T : CandidateGround S) : Prop where
  aseity : IsNecessary S T ∧ NatureInvariant S T
  transcendence : ∃ e : T.ExtEntity, T.ground = GroundIdentity.external e
  immanence : T.GroundsConcreteActuality T.ground S.actualWorld
  unicity : ∃ g : Logos.Entity.Entity, Logos.FoundationalUnicity.UniversalModalGround g ∧ ∀ g', Logos.FoundationalUnicity.UniversalModalGround g' → g' = g
  sovereign_freedom : ActsFreely S T
  omniscience : (∀ w_alt, S.Accessible S.actualWorld w_alt → (¬ S.InstantiatedIn w_alt ∨ S.ConfigurationIn w_alt ≠ S.ConfigurationIn S.actualWorld) → T.ApprehendsAlternative T.ground w_alt) ∧
                (∀ w_alt, S.Accessible S.actualWorld w_alt → T.ReasonsFavor T.ground S.actualWorld w_alt)
  intentionality : SelectsIntentionally S T
  trinitarian_communion : ∃ a b c : Logos.Agency.Subject,
    Logos.TrinitarianSubjectBridge.DivineSubjectRole a = Logos.TrinitarianSubjectBridge.DivineRole.source ∧
    Logos.TrinitarianSubjectBridge.DivineSubjectRole b = Logos.TrinitarianSubjectBridge.DivineRole.word ∧
    Logos.TrinitarianSubjectBridge.DivineSubjectRole c = Logos.TrinitarianSubjectBridge.DivineRole.spirit ∧
    Logos.Person.Person a ∧ Logos.Person.Person b ∧ Logos.Person.Person c
```

### Coverage in `logos4`:
1. **Aseity:** Covered (combining metaphysical necessity and nature invariance across worlds).
2. **Transcendence:** Covered (structural externality of the ground relative to the cosmos).
3. **Immanence:** Covered (concrete grounding of the actual world).
4. **Unicity:** Covered (formal unicity of the universal modal ground).
5. **Sovereign Freedom:** Covered (positive libertarian freedom and counterfactual choice).
6. **Omniscience:** Covered (apprehension of all counterfactual worlds and normative reasons).
7. **Intentionality:** Covered (action guided by reason-favoring).
8. **Trinitarian Communion:** Covered (tri-personal relational communion via declared structural roles).

---

## 4. The Specific Attributes Omitted in `logos4`

The comparison reveals 10 major theistic attributes present in `logos` that are absent from `logos4`:

### 1. Divine Simplicity (*Simplicitas Dei*)
- **In `logos`:** Formalized in `DivineClassicalAttributes.lean:711–950`. Establishes:
  - *Mereological Non-Compositeness:* `NonComposite e ↔ CanonicalAseity e` (no external grounding parts).
  - *Zero Internal Decomposition:* `ofGround_has_no_internal_components` (the ground has no structural parts).
  - *Undivided Essence:* `ofGround_undivided_meaning`.
  - *Sole Bearer Theorem:* `divine_simplicity_sole_bearer` proves the ground is the *only* simple entity in reality.
- **In `logos4`:** Completely absent.

### 2. Divine Immutability (*Immutabilitas Dei*)
- **In `logos`:** Formalized in `DivineClassicalAttributes.lean:1008–1250`. Proves a 4-fold invariance:
  - *Modal Invariance:* Unchanging existence across all worlds.
  - *Stage Invariance:* Unchanging existence across all temporal stages.
  - *Transition Invariance:* Outside all state-transitions and process-becoming (`Initiates`).
  - *Capacity Invariance:* Constant meaning-capacity.
- **In `logos4`:** Only modal invariance is partially captured in `NatureInvariant`. Temporal, transition, and capacity invariance are omitted.

### 3. Eternity and Atemporality (*Aeternitas*)
- **In `logos`:** Formalized in `DivineClassicalAttributes.lean:104–350`:
  - `Everlasting Entity.ofGround`: Exists across all temporal stages `∀ t : Time, ExistsAtTime t .ofGround`.
  - `Atemporal Entity.ofGround`: Existence is completely unmodulated by time (`ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e`).
  - `NotInSuccession Entity.ofGround`: Outside any temporal succession or transition sequence.
- **In `logos4`:** Completely absent. `logos4` lacks the temporal sort `Time` and the stage projection apparatus.

### 4. Pure Actuality (*Actus Purus*)
- **In `logos`:** Formalized in `DivineClassicalAttributes.lean:2330–2610`:
  - Proves the complete exclusion of passive potentiality:
    - Zero existential potency (`ofGround_no_existential_potency`);
    - Zero grounding potency (`ofGround_no_grounding_potency`);
    - Zero transition potency (`ofGround_no_transition_potency`);
    - Zero intentional potency (`ofGround_no_intentional_potency`).
- **In `logos4`:** Absent. While `ActsFreely` establishes active choice, the metaphysical perfection of *Actus Purus* (zero passive potency) is omitted.

### 5. Foundational Omnipotence (*Omnipotentia*)
- **In `logos`:** Formalized in `DivineClassicalAttributes.lean:2720–3050`:
  - `ofGround_foundational_omnipotence`: Power over whatever does not imply a contradiction (Aquinas *ST* I q. 25 a. 5 ad 1).
  - Proves `ofGround_gapless_operative_scope` and `ofGround_does_not_operate_contradictions`.
- **In `logos4`:** Absent. Operative power across possible configurations is not formalized.

### 6. Divine Love and Agape (*Caritas Dei*)
- **In `logos`:** Formalized in `DivineClassicalAttributes.lean:3640–4000` and `DivineTrinitarianAttributes.lean:2100–2250`:
  - `the_ground_is_a_necessary_and_chosen_lover`: The ground holds a directional good toward contingent reality (`poem.txt:24`).
  - Requires the declared bridge axiom `AxGroundLovesContingentRealm`.
- **In `logos4`:** Absent. `logos4` currently contains no directional benevolence predicate or love axiom.

### 7. Precedence over Right/Wrong Distinction
- **In `logos`:** Formalized in `DivineTrinitarianAttributes.lean:800–1090`:
  - Proves `ofGround_precedes_the_right_wrong_distinction`: the Ground obtains in worlds where no atomic truth obtains, conditioning all normative reality without being an individual moral subject.
- **In `logos4`:** Absent.

### 8. Exclusion of Pantheism
- **In `logos`:** Formalized in `DivineClassicalAttributes.lean:4720–4780`:
  - `the_ground_is_not_the_universe`: Refutes the identity between the ground and the cosmic totality of entities.
- **In `logos4`:** Absent. While transcendence asserts externality, the formal refutation of pantheistic identity is not stated as a theorem.

### 9. Divine Incorporeality (*Incorporeitas*)
- **In `logos`:** Formalized in `DivineClassicalAttributes.lean:2549`:
  - `ofGround_incorporeal`: Proves the ground is strictly non-physical and disjoint from any atomic matter.
- **In `logos4`:** Absent.

### 10. Anti-Quaternity (Not an Individual Person-Correlate)
- **In `logos`:** Formalized in `DivineClassicalAttributes.lean:4685`:
  - `ofGround_not_a_person_correlate`: The ground is personal essence, but is *not* a fourth chooser alongside Father, Word, and Spirit.
- **In `logos4`:** Partially protected by types, but not explicitly stated as a theorem.

---

## 5. Axiom Footprint and Infrastructure Prerequisites

If these missing attributes are to be integrated into `logos4`, their exact epistemic status and technical prerequisites must be respected:

| Attribute | Epistemic Classification | Axiom Cost | Technical Prerequisites in `logos4` |
|---|---|---|---|
| **Divine Simplicity** | `✅ PROVEN` (conditional) | 0 substantive (under `SemanticFinitude` VOCAB) | Needs mereological non-compositeness and internal component definitions |
| **Divine Immutability** | `✅ PROVEN` | 0 substantive (VOCAB only) | Needs state-transition predicates and stage invariance |
| **Eternity & Atemporality**| `✅ PROVEN` | 0 substantive (VOCAB only) | **Requires temporal stage infrastructure:** `Time`, `stageOf t : World`, `ExistsAtTime` |
| **Pure Actuality** | `✅ PROVEN` (conditional) | 0 substantive (VOCAB only) | Needs passive potency exclusion predicates |
| **Foundational Omnipotence**| `✅ PROVEN` | 0 substantive (VOCAB only) | Needs `OperatesAt` modal operator and contradiction filtering |
| **Divine Incorporeality** | `✅ PROVEN` | 0 substantive (VOCAB only) | Needs disjointness from atomic entities |
| **Exclusion of Pantheism** | `🧱 COUNTERMODEL` / `PROVEN` | 0 substantive | Needs universe totality definition `Universe e := ∀ w x, ExistsAt w x → e = x` |
| **Precedence to Right/Wrong**| `✅ PROVEN` | 0 substantive | Needs atomic world falsity condition |
| **Divine Love (Agape)** | `⚠️ AXIOMATIC` | 1 substantive axiom (`AxGroundLovesContingentRealm`) | Needs `GroundBearsGood` VOCAB and `AxGroundLovesContingentRealm` bridge |
| **Causal Omnipotence** | `◆ AXIOM` | 1 substantive axiom (`ground_produces_every_satisfiable_form`) | Needs `Produces` relation and production bridge |

---

## 6. Strategic Recommendations

Why did `logos4` omit these originally?  
`logos4` was constructed with a clean, focused architectural objective: **isolate the master deduction of the Free Personal Source from ontological incompleteness within 4 elegant modules**, shedding the 8,500 lines of historical controversy, temporal stage scaffolding, and auxiliary mereology present in `logos`.

### Three Pathways Forward:

1. **Pathway A (Keep `logos4` Focused as the Master Eliminative Engine):**
   - Keep `logos4` as it is: the cleanest, fastest, and most robust verification of the Free Personal Source from Ontological Incompleteness (8 core characteristics, 4 clean modules, sub-second kernel build).
   - Reference `~/logos` (or `investigations/ledger.md`) as the comprehensive classical theological encyclopedia.

2. **Pathway B (Surgically Port the Zero-Axiom Classical Attributes):**
   - Formalize the key zero-substantive-axiom attributes directly into `logos4/formal/Logos/Source.lean` without importing heavy temporal infrastructure:
     - **Divine Simplicity** (non-composite, undivided);
     - **Pure Actuality** (absence of passive potency);
     - **Foundational Omnipotence** (gapless operative power over non-contradictory configurations);
     - **Divine Incorporeality** (immaterial, disjoint from physical atoms);
     - **Exclusion of Pantheism** (the ground is not the cosmic totality).
   - This elevates `DivineReality` from 8 to 13 characteristics **without adding a single substantive axiom** and keeping the 4-module build clean.

3. **Pathway C (Full Classical Theistic Parity):**
   - Port the complete temporal apparatus (`Time`, `stageOf`), the divine love bridge (`AxGroundLovesContingentRealm`), and the complete 40-row ledger into `logos4`.
   - *Note:* This would significantly increase the size and complexity of `logos4`, reintroducing historical axioms that were deliberately pruned.

---

## 7. Conclusion

`logos4` did not miss anything by defect; it was streamlined by design. However, from the standpoint of classical philosophical theology (Aquinas, Augustine, Anselm), **Simplicity, Immutability, Actus Purus, Omnipotence, Eternity, and Incorporeality** are quintessential divine attributes that exist in `~/logos` and could enrich `logos4` tremendously if ported via Pathway B.
