# Γ — The Deduction

## The Argument at a Glance

This deduction establishes the complete philosophical arc from the performative attempt to deny objective Right and Wrong to the ultimate personal ground, exposing the exact formal status, substantive axiom footprint, and mathematical frontiers at every step.

Central Distinction: Epistemic Discovery (Right/Wrong reveals Person) operates in reverse of Ontological Grounding (Person grounds Right/Wrong).

```text
RIGHT / WRONG
  Right and wrong both obtain: the binary normative distinction is real.
  ⊢ Right ≠ Wrong ∧ EstablishedRightWrong : Prop := ¬N_T ∧ ¬N_F
  *[PROVEN · 0 substantive axioms]*
        ▲
        │ [Retorsive Defense Against Skeptical Denial]
        │ ⊢ ClaimsCorrect(s, NoRight) ∧ NoRight → ⊥ [NoRight ≡ ¬NormativeRightExists]
        │
        │ [discovery · normative standard specification]
        ▼
OUGHT / OUGHT-NOT
  Objective correctness determines agential standards: Ought vs. Ought-Not.
  ⊢ Ought TruthNorm ⟨s, p⟩ ∧ OughtNot TruthNorm ⟨s, q⟩
  *[PROVEN · 0 substantive axioms]*
        │
        │ [discovery · apprehension of incompatible alternatives]
        ▼
CHOICE
  Apprehending incompatible alternatives and committing constitutes Choice.
  ⊢ Chooses s p q : Prop := Means s p ∧ Means s q ∧ Incompatible p q
  *[PROVEN · 0 substantive axioms]*
        │
        │ [discovery · PURE LOGIC · 0 substantive axioms]
        ▼
FREE WILL
  Freedom is derived by pure logic from genuine normativity and choice.
  ⊢ Chooses s p q ∧ FreeWill(s)
  *[PROVEN · 0 substantive axioms]*
        │
        │ [discovery · definitional equivalence [FreeSubject(s) ≡ FreeWill(s)]]
        ▼
FREE SUBJECT
  A subject is recognized as free in virtue of possessing Free Will.
  ⊢ FreeSubject(s) ≡ FreeWill(s)
  *[PROVEN · 0 substantive axioms]*
        │
        │ [discovery · constitutive theorem [Person := FreeSubject]]
        ▼
PERSON
  A free subject is constitutively an authoritative Person.
  ⊢ Person s : Prop := FreeSubject s
  *[PROVEN · 0 substantive axioms]*
        │
        │ [discovery · numerical individuation [will_individuation]]
        ▼
INDEPENDENT PERSONAL WILL
  Distinct persons have numerically distinct wills (subjectWill s₁ ≠ subjectWill s₂).
  ⊢ Person(s) ↔ FreeIndependentWill(s)
  *[PROVEN · 0 substantive axioms]*
        │
        │ [GROUNDING · ONTOLOGICAL GROUNDING ARROW [Grounding ≠ Identity]]
        ▼
ONTOLOGICAL GROUND OF RIGHT / WRONG
  Personal free agency ontologically grounds the normative order (Grounding ≠ Id).
  ⊢ GroundsJudicativePolarity s p : Prop := GroundProp (EntityOf s) (DeonticOpposition (Correct s p) (Incorrect s p))
  *[PROVEN · 0 substantive axioms]*
  *[Anti-Self-Legislation: identifying Ought with current will collapses normativity (NORMATIVE COLLAPSE). Hostile Impersonal Model confirms bare ought consistent without a second person (SURVIVING PLATONIST MODEL). Under second-personal address and plurality (AxSecondPersonalAddress META / AxTwoSubjects META), objective ought derives distinct persons.]*
        │
        │ [continuation · modal continuation from normative truth]
        ▼
NECESSARY TRUTH
  The objective logical and normative order entails necessary truth.
  ⊢ □ τ : Prop
  *[PROVEN · 0 substantive axioms]*
        │
        │ [continuation · truthmaker grounding [AxGlobalGround (SEM)]]
        ▼
NECESSARY REALITY
  Necessary truth requires an ontological grounder: a necessary entity.
  ⊢ ∃ e, NecessaryEntity(e) ∧ Ground(e, τ) [requires: AxGlobalGround (SEM)]
  *[SEMANTIC [requires: AxGlobalGround (SEM)]]*
        │
        │ [continuation · ontological reality grounding & agential transmission [AxRealityGrounding, agential_grounding_transmission (SEM)]]
        ▼
NECESSARY PERSONAL GROUND
  The necessary ground must possess the Divine Personal Nature (One God ≠ One Person).
  ⊢ ∃ g, NecessaryPersonalGround g
  *[DEFINITIONAL]*
        │
        ├─── [DERIVED THEOREM · DIVINE] → NECESSARY PERSON (Divine Person)
        │     ⊢ ∃ s, NecessarySubject(s) ∧ Person(s)
        │     *[DEFINITIONAL]*
        │
        ├─── [DIVINE UNIQUENESS · g₁=g₂] → ONE GOD / STRICT MONOTHEISM
        │     ⊢ Monotheism
        │     *[DEFINITIONAL]*
        │
        └─── [COUNTERMODEL SEPARATION FRONTIERS] → WHAT THIS DOES NOT YET PROVE
              ⊢ preceding_theory ⇏ trinity | necessary_ground ⇏ contingent_creation
              *[COUNTERMODEL · ⇏]*
                   │
                   │ [COUNTERMODEL SEPARATION FRONTIERS]
                   ▼
              THEOLOGICAL FRONTIERS
                *[COUNTERMODEL · ⇏]*
```

## 1. Objective Right and Wrong

The deduction begins with the objective distinction between Right and Wrong (Right ≠ Wrong). Objective normative distinction is real: neither all propositions are true nor all are false (¬N_T ∧ ¬N_F), and rational judgment constitutively presupposes an objective standard of correctness.

The main reader should first understand WHAT is established: the reality of the normative distinction itself. The performative retorsion is a supporting investigation explaining HOW the normative datum is defended against skeptical denial.

*(Detailed technical proof & model analysis: [investigations/right-and-wrong.md](investigations/right-and-wrong.md))*

Right and wrong both obtain: it is false that nothing is true, and false that everything is true.

    ∴ ¬N_T ∧ ¬N_F

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `Core.lean#rightWrongDistinction`)*

The Established Right/Wrong Distinction: The binary normative distinction is real

    ∴ EstablishedRightWrong ≡ ¬N_T ∧ ¬N_F

    [DEFINITIONAL]
    *(Formal certification: Lean: `IndubitableNormativeFreeWill.lean#EstablishedRightWrong`)*

### Retorsive Defense Against Skeptical Denial

The attempted denial of objective Right and Wrong (NoRight := ¬NormativeRightExists) refutes itself performatively. Claiming the denial as correct (ClaimsCorrect s NoRight) while the denial is true produces a strict constructive contradiction (claims_correct_no_right_self_refuting). Classical double-negation elimination (Classical.not_not, footprint {CL}) derives that objective Right necessarily exists (performative_normative_denial_establishes_normative_right).

The Fundamental Diagonal Retorsion Theorem: Claiming NoRight as correct while NoRight is true produces a strict, constructive contradiction

    ClaimsCorrect(s, NoRight) ∧ NoRight → ⊥

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `DirectNormativeRetorsion.lean#claims_correct_no_right_self_refuting`)*

Unassertability Theorem: No agent can claim NoRight as correct if NoRight is true

    ∴ ¬∃ s, ClaimsCorrect(s, NoRight) ∧ NoRight

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `DirectNormativeRetorsion.lean#cannot_claim_correct_no_right_and_true`)*

Performative Derivation Theorem: If any agent actually performs a normative correctness claim on NoRight, the thesis NoRight is strictly false

    ∴ ¬NoRight

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `DirectNormativeRetorsion.lean#performative_normative_denial_establishes_normative_right`)*

---

## 2. Ought and Normative Polarity

From objective Right and Wrong, the normative standard is expressed as agential Ought and Ought-Not. Under the objective epistemic TruthNorm, correct judgment implies what the subject ought to affirm, and incorrect judgment implies what the subject ought not to affirm. Correctness and incorrectness constitute a strict deontic opposition between what ought and what ought not to be judged.

Deontic opposition between the positive normative pole (Correct s p) and the negative pole (Incorrect s p)

    ∴ DeonticOpposition(Correct s p, Incorrect s p)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `NormativeOrder.lean#correctness_deontic_opposition`)*

### Supporting Infrastructure: `TruthNorm`

The objective epistemic norm of Truth: truth prescribes affirmation, and falsity prohibits affirmation

    ∴ TruthNorm ≡ T(a).content prohibits a := IsFalse(a).content incompatible a := fun ⟨hT, hF⟩ => hF hT

    [DEFINITIONAL]
    *(Formal certification: Lean: `NormativeOrder.lean#TruthNorm`)*

### Supporting Infrastructure: `correct_implies_ought`

A correct judgment act implies that the subject ought to affirm the content under TruthNorm

    ∴ Ought TruthNorm ⟨s, p⟩

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `NormativeOrder.lean#correct_implies_ought`)*

### Supporting Infrastructure: `incorrect_implies_oughtNot`

An incorrect judgment act implies that the subject ought not to affirm the content under TruthNorm

    ∴ OughtNot TruthNorm ⟨s, p⟩

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `NormativeOrder.lean#incorrect_implies_oughtNot`)*

---

## 3. Genuine Choice

Genuine normativity between incompatible alternatives requires that the agent cognitively grasps both options. Apprehending incompatible alternatives and selecting between them is the constitutive definition of rational choice: the agent co-means both incompatible contents in thought while committing to one.

*(Detailed technical proof & model analysis: [investigations/contrastive-choice.md](investigations/contrastive-choice.md))*

Deliberate choice entails genuine choice in the co-meaning sense

    ∴ Chooses(s, p, q)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `Choice.lean#deliberateChoice_implies_chooses`)*

### Supporting Infrastructure: `Chooses`

`Chooses s p q`: strong choice: the subject co-means incompatible alternatives

    ∴ Chooses ≡ Means(s, p) ∧ Means(s, q) ∧ Incompatible(p, q)

    [DEFINITIONAL]
    *(Formal certification: Lean: `Choice.lean#Chooses`)*

### Supporting Infrastructure: `incompatible_self_negation`

Every proposition is incompatible with its own negation.

    ∴ Incompatible(p, ¬p)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `Choice.lean#incompatible_self_negation`)*

---

## 4. Free Will

We did not assume a free subject. Free Will is not assumed as an initial axiom; the argument derives it as an unavoidable theorem. From the reality of genuine normative address and rational choice, Free Will follows from Genuine Normativity by pure logic with zero substantive axioms. A subject endowed with the capacity to choose between incompatible alternatives possesses Free Will by definition.

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

The Shortest Complete Master Proof: Genuine Normativity derives Choice and Free Will

    ∴ Chooses(s, p, q) ∧ FreeWill(s)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `IndubitableNormativeFreeWill.lean#indubitable_normative_free_will`)*

### Supporting Infrastructure: `freeWillExists_of_chooses`

Freedom exists as soon as a genuine choice witness is supplied. This is the formal shape of the target `freeWillExists`; it is *conditional* because the unconditional witness is exactly the blocked `rejectedHornCoMeant`.

    ∴ ∃ s, FreeWill(s)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `Choice.lean#freeWillExists_of_chooses`)*

---

## 5. The Free Subject

A subject is definitionally a free subject if and only if it possesses free will (FreeSubject(s) ↔ FreeWill(s), Iff.rfl). The subject is recognized here as a Free Subject because it possesses Free Will. We do NOT derive Free Will from the existence of the subject; rather, the free subject is introduced only after Free Will is established.

FreeSubject and FreeWill are definitionally equivalent.

    ∴ FreeSubject(s) ↔ FreeWill(s)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `Choice.lean#freeSubject_iff_freeWill`)*

### Supporting Infrastructure: `chooses_implies_freeSubject`

Genuine choice entails a free subject — by definition.

    ∴ FreeSubject(s)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `Choice.lean#chooses_implies_freeSubject`)*

---

## 6. Person

In the unified Γ ontology, Personhood is defined constitutively: a Person is a subject possessing genuine free will (Person(s) := FreeSubject(s)). Personhood is not an opaque or unprovable predicate; every Free Subject is proven to be an authoritative Person by pure deduction (free_subject_is_person, 0 substantive axioms). This is the first point at which the personal subject properly enters the main deduction.

*(Detailed technical proof & model analysis: [investigations/divine-personhood.md](investigations/divine-personhood.md))*

Master Theorem: Every Free Subject is a Person

    ∴ Person(s)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `Person.lean#free_subject_is_person`)*

### Supporting Infrastructure: `person_iff_freeSubject`

Master Equivalence: Personhood is constitutively equivalent to Free Subjecthood

    ∴ Person(s) ↔ FreeSubject(s)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `Person.lean#person_iff_freeSubject`)*

### Supporting Infrastructure: `person_has_free_will`

Every Person possesses Free Will

    ∴ FreeWill(s)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `Person.lean#person_has_free_will`)*

---

## 7. Personal and Independent Will

We distinguish carefully between: (1) the subject possessing a Will; (2) the faculty of will (subjectWill s); (3) the act of willing (Wills s p); and (4) the capacity of free choice (FreeWill s). By the principle of numerical individuation (will_individuation), distinct subjects possess numerically distinct faculties of will (subjectWill s₁ ≠ subjectWill s₂). A Person is constitutively a subject with a free will that is genuinely its own, not numerically identical with another subject's will (Person(s) ↔ FreeIndependentWill(s), 0 substantive axioms).

Master Equivalence: Personhood is constitutively equivalent to Free, Independent Will

    ∴ Person(s) ↔ FreeIndependentWill(s)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `Person.lean#person_iff_freeIndependentWill`)*

### Supporting Infrastructure: `independent_will_of_subject`

Numerical individuation guarantees that every subject possesses an independent will

    ∴ IndependentWill(s)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `Person.lean#independent_will_of_subject`)*

### Supporting Infrastructure: `person_has_free_independent_will`

Master Theorem: Every Person possesses a Free, Independent Will

    ∴ FreeIndependentWill(s)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `Person.lean#person_has_free_independent_will`)*

---

## 8. Personal Agency as Ontological Ground of Normativity

Here the argument reverses the direction: personal free agency is the ontological ground of the Right/Wrong distinction (person_grounds_normative_polarity, under AxPersonalNormativeGround (SEM)).

### Discovery vs. Ontological Grounding
* **Discovery direction:** The argument discovers personal agency FROM normative reality (Right/Wrong → Ought → Choice → Free Will → Free Subject → Person).
* **Ontological grounding direction:** Once Person / Free Will has been established, the ontological relation runs in reverse: Person / Free Independent Will → grounds → Right/Wrong.

These two relations are strictly distinct. Grounding is not causal generation and not identity (Grounding ≠ Identity): identifying Ought with current volition collapses normative violation (will_identity_collapses_normativity). Bare model theory confirms that a free subject does not analytically entail personal grounding without an explicit semantic bridge (Model B separation).

*(Detailed technical proof & model analysis: [investigations/grounding.md](investigations/grounding.md))*

Master Grounding Theorem from Personhood: Every Person performing a judgment act constitutes the judicative normative polarity

    ∴ GroundsJudicativePolarity(s, p)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `PersonalNormativeGround.lean#person_grounds_normative_polarity`)*

Non-Circularity Architectural Theorem: The retorsive discovery proof of Free Will (`indubitable_normative_free_will`) does NOT require or depend upon the grounding bridge `AxPersonalNormativeGround`

    ∴ Chooses(s, p, q) ∧ FreeWill(s)

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `PersonalNormativeGround.lean#discovery_independent_of_grounding`)*

### Obstruction / Formal Boundary: `model_b_separation`

Theorem: Separation Theorem from Model B

    model_b_separation ⇏ Independence

    [COUNTERMODEL | model_b_separation ⇏ Independence]
    *(Formal certification: Lean: `PersonalNormativeGround.lean#model_b_separation`)*

---

## 9. Necessary Truth

Only after normative reality has been established and its personal grounding explained does the document move to Necessary Truth (∃ τ, □ τ). Necessary truth is not an unrelated parallel argument accidentally appended to the personal argument; it reads as the modal continuation of the already-established objective normative and logical order.

Step 1: Strong Necessary Truth exists (resident in Core/Semantics, C59)

    ∴ ∃ τ, □ τ

    [PROVEN | 0 substantive axioms]
    *(Formal certification: Lean: `NecessaryPersonalGround.lean#step1_necessary_truth_exists`)*

### Supporting Infrastructure: `groundPrinciple_atom`

Every atomic truth is grounded: where an atom is true, an entity exists there that grounds it.

    ∴ w ⊨ atom(n) → ∃ e, ExistsAt(w, e) ∧ Ground(e, atom(n))

    [SEMANTIC [requires: Truthmaker (SEM)]]
    *(Formal certification: Lean: `Truthmaker.lean#groundPrinciple_atom`)*

---

## 10. Necessary Reality

Truth does not float ungrounded. By the truthmaker principle, necessary truth entails the existence of a necessary reality: an entity that exists in every possible world and rigidly grounds necessary truth (T7_necessaryReality, under AxGlobalGround (SEM)). The formal dependency on AxGlobalGround is stated explicitly and honestly.

T7 — necessary truth forces necessary reality (base.txt T7).

    ∴ ∃ e, NecessaryEntity(e) ∧ Ground(e, τ)

    [SEMANTIC [requires: AxGlobalGround (SEM)]]
    *(Formal certification: Lean: `Modal.lean#T7_necessaryReality`)*

### Supporting Infrastructure: `AxGlobalGround`

AxGlobalGround (SEM): a formula true in every world is grounded by a single entity that exists in every world.

    ∴ ∀ φ, □ φ → ∃ e, ∀ w, ExistsAt(w, e) ∧ Ground(e, φ)

    [SEMANTIC [requires: AxGlobalGround (SEM)]]
    *(Formal certification: Lean: `Modal.lean#AxGlobalGround`)*

---

## 11. Necessary Personal Ground

The culmination of the ontological deduction. The target is NOT merely a NecessaryEntity(g), NOT merely NecessaryEntity(g) ∧ Personal(g), and NOT merely Ground(g, τ). The target is specifically a necessary ground of all reality realizing personal agency: NecessaryPersonalGround(g). We strictly distinguish three concepts: Necessary Entity (NecessaryEntity e) ≠ Personal Ground (Personal e) ≠ Necessary Personal Ground (NecessaryPersonalGround g), as well as the three ontological levels: Necessary Personal Reality (historical T8, Claim C) ≠ Necessary Ground of Reality (Claim D) ≠ Necessary Personal Ground of Reality (Claim E). By T7 and AxRealityGrounding (GAPMAP C130), the necessary ground of truth ontologically grounds reality; by personal-logical inseparability (§24b), explanatory adequacy (atom_cannot_ground_person), and agential grounding transmission (SEM), the ground of personal agents realizes personal agency (necessary_personal_ground_derived under AxRealityGrounding, agential_grounding_transmission, and AxGlobalGround).

### Strict Monotheism and Personal Plurality
ONE GOD ≠ ONE PERSON. We do NOT define God as the entity-correlate of one Person in a way that collapses the Godhead. The desired architecture remains: ONE NECESSARY DIVINE REALITY / ONE DIVINE NATURE, with THREE NUMERICALLY DISTINCT PERSONS and THREE NUMERICALLY DISTINCT WILLS (monotheism_compatible_with_trinity, 0 substantive axioms). The Necessary Personal Ground establishes the personal character of the necessary divine reality; it does not by itself constitute the complete proof of the Trinity.

*(Detailed technical proof & model analysis: [investigations/divine-personhood.md](investigations/divine-personhood.md))*

### Branch A: Necessary Divine Person

From the necessary personal ground, the reality of a Necessary Person possessing the Divine Nature follows directly (Claim E → Claim D, 0 substantive axioms beyond ground infrastructure).

### Branch B: Divine Uniqueness and Monotheism

The uniqueness of the ultimate ground entails strict monotheism (g₁ = g₂). This monotheism is formally proven to be fully compatible with three distinct personal centers and wills (monotheism_compatible_with_trinity, 0 substantive axioms).

### Branch C: What This Does Not Yet Prove (Theological Frontiers)

The power of a formal system lies as much in what it refrains from claiming as in what it proves. The deduction strictly distinguishes established theorems from open frontiers. Machine-checked independence countermodels prove that preceding theory does NOT logically entail: (1) The Trinitarian structure of Three Divine Persons; (2) Contingent creation of a temporal cosmos; or (3) The Incarnation. These remain independent theological frontiers.

For deep technical proofs, countermodel models, and exhaustive dependency matrices, consult the specialized investigations:
* [Retorsive Defense and Normative Polarity](investigations/right-and-wrong.md)
* [Contrastive Choice and Free Will](investigations/contrastive-choice.md)
* [Free Will Theorem & Derivations](investigations/free-will.md)
* [Ontological Grounding and Model Separations](investigations/grounding.md)
* [Divine Personhood and Monotheism](investigations/divine-personhood.md)
* [Countermodels and Independence Proofs](investigations/countermodels.md)
* [Theological Frontiers: Trinity](investigations/trinity.md)
* [Theological Frontiers: Creation](investigations/creation.md)
* [Theological Frontiers: Incarnation](investigations/incarnation.md)
* [Plurality and Love](investigations/plurality-and-love.md)
* [Kernel Axiom Audit & Footprint Ledger](investigations/kernel-audit.md)

*(Detailed technical proof & model analysis: [investigations/countermodels.md](investigations/countermodels.md))*

#### Obstruction / Formal Boundary: `preceding_theory_not_entails_trinity`

Binitarian Separation Model (Toy Cardinality Model over Bool): Demonstrates that an unconstrained 2-element domain (`Subj := Bool`) cannot accommodate three distinct personal centers by pure cardinality (Pigeonhole Principle).

    preceding_theory ⇏ trinity

    [COUNTERMODEL | preceding_theory ⇏ trinity]
    *(Formal certification: Lean: `ConditionalTheology.lean#preceding_theory_not_entails_trinity`)*

#### Obstruction / Formal Boundary: `necessary_ground_not_entails_contingent_creation`

Acosmic Divine Model: A necessary divine ground exists with zero contingent created reality

    necessary_ground ⇏ contingent_creation

    [COUNTERMODEL | necessary_ground ⇏ contingent_creation]
    *(Formal certification: Lean: `ConditionalTheology.lean#necessary_ground_not_entails_contingent_creation`)*

#### Obstruction / Formal Boundary: `preceding_theory_not_entails_incarnation`

Unincarnate Hostile Model: The existing theory (necessary divine ground, human agency, free will) is completely consistent with God remaining purely transcendent and unincarnate

    preceding_theory ⇏ incarnation

    [COUNTERMODEL | preceding_theory ⇏ incarnation]
    *(Formal certification: Lean: `ConditionalTheology.lean#preceding_theory_not_entails_incarnation`)*

## Further Investigations

### Retorsions

* **Performative_Boundary_Theorem:** `performative_boundary_theorem` (`formal/Logos/A14SemanticAudit.lean`) — PERFORMATIVE BOUNDARY THEOREM: Performative retorsion forces an intentional subject (Considers, Assumes, Derives, Affirms, Rejects) and asymmetric cognitive resolution (SettlementChoice), but strictly stops before executive aiming (AimsAt), action execution…
* **Noact_Conditional_Selfrefutes:** `noAct_conditional_selfRefutes` (`formal/Logos/Agency.lean`) — Asserting NoAct refutes itself under a weak assertion ONLY given the bridge from weak act to strong Act.
* **Nocogito_Selfrefutes:** `noCogito_selfRefutes` (`formal/Logos/Agency.lean`) — Step 4 (C58 strong shortcut): Retorsion — asserting that no act occurs refutes itself
* **Nosubjectsort_Selfrefutes:** `noSubjectSort_selfRefutes` (`formal/Logos/Agency.lean`) — Denying the domain of discourse refutes itself whenever a speaker asserts it.
* **Nosubject_Performative_Selfrefutes:** `noSubject_performative_selfRefutes` (`formal/Logos/Agency.lean`) — C57: Retorsion — asserting that no subject exists refutes itself
* **Nosubject_Selfrefutes:** `noSubject_selfRefutes` (`formal/Logos/Agency.lean`) — C57 canonical theorem name in Agency.
* **Noweakact_Selfrefutes:** `noWeakAct_selfRefutes` (`formal/Logos/Agency.lean`) — Step 4 (weak retorsion): Asserting that no performed event occurs refutes itself directly
* **Level_3_Retorsion_Impotent_Without_Semantic_Premise:** `level_3_retorsion_impotent_without_semantic_premise` (`formal/Logos/BipolarityRetorsion.lean`) — Level 3: Retorsive Impotence of Bare Denial
* **Nochoicefield_Selfrefutes:** `noChoiceField_selfRefutes` (`formal/Logos/Choice.lean`) — C53 (field form): performative retorsion — asserting that no choice field exists refutes itself. Footprint: `{Initiates, Means, State, Subject}` (VOCAB only; zero AxTwoSubjects).
* **Nostrongtruth_Assertable_Refutes:** `noStrongTruth_assertable_refutes` (`formal/Logos/Choice.lean`) — No one can assert "there is no strong truth": the act of denying the world-level datum is destroyed by the datum itself (assertive retorsion of C93, completing the retorsion family at the assertion level; footprint {Means, Subject, CL}).
* **Nosubject_Selfrefutes:** `noSubject_selfRefutes` (`formal/Logos/Choice.lean`) — C57: Retorsion — asserting that no actual subject exists refutes itself
* **Selfassertedparadox_Not_Assertable:** `selfAssertedParadox_not_assertable` (`formal/Logos/Choice.lean`) — Candidate D performative retorsion under factive assertion: one cannot truthfully assert Candidate D.
* **Selfdenialofexecutivechoice_Selfrefutes:** `selfDenialOfExecutiveChoice_selfRefutes` (`formal/Logos/Choice.lean`) — The Performative Retorsion Theorem for Executive Choice: Denying executive choice in an assertion is self-refuting
* **Diagonal_Negative_Choice_Coherent:** `diagonal_negative_choice_coherent` (`formal/Logos/DeepContrastiveFrontier.lean`) — Candidate Δ2: Negative self-assertion of determinism is strictly true and non-self-refuting
* **Retorsion_Denial_Does_Not_Commit_To_Content:** `retorsion_denial_does_not_commit_to_content` (`formal/Logos/DefinitiveAgencyFrontier.lean`) — Retorsion Failure Theorem: Asserting "I do not commit to p" reflexively instantiates an assertion of the negation, but does NOT instantiate commitment to p itself
* **Performative_Self_Refutation_Compatible_With_Determinism:** `performative_self_refutation_compatible_with_determinism` (`formal/Logos/DeterministicReductioFrontier.lean`) — Core Independence Result: Performative self-refutation does NOT imply libertarian freedom
* **Self_Denial_Of_Reasoning_Self_Refutes:** `self_denial_of_reasoning_self_refutes` (`formal/Logos/DeterministicReductioFrontier.lean`) — Performative Self-Refutation of Denying One's Own Present Act: If an agent asserts "I am not acting", the factive assertion itself refutes the content
* **Claims_Correct_No_Right_Self_Refuting:** `claims_correct_no_right_self_refuting` (`formal/Logos/DirectNormativeRetorsion.lean`) — The Fundamental Diagonal Retorsion Theorem: Claiming NoRight as correct while NoRight is true produces a strict, constructive contradiction
* **Master_Retorsion_To_Free_Will:** `master_retorsion_to_free_will` (`formal/Logos/DirectNormativeRetorsion.lean`) — Master Retorsive Synthesis: If an agent performs a normative denial of NoRight, then Free Will is established under classical double negation and the constitutive bridge
* **Model_A_Mere_Utterance_Avoids_Claims_Correct:** `model_a_mere_utterance_avoids_claims_correct` (`formal/Logos/DirectNormativeRetorsion.lean`) — Model A Avoidance Lemma: Mere utterance does not satisfy ClaimsCorrect
* **Model_B_Mere_Meaning_Avoids_Claims_Correct:** `model_b_mere_meaning_avoids_claims_correct` (`formal/Logos/DirectNormativeRetorsion.lean`) — Model B Avoidance Lemma: Meaning NoRight without acting on it does not instantiate ClaimsCorrect
* **Retorsion_Nochoice_Self_Refutes:** `retorsion_NoChoice_self_refutes` (`formal/Logos/ExecutiveDeliberativeFrontier.lean`) — Group 1 Theorem: Asserting NoChoice is performatively self-refuting.
* **Retorsion_Nodeliberation_Consistent:** `retorsion_NoDeliberation_consistent` (`formal/Logos/ExecutiveDeliberativeFrontier.lean`) — Group 2 Theorem: Asserting NoDeliberation is completely consistent and non-self-refuting.
* **Retorsion_Nofreewill_Consistent:** `retorsion_NoFreeWill_consistent` (`formal/Logos/ExecutiveDeliberativeFrontier.lean`) — Group 2 Theorem: Asserting NoFreeWill is completely consistent and non-self-refuting.
* **Schema_S4_Satisfiable_And_Non_Self_Refuting:** `schema_S4_satisfiable_and_non_self_refuting` (`formal/Logos/ExecutiveDeliberativeFrontier.lean`) — Schema S4 Theorem: Denying deliberative choice is NOT performatively self-refuting! A deterministic agent can assert with complete truth that it does not deliberate.
* **Trackb_Selfdenialofexecutivechoice_Selfrefutes:** `trackB_selfDenialOfExecutiveChoice_selfRefutes` (`formal/Logos/ExecutiveDeliberativeFrontier.lean`) — Re-verifying the retorsion theorem for executive choice in this module.
* **Denial_Of_Necessary_Ground_Is_Non_Self_Refuting:** `denial_of_necessary_ground_is_non_self_refuting` (`formal/Logos/GroundingFrontier.lean`) — Retorsion Test on Grounding: Asserting "There is no necessary ground" does NOT performatively refute itself
* **Contextual_Retorsion_Datum:** `contextual_retorsion_datum` (`formal/Logos/HardenedInvariance.lean`) — Contextual Retorsion: Denying that any deduction is developed in any context refutes itself performatively when that denial is asserted as a step within an inquiry context.
* **Retorsion_Cannot_Refute_Infinite_Regress:** `retorsion_cannot_refute_infinite_regress` (`formal/Logos/HostileSemantics.lean`) — Separation Theorem 1: Retorsion cannot refute the infinite ground chain under permissive truthmaking
* **Ultimate_Ground_Dilemma:** `ultimate_ground_dilemma` (`formal/Logos/HostileSemantics.lean`) — The Inescapable Dilemma of Grounding Infinite Regress: Either: (Case 1) Truthmaking is permissive / local: the infinite regress survives, and retorsion cannot refute it
* **Retorsion_Does_Not_Imply_Doubt:** `retorsion_does_not_imply_doubt` (`formal/Logos/HostileSemantics.lean`) — Transcendental retorsion holds fully in TwoPersons, yet Cartesian doubt is empty.
* **Neg_G_Consistent_In_Deflationary_Model:** `neg_G_consistent_in_deflationary_model` (`formal/Logos/HostileSemantics.lean`) — Retorsion Failure on ¬G: Asserting ¬G is completely consistent with the performative core
* **Truthmaking_Retorsion_Fails:** `truthmaking_retorsion_fails` (`formal/Logos/HostileSemantics.lean`) — Retorsion Boundary Principle for Truthmaking: Retorsion refutes a denial Q only when asserting Q performatively instantiates the thesis P
* **A6_A7_Synergistic_Forcing:** `A6_A7_synergistic_forcing` (`formal/Logos/JointForcing.lean`) — Synergy Forcing Theorem: A6 (universal_thesis_claims_objectivity) + A7 (transcendental_reflection_intentional) jointly force NonTrivialOntology under the standard retorsive bridges
* **Retorsion_Not_Implies_Choice:** `retorsion_not_implies_choice` (`formal/Logos/JointForcing.lean`) — Cross-Frontier Barrier 2: {A6, A7} (Retorsion) does NOT force AxIntentionalChoice (A1) or FreeWill
* **Canonical_Act_Noi_Proves_P:** `canonical_act_noi_proves_P` (`formal/Logos/NegativeRetorsionAudit.lean`) — Positive Retorsion: Performing an act on NoI proves that an intentional subject exists! Classification: DEFINITIONAL. Footprint: `{}`.
* **Canonical_Asserts_Noi_Selfrefutes:** `canonical_asserts_noi_selfRefutes` (`formal/Logos/NegativeRetorsionAudit.lean`) — The Fundamental Assertive Retorsion: Actually asserting NoI is unconditionally self-refuting (proves False)
* **Canonical_Exists_Asserts_Noi_Selfrefutes:** `canonical_exists_asserts_noi_selfRefutes` (`formal/Logos/NegativeRetorsionAudit.lean`) — Existential Assertive Retorsion: Existence of any assertion of NoI derives False
* **Canonical_Means_Noi_Proves_P:** `canonical_means_noi_proves_P` (`formal/Logos/NegativeRetorsionAudit.lean`) — Positive retorsion: Any subject meaning NoI proves that an intentional subject exists! Classification: DEFINITIONAL. Footprint: `{}`.
* **Canonical_Noi_Implies_Not_Means:** `canonical_noi_implies_not_means` (`formal/Logos/NegativeRetorsionAudit.lean`) — Canonical Fundamental Theorem of Negative Retorsion: Under NoI, no subject can mean NoI
* **Level2_Signature_Asserts_Noi_Selfrefutes:** `level2_signature_asserts_noi_selfRefutes` (`formal/Logos/NegativeRetorsionAudit.lean`) — Signature-generalized Theorem: Asserting NoI refutes itself in any signature
* **Negative_Retorsion_Master_Synthesis:** `negative_retorsion_master_synthesis` (`formal/Logos/NegativeRetorsionAudit.lean`) — Master Synthesis Theorem of the Negative Retorsion Campaign: Collects the definitive machine-checked mathematical conclusions: 1. Bare NoI is satisfiable in isolation (M0, M1)
* **Performed_Denial_Gradient:** `performed_denial_gradient` (`formal/Logos/NegativeRetorsionAudit.lean`) — Master Ladder Theorem of Performed Denial: Demonstrates the exact gradient where retorsion takes effect
* **Regime_M5_Is_Provably_Incoherent:** `regime_M5_is_provably_incoherent` (`formal/Logos/NegativeRetorsionAudit.lean`) — REGIME M5 AUDIT: "NoI is true and someone attempts to mean it." As mandated by the adversarial review advisory, this regime is PROVABLY EMPTY / INCOHERENT: The conjunction `NoI ∧ (∃ s, Means s NoI)` is logically unsatisfiable due to Level 1 retorsion
* **Context_Normative_Truth_Exists:** `context_normative_truth_exists` (`formal/Logos/NormativeTruth.lean`) — Theorem: Context-packaged form of the retorsion theorem
* **Necessary_Normative_Truth_Exists:** `necessary_normative_truth_exists` (`formal/Logos/NormativeTruth.lean`) — Modal Retorsion Theorem: In any modal semantics where the retorsive self-application holds across worlds, normative truth necessarily exists in every world
* **No_Normative_Truth_Is_Self_Refuting:** `no_normative_truth_is_self_refuting` (`formal/Logos/NormativeTruth.lean`) — Theorem: Under self-application, the universal denial of normative truth is strictly self-refuting
* **Normative_Truth_Exists:** `normative_truth_exists` (`formal/Logos/NormativeTruth.lean`) — Theorem: Direct derivation that normative truth necessarily exists from the retorsive self-application
* **Judgment_Of_No_Act_Proves_Act:** `judgment_of_no_act_proves_act` (`formal/Logos/Order.lean`) — The Retorsive Cogito: even the skeptic's denial that any act occurs strictly witnesses that an act occurs. The act cannot be denied without providing the witness that refutes the denial.
* **Asserting_No_Personal_Source_Instantiates_Only_Judging_Subject:** `asserting_no_personal_source_instantiates_only_judging_subject` (`formal/Logos/OughtRetorsion.lean`) — Theorem: Retorsion Boundary on Personal Source
* **Discovery_Independent_Of_Grounding:** `discovery_independent_of_grounding` (`formal/Logos/PersonalNormativeGround.lean`) — Non-Circularity Architectural Theorem: The retorsive discovery proof of Free Will (`indubitable_normative_free_will`) does NOT require or depend upon the grounding bridge `AxPersonalNormativeGround`
* **Retorsion_Proof_Derives_F1B:** `retorsion_proof_derives_F1b` (`formal/Logos/ProofSpecificContrast.lean`) — The Existential Free Will Theorem (F1b) derived from the performative retorsion proof!
* **Bigo_Bigs_Intentional_Synthesis:** `bigO_bigS_intentional_synthesis` (`formal/Logos/Retorsion.lean`) — Synthesis of Big-O / Big-S Retorsion with Intentional Subject: Both absolutes are self-defeating, establishing the irreducible co-existence of the Objective realm, the Subjective realm, and an active IntentionalSubject.
* **Deterministic_Transcendental_Subject_Refutes_Freewill:** `deterministic_transcendental_subject_refutes_freewill` (`formal/Logos/Retorsion.lean`) — Hostile Separation Theorem 1: Weakened retorsion CANNOT derive FreeWill
* **Deterministic_Transcendental_Subject_Refutes_Person:** `deterministic_transcendental_subject_refutes_person` (`formal/Logos/Retorsion.lean`) — Hostile Separation Theorem 2: Weakened retorsion CANNOT derive Personhood
* **Exists_Intentional_Subject_Of_Retorsion:** `exists_intentional_subject_of_retorsion` (`formal/Logos/Retorsion.lean`) — Primary Retorsive Theorem: Existence of an Intentional Subject via Retorsion
* **Exists_Objective_Of_Retorsion:** `exists_objective_of_retorsion` (`formal/Logos/Retorsion.lean`) — Positive Existential Consequence 1 (Something Objective Exists): The objective status of the universal thesis witnesses an intentional-subject-independent item
* **Exists_Subjective_Of_Retorsion:** `exists_subjective_of_retorsion` (`formal/Logos/Retorsion.lean`) — Positive Existential Consequence 2 (Something Subjective Exists): The performative representation of universal objectivity witnesses a Subjective item
* **Not_Everything_Objective:** `not_everything_objective` (`formal/Logos/Retorsion.lean`) — Big-O Retorsion Theorem: It cannot be the case that everything is Objective
* **Not_Everything_Subjective:** `not_everything_subjective` (`formal/Logos/Retorsion.lean`) — Big-S Retorsion Theorem: It cannot be that everything is Subjective (IntentionalSubject-dependent)
* **Pig_Retorsion_Exposes_Premise_Smuggling:** `pig_retorsion_exposes_premise_smuggling` (`formal/Logos/Retorsion.lean`) — Separation Theorem: Bare transcendental reflection does NOT force arbitrary predicates (such as Winged Pig)
* **Retorsion_Boundary_Principle:** `retorsion_boundary_principle` (`formal/Logos/Retorsion.lean`) — Retorsion Boundary Theorem: A retorsion argument succeeds in establishing P from an assertion of denial Q if and only if Q performatively instantiates P
* **Retorsion_Establishes_Affirmation:** `retorsion_establishes_affirmation` (`formal/Logos/Retorsion.lean`) — The fundamental theorem of performative retorsion: If asserting a content `Q` forces `P`, then no agent can consistently assert `Q` if `Q` entails `¬P`
* **Retorsion_No_Act:** `retorsion_no_act` (`formal/Logos/Retorsion.lean`) — Retorsion 1 (DEFINITIONAL): Denying action is performatively self-refuting
* **Retorsion_No_Choicefield:** `retorsion_no_choiceField` (`formal/Logos/Retorsion.lean`) — Retorsion 5 (DEFINITIONAL): Denying the choice field is performatively self-refuting
* **Retorsion_No_Subject:** `retorsion_no_subject` (`formal/Logos/Retorsion.lean`) — Retorsion 4 (DEFINITIONAL): Denying the subject is performatively self-refuting
* **Retorsion_No_Truth:** `retorsion_no_truth` (`formal/Logos/Retorsion.lean`) — Retorsion 3 (LOGICAL): Denying truth is logically and performatively self-refuting
* **Retorsion_No_Weak_Act:** `retorsion_no_weak_act` (`formal/Logos/Retorsion.lean`) — Retorsion 2 (DEFINITIONAL): Denying weak action is performatively self-refuting.
* **Retorsion_Refutes_Denial:** `retorsion_refutes_denial` (`formal/Logos/Retorsion.lean`) — Performative self-defeat: holding `denialContent` as an actual assertion refutes the denial's content.
* **Weakened_Retorsion_Derives_Intentional_Subject:** `weakened_retorsion_derives_intentional_subject` (`formal/Logos/Retorsion.lean`) — Theorem: Weakened retorsion legitimately derives the existence of an Intentional Subject.
* **Winged_Pig_Derived_Of_Pig_Reflection:** `winged_pig_derived_of_pig_reflection` (`formal/Logos/Retorsion.lean`) — Trivial Retorsion Derivation of Winged Pig: If one adopts the question-begging premise, retorsion "proves" the existence of a Winged Pig.
* **Claiming_Denial_Presupposes_Genuine_Normativity:** `claiming_denial_presupposes_genuine_normativity` (`formal/Logos/RetorsiveNormativity.lean`) — The Fundamental Retorsive Presupposition: Claiming the denial of normativity as correct directly instantiates GenuineNormativity
* **Claims_Correct_Is_Act:** `claims_correct_is_act` (`formal/Logos/RetorsiveNormativity.lean`) — Extraction of the intentional act from a claim of correctness.
* **Claims_Correct_Means_Content:** `claims_correct_means_content` (`formal/Logos/RetorsiveNormativity.lean`) — Extraction of the primary meant content from a claim of correctness.
* **Claims_Correct_Presupposes_Normativity:** `claims_correct_presupposes_normativity` (`formal/Logos/RetorsiveNormativity.lean`) — Performative Presupposition of Assertion: Asserting p as correct constitutively instantiates genuine normative governance between p and ¬p for subject s
* **Denial_Of_Genuine_Normativity_Is_Self_Refuting:** `denial_of_genuine_normativity_is_self_refuting` (`formal/Logos/RetorsiveNormativity.lean`) — Theorem: Non-vacuous self-refutation of the denial of GenuineNormativity
* **Normative_Claiming_Denial_Presupposes_Normativity:** `normative_claiming_denial_presupposes_normativity` (`formal/Logos/RetorsiveNormativity.lean`) — The Fundamental Normative Retorsive Presupposition: Claiming the denial of normativity under the normative correctness stance instantiates GenuineNormativity on the judicative poles (Correct vs Incorrect) WITHOUT AxJudicativeBipolarity and without requiring…
* **Normative_Denial_Of_Normativity_Is_Self_Refuting:** `normative_denial_of_normativity_is_self_refuting` (`formal/Logos/RetorsiveNormativity.lean`) — Non-vacuous self-refutation of the denial of GenuineNormativity under the normative correctness stance
* **Normative_Retorsion_Derives_Free_Will:** `normative_retorsion_derives_free_will` (`formal/Logos/RetorsiveNormativity.lean`) — Master Retorsion Route to Free Will without AxJudicativeBipolarity: Normative Denial of GN ⇒ GenuineNormativity ⇒ Chooses ⇒ FreeWill
* **Normative_Retorsion_Derives_Genuine_Normativity:** `normative_retorsion_derives_genuine_normativity` (`formal/Logos/RetorsiveNormativity.lean`) — Performative Derivation Theorem: Under an actual performed denial event with normative correctness awareness, GenuineNormativity is inescapably established with ZERO substantive axioms
* **Retorsion_Derives_Free_Will:** `retorsion_derives_free_will` (`formal/Logos/RetorsiveNormativity.lean`) — The Complete Master Retorsion Route: Denial of GN ⇒ Assertion as Correct ⇒ GenuineNormativity ⇒ Chooses ⇒ FreeWill
* **Retorsion_Derives_Genuine_Normativity:** `retorsion_derives_genuine_normativity` (`formal/Logos/RetorsiveNormativity.lean`) — Performative Derivation Theorem: Under an actual performed denial event, GenuineNormativity is inescapably established
* **Nostrongtruth_Selfrefutes:** `noStrongTruth_selfRefutes` (`formal/Logos/Semantics.lean`) — Denying strong truth refutes itself: it cannot be the case that no formula is necessarily true — the act of denying strong truth is destroyed by strong truth (performative retorsion of C59, footprint {CL}).
* **Denial_Of_Genuine_Choice_Is_Self_Refuting:** `denial_of_genuine_choice_is_self_refuting` (`formal/Logos/StrongActionChoice.lean`) — Theorem: Under RetorsiveAvailability and deliberative settlement, the denial of genuine choice is self-refuting
* **Denial_Of_No_Metaphysical_Alternative_Is_Self_Refuting:** `denial_of_no_metaphysical_alternative_is_self_refuting` (`formal/Logos/StrongActionChoice.lean`) — Theorem: Under the RetorsiveAvailability principle, performing a denial of availability is self-refuting
* **Retorsion_Fails_Against_No_Necessary_Entity:** `retorsion_fails_against_no_necessary_entity` (`formal/Logos/TheologicalModalHardening.lean`) — Retorsion Failure on the denial of necessary reality: An agent asserting `Neg_NecessaryEntityExists` commits no performative contradiction: the agent is actualized at `actualWorld`, but contingent across `World`
* **Noground_Selfrefutes:** `noGround_selfRefutes` (`formal/Logos/Truthmaker.lean`) — The denial that atomic truth is grounded refutes itself under the Truthmaker bridge.
* **Bridge_C_Performative_Judge_Yields_Choice_Field:** `bridge_c_performative_judge_yields_choice_field` (`formal/Logos/UndeniableNormativeDerivation.lean`) — Bridge C: Performative Retorsion Bridge (Judging Act) derives ChoiceField
* **Bridge_D_Retorsion_Derives_Free_Will:** `bridge_d_retorsion_derives_free_will` (`formal/Logos/UndeniableNormativeDerivation.lean`) — Bridge D: Transcendental Retorsion of Genuine Normativity derives Free Will under Judicative Bipolarity (`AxJudicativeBipolarity`)
* [Right and Wrong, Bivalence, and Retorsion](investigations/right-and-wrong.md) — LOGICAL (`{CL}`) / ZERO SUBSTANTIVE AXIOMS

### Countermodels & Independence

* **consequence_A_reasoning ⇏ libertarian:** `consequence_A_reasoning_not_entails_libertarian` (`formal/Logos/AgencyDeterminismConsequences.lean:405`) — Consequence A: Reasoning does NOT logically entail libertarian freedom
* **consequence_B_first_person ⇏ libertarian:** `consequence_B_first_person_not_entails_libertarian` (`formal/Logos/AgencyDeterminismConsequences.lean:430`) — Consequence B: First-person subjectivity does NOT entail libertarian freedom
* **consequence_C_intentionality ⇏ libertarian:** `consequence_C_intentionality_not_entails_libertarian` (`formal/Logos/AgencyDeterminismConsequences.lean:438`) — Consequence C: Intentionality does NOT entail libertarian freedom
* **consequence_D_normativity ⇏ libertarian:** `consequence_D_normativity_not_entails_libertarian` (`formal/Logos/AgencyDeterminismConsequences.lean:446`) — Consequence D: Normativity does NOT entail libertarian freedom
* **D1_discrimination ⇏ choice:** `D1_discrimination_not_entails_choice` (`formal/Logos/CognitiveDiscrimination.lean:207`) — Property D1 (FAILS): Discrimination does NOT entail Choice! Hostile model: s discriminates p from q, but makes no choice.
* **D2_discrimination ⇏ meaning:** `D2_discrimination_not_entails_meaning` (`formal/Logos/CognitiveDiscrimination.lean:216`) — Property D2 (FAILS): Discrimination does NOT entail Representation/Meaning of q! Hostile model: s discriminates p from an external contrast boundary q without meaning q.
* [Complete Catalog of Hostile Models Across Γ](investigations/countermodels.md) — INDEPENDENCE & SEPARATION THEOREMS (Footprint `{}`)

### Detailed Investigations

* [Contrastive Choice, Action, and Axiom A14](investigations/contrastive-choice.md) — SEMANTIC BRIDGE A14 (`AxIntentionalChoice`, Tag: SEM) / INDEPENDENCE THEOREMS (`{}`)
* [Contingent Creation and Teleology](investigations/creation.md) — CONTINGENT FACT / METAPHYSICAL BRIDGE / ACOSMIC MODEL
* [Divine Personhood and the Rejection of Impersonalism](investigations/divine-personhood.md) — METAPHYSICAL BRIDGE (`AxPersonalGround`, A7) / THEOREM T8
* [The Normative Route to Free Will](investigations/free-will.md) — LOGICAL derivation from CONSTITUTIVE SEMANTICS (`{Means, Subject}`, 0 substantive axioms)
* [Truthmaking, Grounding, and Necessary Reality (God)](investigations/grounding.md) — SEMANTIC BRIDGE (`Truthmaker`, `AxGlobalGround`) / THEOREMS T7 & T8
* [The Incarnation — The Builder Entering the House](investigations/incarnation.md) — THEOLOGICAL TELEOLOGICAL BRIDGE / UNINCARNATE MODEL
* [Plurality of Divine Persons and Eternal Love](investigations/plurality-and-love.md) — THEOREMS T12, T13, T14 (`{Means, Subject, AxTwoSubjects}`)
* [The Trinity and the Condilectus Principle](investigations/trinity.md) — CONDITIONAL METAPHYSICAL BRIDGE / BINITARIAN SEPARATION MODEL

### Technical

* [Technical Appendix: Kernel Audit, Consistency & Code Annex](investigations/kernel-audit.md) — Complete kernel audit, transitive axiom footprints, dependency ledger, and consistency checks.
* [Formal Dependency Graph (JSON)](formal/depgraph.json) / [(DOT)](formal/depgraph.dot) — LeanDepViz transitive kernel dependency DAG.
* [Theorem Ledger (GAPMAP)](formal/GAPMAP.md) — Formal correspondence mapping across formal and prose corpora.
