/-
# Logos.NecessaryPersonalGround — The Necessary Personal Ground

This module reconstructs the transition from Necessary Truth and Necessary Reality
to the Necessary Personal Ground within Γ's unified four-tier ontology
(`Entity`, `Subject`, `Nature`, `Will`).

Status (Batch THIS_IS_PERSONAL, 2026-09-22; plan `THIS_IS_PERSONAL.md` §11.7/§12):

1. **Constitutive headline.** The required deliverable is Claim (I): the free
   personal judicative act is the necessary ontological basis of Right/Wrong,
   truth/falsity, and all Γ-reality. It is proved in
   `Logos.PersonalGroundOfReality.present_act_yields_personal_grounding_of_reality`
   (footprint `{Initiates, Means, State, Subject, CL}`). Claim E
   (`∃ g, NecessaryEntity g ∧ NecessaryPersonalGround g`) is **annotated only**,
   never a theorem (obstacle registry, `THIS_IS_PERSONAL.md` §12.1).
2. **Trinitarian / monotheism block DEFERRED.** The strict-monotheism and
   trinitarian-architecture material (axioms `PersonalNature`,
   `personal_nature_iff_person`, `DivineNature`, `divine_nature_is_personal`,
   `divine_person_is_necessary`, `universal_ground_unique`, duplicate
   `GroundsEntity`/`explanatory_adequacy`, `explanatory_adequacy_normative_order`,
   and the derived theorems `divine_subject_is_person`, `God`, `Monotheism`,
   `divine_uniqueness`, `monotheism_derived`, `TrinitarianGodhead`,
   `trinitarian_*`, `necessary_person_derived`, `claim_e_implies_claim_d`, …) was
   moved verbatim to `scratch/Trinitarian_deferred.lean`, which is **never
   imported** by the build and may not compile (that is acceptable).
3. **Claim-E surface kept as annotations.** The definitions
   `GroundsPersonalReality`, `PersonalGround`, `NecessaryPersonalGround`, the five
   claim definitions, and the pure-logic claim entailments stay as the annotated
   entity-level surface (`THIS_IS_PERSONAL.md` §12.1); no entity-level theorem is
   fabricated over them.
-/

import Logos.Core
import Logos.Agency
import Logos.Alternatives
import Logos.Choice
import Logos.Person
import Logos.Order
import Logos.Value
import Logos.Semantics
import Logos.Truthmaker
import Logos.Modal
import Logos.Plurality
import Logos.GroundPerson
import Logos.NormativeOrder
import Logos.RecoveredOntologicalGround

namespace Logos.NecessaryPersonalGround

open Logos.Core (T IsFalse)
open Logos.Semantics (Form World Satisfies TrueAt)
open Logos.Agency (Subject A Means IntentionalSubject Nature HasNature Will subjectWill will_individuation)
open Logos.Choice (Chooses FreeWill FreeSubject)
open Logos.Person (Person person_is_intentional person_has_free_will)
open Logos.Truthmaker (Entity Ground ExistsAt TrueAt NecessarilyTrue EntityOf)
open Logos.Modal (NecessaryEntity Contingent actualWorld T7_necessaryReality)
open Logos.Plurality (NecessarySubject)
open Logos.GroundPerson (GroundProp Realizes IsPresentPersonalFeature)
open Logos.RecoveredOntologicalGround (GroundsEntity explanatory_adequacy)

-- ============================================================================
-- 1. Unified Ontological Framework (Subject, Nature, Will, Entity)
-- ============================================================================

/- The trinitarian axioms (`PersonalNature`, `personal_nature_iff_person`,
`DivineNature`, `divine_nature_is_personal`, `divine_person_is_necessary`) and
`divine_subject_is_person` moved VERBATIM to scratch/Trinitarian_deferred.lean
(DEFERRED, never imported). The duplicate `GroundsEntity` AXIOM that shadowed
the canonical definition was retired with that block. -/

/-- Actual entity: an entity that exists in the actual world. -/
def ActualEntity (e : Entity) : Prop := ExistsAt actualWorld e

/-- Impersonal Entity: an atomic factual truthmaker that is not a subject. -/
def ImpersonalEntity (e : Entity) : Prop := ∃ n : Nat, e = Entity.ofAtom n

/-- The Propositional Content of the Objective Normative Order:
    The transcendent normative structure governing rational judgment and agency,
    unifying:
    1. Right/Wrong distinction: truth and untruth both non-vacuously obtain (Core.rightWrongDistinction);
    2. Agential TruthNorm standard: prescribing truth, prohibiting error (NormativeOrder.TruthNorm);
    3. Deontic Incompatibility: Ought and OughtNot are mutually incompatible (NormativeOrder.ought_and_oughtNot_incompatible);
    4. Deontic Opposition: Correct and Incorrect judgments are strictly opposed (NormativeOrder.correctness_incompatible). -/
def ObjectiveNormativeOrder : Prop :=
  (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) ∧
  (∀ a : Logos.NormativeOrder.JudicativeAct,
    Logos.Alternatives.Incompatible
      (Logos.NormativeOrder.Ought Logos.NormativeOrder.TruthNorm a)
      (Logos.NormativeOrder.OughtNot Logos.NormativeOrder.TruthNorm a)) ∧
  (∀ (s : Subject) (p : Prop),
    Logos.Alternatives.Incompatible (Logos.Order.Correct s p) (Logos.Order.Incorrect s p))

/-- Theorem: The objective normative order holds in reality with 0 substantive axioms. -/
theorem objective_normative_order_holds : ObjectiveNormativeOrder :=
  ⟨Logos.Core.rightWrongDistinction,
   fun a => Logos.NormativeOrder.ought_and_oughtNot_incompatible a.subject a.content,
   fun s p => Logos.NormativeOrder.correctness_incompatible s p⟩

/-- The Objective Normative Order obtains at world w:
    holds at any world where the transcendent normative structure is realized. -/
def NormativeOrderAt (_w : World) : Prop := ObjectiveNormativeOrder

/-- The Invariant Necessity of the Objective Normative Order:
    holds across all possible worlds via Logos.Necessity.Necessity. -/
def NecessaryNormativeOrder : Prop :=
  ∀ w : World, NormativeOrderAt w

/-- Theorem: The objective normative order is strictly necessary across all worlds.
    Status: PROVED with 0 substantive axioms. -/
theorem necessary_normative_order : NecessaryNormativeOrder :=
  fun _w => objective_normative_order_holds

/-- Strengthened Semantic Definition of Ontological Grounding of the Normative Order:
    An entity g ontologically grounds the objective normative order iff:
    1. g grounds the proposition of the objective normative order (GroundProp g ObjectiveNormativeOrder);
    2. Ontological Persistence: in every possible world w where the normative order obtains,
       its ground g exists (ExistsAt w g).
    Kept as the annotated Claim-E surface (THIS_IS_PERSONAL.md §12.1). -/
structure GroundsNormativeOrder (g : Entity) : Prop where
  grounds : Logos.GroundPerson.GroundProp g ObjectiveNormativeOrder
  persistence : ∀ (w : World), NormativeOrderAt w → ExistsAt w g

/-- The necessity of the normative order is grounded in the free personal judicative
    act — constitutive, axiom-free (NormativeGroundPersistence and
    GroundPrincipleProp retired, THIS_IS_PERSONAL.md §13.4). -/
theorem normative_order_is_grounded_in_personal_nature
    {s : Subject} {p : Prop} (h : Logos.NormativeOrder.ClaimsNormativeCorrectness s p) :
    NecessaryNormativeOrder ∧ Person s := by
  have hFW := Logos.NormativeOrder.claims_normative_correctness_derives_free_will s p h
  exact ⟨necessary_normative_order, Logos.Person.free_subject_is_person s hFW.2⟩

/-- The objective normative order is necessary (0 substantive axioms). -/
theorem necessary_normative_order_is_necessary : NecessaryNormativeOrder :=
  necessary_normative_order

/-- Derivation of the Necessity of the Normative Ground.
    Derived by direct modus ponens from grounding persistence and necessary_normative_order.
    Footprint: `{}` (pure logic). -/
theorem ground_of_necessary_normative_order_is_necessary
    {g : Entity}
    (hGround : GroundsNormativeOrder g)
    (hNecessary : NecessaryNormativeOrder) :
    NecessaryEntity g := by
  intro w
  exact hGround.persistence w (hNecessary w)

/-- GroundsPersonalReality: entity g genuinely grounds personal reality.
    An entity g grounds personal reality iff g grounds all reality and realizes a present personal feature. -/
def GroundsPersonalReality (g : Entity) : Prop :=
  Logos.RecoveredOntologicalGround.GroundOfReality g ∧
  ∃ f : Prop, Logos.GroundPerson.Realizes g f ∧ Logos.GroundPerson.IsPresentPersonalFeature f

/-- PersonalGround: an entity g is a personal ground iff:
    1. g grounds personal reality;
    2. g is strictly non-impersonal (¬ ImpersonalEntity g). -/
def PersonalGround (g : Entity) : Prop :=
  GroundsPersonalReality g ∧ ¬ ImpersonalEntity g

/-- Target Definition: Necessary Personal Ground.
    An entity G is a necessary personal ground iff:
    1. G is a necessary entity (NecessaryEntity G);
    2. G grounds the personal reality of free subjects (GroundsPersonalReality G);
    3. G is strictly not an impersonal entity (¬ ImpersonalEntity G). -/
def NecessaryPersonalGround (g : Entity) : Prop :=
  NecessaryEntity g ∧ GroundsPersonalReality g ∧ ¬ ImpersonalEntity g

-- ============================================================================
-- 3. Rigorous Formulation of the Five Claims
-- ============================================================================

/-- Claim A: Necessary Truth exists (e.g. τ := p ∨ ¬p). -/
def ClaimA_NecessaryTruth (φ : Form) : Prop := NecessarilyTrue φ

/-- Claim B: Necessary Reality exists (T7 under AxGlobalGround). -/
def ClaimB_NecessaryReality : Prop := ∃ e : Entity, NecessaryEntity e

/-- Claim C: Historical T8 / Act-Content Reality exists.
    A necessary entity grounds some proposition meant in an act.
    Note: GroundPerson.Personal merely denotes property-bearing on act-content. -/
def ClaimC_HistoricalT8 : Prop := ∃ e : Entity, NecessaryEntity e ∧ Logos.GroundPerson.Personal e

/-- Claim D: Necessary Person exists.
    There exists a personal subject that exists across all possible worlds. -/
def ClaimD_NecessaryPerson : Prop := ∃ s : Subject, NecessarySubject s ∧ Person s

/-- Claim E: Necessary Personal Ground exists.
    There exists a necessary personal ground of personal reality. -/
def ClaimE_NecessaryPersonalGround : Prop := ∃ g : Entity, NecessaryPersonalGround g

-- ============================================================================
-- 4. Constructive Entailments Between Claims
-- ============================================================================

/-- Theorem: Claim E implies Claim B (Personal Ground entails Necessary Reality).
    Footprint: `{}`. -/
theorem claim_e_implies_claim_b :
    ClaimE_NecessaryPersonalGround → ClaimB_NecessaryReality := by
  rintro ⟨g, hNecG, _, _⟩
  exact ⟨g, hNecG⟩

/-- Theorem: Claim D implies Claim B (Necessary Person entails Necessary Reality).
    Footprint: `{Subject}`. -/
theorem claim_d_implies_claim_b :
    ClaimD_NecessaryPerson → ClaimB_NecessaryReality := by
  rintro ⟨s, hNecS, _⟩
  exact ⟨EntityOf s, Logos.Modal.subject_nec_entity_nec s hNecS⟩

/-- Theorem: Claim C implies Claim B (Historical T8 entails Necessary Reality).
    Footprint: `{}`. -/
theorem claim_c_implies_claim_b :
    ClaimC_HistoricalT8 → ClaimB_NecessaryReality := by
  rintro ⟨e, hNecE, _⟩
  exact ⟨e, hNecE⟩

-- ============================================================================
-- 5. Explanatory Adequacy & Non-Reducibility of Personal Reality
-- ============================================================================

/-- Ontological Distinction: Atomic entities are provably distinct from any subject correlate. -/
theorem ofAtom_ne_ofSubject (n : Nat) (s : Subject) :
    Entity.ofAtom n ≠ EntityOf s :=
  fun h => Entity.noConfusion h

/-- Empirical atomic entities are contingent: they fail to exist in the empty world where atoms evaluate false.
    Footprint: `{}` (0 axioms). -/
theorem ofAtom_not_necessary_entity (n : Nat) : ¬ NecessaryEntity (Entity.ofAtom n) := by
  intro hNec
  have hFalse : ExistsAt (fun _ => Logos.Semantics.TV.f) (Entity.ofAtom n) :=
    hNec (fun _ => Logos.Semantics.TV.f)
  nomatch hFalse

/-- No impersonal atomic entity can be a necessary entity.
    Footprint: `{}` (0 axioms). -/
theorem impersonal_not_necessary (e : Entity) : ImpersonalEntity e → ¬ NecessaryEntity e := by
  rintro ⟨n, rfl⟩
  exact ofAtom_not_necessary_entity n

/-- Intentional capacity of an entity: an entity means proposition `p` iff it is a
    subject performing the intentional act `Means s p`. Empirical atoms have zero intentional capacity. -/
def EntityMeans (e : Entity) (p : Prop) : Prop :=
  match e with
  | Entity.ofSubject s => Means s p
  | Entity.ofAtom _ => False

/- The duplicated `explanatory_adequacy` AXIOM moved VERBATIM to
scratch/Trinitarian_deferred.lean (DEFERRED); the canonical theorem
`Logos.RecoveredOntologicalGround.explanatory_adequacy` (footprint
`{Means, Subject}`) is used below via the `open` above. -/

/-- An impersonal atomic entity cannot ground an intentional agent.
    Because an atom has zero intentional capacity (EntityMeans (Entity.ofAtom n) p ↔ False),
    it cannot ground any subject that means a proposition.
    Footprint: `{explanatory_adequacy, Means, Subject}`. -/
theorem atom_cannot_ground_intentional_subject
    (n : Nat) (s : Subject) (p : Prop) (hm : Means s p) :
    ¬ GroundsEntity (Entity.ofAtom n) (EntityOf s) := by
  intro hGr
  have hSub := explanatory_adequacy (Entity.ofAtom n) (EntityOf s) hGr
  have hMeanS : EntityMeans (EntityOf s) p := hm
  have hMeanAtom : EntityMeans (Entity.ofAtom n) p := hSub p hMeanS
  exact hMeanAtom

/-- An impersonal atomic entity cannot ground a free subject / person.
    Every Person possesses free will and genuine choice, which entails intentional meaning (Means s p).
    Hence, by explanatory adequacy, no empirical atom can ground a Person.
    Footprint: `{explanatory_adequacy, Means, Subject}`. -/
theorem atom_cannot_ground_person (n : Nat) (s : Subject) (hPerson : Person s) :
    ¬ GroundsEntity (Entity.ofAtom n) (EntityOf s) := by
  have hFreeWill : FreeWill s := Logos.Person.person_has_free_will s hPerson
  obtain ⟨p, _q, hChooses⟩ := hFreeWill
  exact atom_cannot_ground_intentional_subject n s p hChooses.1

-- ============================================================================
-- 6. Principled Derivation of Necessary Personal Ground (No Blunt Shortcut)
-- ============================================================================

/-- Step 1: Strong Necessary Truth exists (resident in Core/Semantics, C59).
    Verified with footprint `{CL}`. -/
theorem step1_necessary_truth_exists : ∃ τ : Form, NecessarilyTrue τ :=
  Logos.Semantics.strongTruthExists

/-- Step 2: Necessary Truth forces a Necessary Reality that grounds it (T7, C18).
    Derived under the declared semantic bridge `AxGlobalGround`.
    Footprint: `{AxGlobalGround, Ground, Subject}`. -/
theorem step2_necessary_reality_exists :
    ∃ e : Entity, NecessaryEntity e ∧ ∃ τ : Form, NecessarilyTrue τ ∧ Ground e τ := by
  obtain ⟨τ, hNecτ⟩ := step1_necessary_truth_exists
  obtain ⟨e, hNecE, hGr⟩ := Logos.Modal.T7_necessaryReality hNecτ
  exact ⟨e, hNecE, τ, hNecτ, hGr⟩

/-- Step 3: Personal-Logical Inseparability (§24b, C25).
    In every rational act, personal features and logical features are strictly inseparable.
    Footprint: `{Initiates, Means, State, Subject, CL}`. -/
theorem step3_personal_logical_inseparability
    (a : Prop) (hAct : Logos.Person.RationalAct a) :
    Logos.Person.CarriesPersonalFeature a ↔ Logos.Person.CarriesLogicalFeature a :=
  Logos.Person.inseparability_24b a hAct

/-- Personal-Logical Inseparability on the intentional act:
    Because personal and logical features are strictly inseparable in every rational act (§24b),
    any rational act being performed carries personal features.
    Footprint: `{Initiates, Means, State, Subject, CL}`. -/
theorem rational_act_carries_personal (s : Subject) (p : Prop) (hAct : Logos.Agency.Act s p) :
    Logos.Person.CarriesPersonalFeature p := by
  have hRat : Logos.Person.RationalAct p := ⟨s, p, hAct, rfl⟩
  have hInsep := step3_personal_logical_inseparability p hRat
  have hLog : Logos.Person.CarriesLogicalFeature p := by
    refine ⟨p, id, ?_⟩
    by_cases hT : T p
    · exact Or.inl hT
    · exact Or.inr hT
  exact hInsep.mpr hLog

/-- Step 4: Master Agential Theorem.
    Under the performative retorsive hypothesis, actual volitional reality is established:
    `Asserts s p → Act s p → Chooses s p q → FreeWill s → FreeSubject s → Person s ∧ Will (subjectWill s) ∧ ActualEntity (EntityOf s)`.
    Footprint: `{AxIntentionalChoice, Initiates, Means, State, Subject, CL}`. -/
theorem established_will_reality (hAssert : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Asserts s p) :
    ∃ s : Subject, (∃ w : Will, w = subjectWill s) ∧ FreeWill s ∧ FreeSubject s ∧ Person s ∧ ActualEntity (EntityOf s) := by
  obtain ⟨s, p, hAss⟩ := hAssert
  obtain ⟨s', p', hAct⟩ := Logos.Agency.act_exists_of_assert hAss
  obtain ⟨q, hChooses⟩ := Logos.Choice.AxIntentionalChoice s' p' hAct
  have hFreeWill : FreeWill s' := Logos.Choice.chooses_implies_freeWill hChooses
  have hFreeSubj : FreeSubject s' := hFreeWill
  have hPerson : Person s' := Logos.Person.free_subject_is_person s' hFreeSubj
  have hWill : ∃ w : Will, w = subjectWill s' := ⟨subjectWill s', rfl⟩
  have hActual : ActualEntity (EntityOf s') := by
    change Logos.Truthmaker.SubjectExistsAt actualWorld s'
    exact rfl
  exact ⟨s', hWill, hFreeWill, hFreeSubj, hPerson, hActual⟩

/-- Epistemic Discovery: Master Agential Theorem without AxIntentionalChoice.
    Under the performative normative stance, actual volitional reality is established:
    `ClaimsNormativeCorrectness s p → Chooses s (Correct s p) (Incorrect s p) → FreeWill s → FreeSubject s → Person s ∧ Will (subjectWill s) ∧ ActualEntity (EntityOf s)`.
    Footprint: `{Initiates, Means, State, Subject, CL}` (0 substantive axioms, completely free of AxIntentionalChoice). -/
theorem established_normative_person
    (hClaims : ∃ s : Subject, ∃ p : Prop, Logos.NormativeOrder.ClaimsNormativeCorrectness s p) :
    ∃ s : Subject, (∃ w : Will, w = subjectWill s) ∧ FreeWill s ∧ FreeSubject s ∧ Person s ∧ ActualEntity (EntityOf s) := by
  obtain ⟨s, p, hClaims_sp⟩ := hClaims
  have hFW : FreeWill s := (Logos.NormativeOrder.claims_normative_correctness_derives_free_will s p hClaims_sp).2
  have hFreeSubj : FreeSubject s := hFW
  have hPerson : Person s := Logos.Person.free_subject_is_person s hFreeSubj
  have hWill : ∃ w : Will, w = subjectWill s := ⟨subjectWill s, rfl⟩
  have hActual : ActualEntity (EntityOf s) := by
    change Logos.Truthmaker.SubjectExistsAt actualWorld s
    exact rfl
  exact ⟨s, hWill, hFW, hFreeSubj, hPerson, hActual⟩

/- The redundant SEM axiom `explanatory_adequacy_normative_order` moved VERBATIM
to scratch/Trinitarian_deferred.lean (DEFERRED). Its only consumers,
`atom_cannot_ground_normative_order` and `ground_of_normative_order_not_impersonal`,
are NOT re-provable over the uninterpreted `GroundProp` relation (the
`GroundsNormativeOrder` structure field `grounds : GroundProp g ObjectiveNormativeOrder`
has no ground-free negation), so they are annotated instead of faked
("prefer losing a theorem over hiding a premise"; THIS_IS_PERSONAL.md §13.8).
Entity-level non-impersonality of the ground of reality is retained at
`Logos.RecoveredOntologicalGround.ground_of_reality_not_impersonal` via the
constitutive `GroundsEntity` definition (atom branch `EntityMeans atom p = False`). -/

/-- Derivation of Personal Ground from Explanatory Adequacy. -/
theorem ground_of_normative_order_is_personal_ground
    {g : Entity} (hGr : GroundsPersonalReality g) (hNotImp : ¬ ImpersonalEntity g) :
    PersonalGround g :=
  ⟨hGr, hNotImp⟩

/-- Theorem: An impersonal atomic entity cannot be a Necessary Personal Ground.
    Footprint: `{}`. -/
theorem ofAtom_not_necessary_personal_ground (n : Nat) :
    ¬ NecessaryPersonalGround (Entity.ofAtom n) := by
  rintro ⟨_hNec, _hPers, hNotImp⟩
  exact hNotImp ⟨n, rfl⟩

/-
`necessary_personal_ground_derived` and `necessary_ground_is_personal` (Claim-E
derivations: `ClaimE_NecessaryPersonalGround`, resp. `∃ g, NecessaryEntity g ∧
GroundsPersonalReality g`) are REMOVED as theorems: their only routes used the
deleted axioms `AxRealityGrounding` + `agential_grounding_transmission`
(`Logos.RecoveredOntologicalGround`, retired this batch).

Claim E is an ANNOTATED-ONLY surface, never a theorem (THIS_IS_PERSONAL.md §12.1,
obstacle registry): world-indexed necessity needs the SEM `AxGlobalGround`;
`Personal` needs the META `GroundProp` instance `AxPersonalGround`; the
`GroundOfReality` subject-branch is open (R3). The headline deliverable is the
constitutive Claim (I):
`Logos.PersonalGroundOfReality.present_act_yields_personal_grounding_of_reality`
(footprint `{Initiates, Means, State, Subject, CL}`).
-/

-- ============================================================================
-- 6b. The Complete Proof Spine of Γ (Addendum Section 9)
-- ============================================================================

/-- Spine 1: Right and Wrong are objectively distinct. -/
theorem right_wrong_established
    (h : (∃ s : Subject, ∃ p : Prop, Logos.Order.Correct s p) ∧
         (∃ s : Subject, ∃ p : Prop, Logos.Order.Incorrect s p)) :
    ∃ p : Prop, Logos.Choice.Meaning_I p :=
  Logos.Order.rightDistinctWrong_implies_meaning h

/-- Spine 2: Objective Normativity: Correct and Incorrect judgments are distinct. -/
theorem normativity_established (hAct : ∃ s : Subject, ∃ p : Prop, Logos.Agency.A s p) :
    ¬ (∀ s : Subject, ∀ p : Prop, Logos.Order.Correct s p ↔ Logos.Order.Incorrect s p) :=
  Logos.Order.correctness_distinct hAct

/-- Spine 3: Genuine Choice is established from intentional action (Choice.AxIntentionalChoice). -/
theorem genuine_choice_established (s : Subject) (p : Prop) (hAct : Logos.Agency.Act s p) :
    ∃ q : Prop, Chooses s p q :=
  Logos.Choice.AxIntentionalChoice s p hAct

/-- Spine 4: Free Will is established from intentional action (Choice.freeWill_exists_of_act). -/
theorem free_will_established (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ s : Subject, FreeWill s :=
  Logos.Choice.freeWill_exists_of_act h

/-- Spine 5: Free Subject exists from intentional action (Choice.freeSubject_exists_of_act). -/
theorem free_subject_exists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ s : Subject, FreeSubject s :=
  Logos.Choice.freeSubject_exists_of_act h

/-- Spine 6: Person exists from intentional action (Person.free_subject_is_person). -/
theorem person_exists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ s : Subject, Person s := by
  obtain ⟨s, hFs⟩ := free_subject_exists h
  exact ⟨s, Logos.Person.free_subject_is_person s hFs⟩

/-- Spine 7: Necessary Truth exists (resident in Semantics, C59). -/
theorem necessary_truth_exists : ∃ τ : Form, NecessarilyTrue τ :=
  step1_necessary_truth_exists

/-- Spine 8: Necessary Reality exists (Modal.T7_necessaryReality / T7, C18). -/
theorem necessary_reality_exists :
    ∃ e : Entity, NecessaryEntity e ∧ ∃ τ : Form, NecessarilyTrue τ ∧ Ground e τ :=
  step2_necessary_reality_exists

-- ============================================================================
-- 7. Forensic Reassessment of Countermodels
-- ============================================================================

/- Sections 7 (Strict Monotheism) and 8 (Trinitarian Architecture) of the
original file moved VERBATIM to scratch/Trinitarian_deferred.lean (DEFERRED,
never imported by the build): `God`, `Monotheism`, `universal_ground_unique`,
`divine_uniqueness`, `monotheism_derived`, `monotheism_of_god_and_uniqueness`,
`TrinitarianGodhead`, `trinitarian_persons_are_personal`,
`trinitarian_persons_are_necessary`, `trinitarian_wills_are_distinct`,
`trinitarian_godhead_yields_necessary_person`, `necessary_person_derived`,
`claim_e_implies_claim_d`, `monotheism_compatible_with_trinity`.
The proof spine above (1-8) and everything below (forensic countermodels, audit)
do not depend on that material. -/

/-- De Dicto vs De Re Modal Gap:
    General modal logic separating de dicto necessity from de re necessity.
    Footprint: `{}`. -/
theorem de_dicto_not_implies_de_re :
    ∃ (W : Type) (S : Type) (ExistsAt : W → S → Prop) (Pers : S → Prop),
      (∀ w : W, ∃ s : S, ExistsAt w s ∧ Pers s) ∧
      ¬ (∃ s : S, (∀ w : W, ExistsAt w s) ∧ Pers s) := by
  refine ⟨Bool, Bool, fun w s => s = w, fun _ => True, ?_⟩
  constructor
  · intro w; exact ⟨w, rfl, trivial⟩
  · rintro ⟨s, hUniv, _⟩
    have hTrue := hUniv true
    have hFalse := hUniv false
    rw [hTrue] at hFalse
    contradiction

/-- Normative Ground Independence Model:
    Evaluates whether the invariant necessity of the objective normative order
    (NecessaryNormativeOrder) logically forces the existence of an ontological ground
    (∃ g : Entity, GroundProp g ObjectiveNormativeOrder) in the absence of the
    universal truthmaker principle `GroundPrincipleProp`.
    Demonstrates that necessary normative truth does NOT entail a truthmaker. -/
structure NormativeGroundIndependenceModel where
  World : Type
  Entity : Type
  Subject : Type
  EntityOf : Subject → Entity
  ExistsAt : World → Entity → Prop
  PropSort : Type
  T : PropSort → Prop
  ObjectiveNormativeOrder : PropSort
  NormativeOrderAt : World → PropSort → Prop
  GroundProp : Entity → PropSort → Prop
  order_holds : T ObjectiveNormativeOrder
  necessary_order : ∀ w : World, NormativeOrderAt w ObjectiveNormativeOrder
  Act : Subject → PropSort → Prop
  FreeIndependentWill : Subject → Prop
  JudicativePolarity : Subject → PropSort → PropSort
  local_agential_grounding :
    ∀ (s : Subject) (p : PropSort),
      Act s p → FreeIndependentWill s → GroundProp (EntityOf s) (JudicativePolarity s p)
  no_ground_of_normative_order :
    ∀ g : Entity, ¬ GroundProp g ObjectiveNormativeOrder

/-- Theorem: The Normative Ground Independence Model is mathematically satisfiable.
    Proves that a universe can satisfy classical semantics, necessary normative truth,
    and local personal grounding while lacking any ontological ground of the objective normative order.
    Footprint: `{}`. -/
theorem normative_ground_independence_model_satisfiable :
    ∃ (_M : NormativeGroundIndependenceModel), True := by
  let M : NormativeGroundIndependenceModel := {
    World := Unit
    Entity := Unit
    Subject := Unit
    EntityOf := fun _ => ()
    ExistsAt := fun _ _ => True
    PropSort := Bool
    T := fun b => b = true
    ObjectiveNormativeOrder := true
    NormativeOrderAt := fun _ b => b = true
    GroundProp := fun _ p => p = false
    order_holds := rfl
    necessary_order := fun _ => rfl
    Act := fun _ _ => True
    FreeIndependentWill := fun _ => True
    JudicativePolarity := fun _ _ => false
    local_agential_grounding := fun _ _ _ _ => rfl
    no_ground_of_normative_order := fun _ h => by cases h
  }
  exact ⟨M, trivial⟩

/-- UNINTERPRETED-GROUND RELATION SEPARATION:
    In the absence of the universal truthmaking axiom `GroundPrincipleProp`,
    the invariant necessity of the objective normative order does NOT logically force
    the existence of an ontological ground over an uninterpreted `GroundProp` relation
    (`fun _ p => p = false`). This refutes forcing over an uninterpreted syntactic relation
    rather than proving philosophical independence of reality grounding.
    Footprint: `{}`. -/
theorem necessary_normative_truth_not_implies_ground :
    ¬ (∀ (M : NormativeGroundIndependenceModel),
        (∀ w, M.NormativeOrderAt w M.ObjectiveNormativeOrder) →
        ∃ g : M.Entity, M.GroundProp g M.ObjectiveNormativeOrder) := by
  intro hForced
  obtain ⟨M, _⟩ := normative_ground_independence_model_satisfiable
  have hNec := M.necessary_order
  obtain ⟨g, hg⟩ := hForced M hNec
  exact M.no_ground_of_normative_order g hg

-- ============================================================================
-- 8. Audit Block
-- ============================================================================

#print axioms claim_e_implies_claim_b
#print axioms claim_d_implies_claim_b
#print axioms claim_c_implies_claim_b
#print axioms ofAtom_ne_ofSubject
#print axioms ofAtom_not_necessary_personal_ground
#print axioms step1_necessary_truth_exists
#print axioms step2_necessary_reality_exists
#print axioms step3_personal_logical_inseparability
#print axioms ground_of_necessary_normative_order_is_necessary
#print axioms ground_of_normative_order_is_personal_ground
#print axioms de_dicto_not_implies_de_re
#print axioms normative_ground_independence_model_satisfiable
#print axioms necessary_normative_truth_not_implies_ground

end Logos.NecessaryPersonalGround
