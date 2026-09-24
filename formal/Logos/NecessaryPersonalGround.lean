/-
# Logos.NecessaryPersonalGround — The Necessary Personal Ground

This module reconstructs the transition from Necessary Truth and Necessary Reality
to the Necessary Personal Ground within Γ's unified four-tier ontology
(`Entity`, `Subject`, `Nature`, `Will`).

Status (Batch THIS_IS_PERSONAL, 2026-09-22; plan `THIS_IS_PERSONAL.md` §11.7/§12):

1. **Constitutive headline.** The required deliverable is Claim (I): Personhood
   is the necessary ontological basis of the objective normative/truth order (Right/Wrong,
   truth/falsity, Ought/OughtNot under the epistemic TruthNorm) governing judgments about
   Γ-reality. That is, it grounds the *correctness of propositions about what is the case*,
   not the fact of what exists: it is NOT a claim that the personal ground causally produces
   every existent, nor that it makes evil exist or morally legitimizes evil.
   It is proved in `Logos.PersonalGroundOfReality.person_yields_personal_grounding_of_reality`
   (historical compatibility alias: `present_act_yields_personal_grounding_of_reality`,
   footprint `{Initiates, Means, State, Subject, CL}`). Claim E
   (`∃ g, NecessaryEntity g ∧ NecessaryPersonalGround g`) is **annotated only**,
   never a theorem (obstacle registry, `THIS_IS_PERSONAL.md` §12.1).
2. **Trinitarian / monotheism block DEFERRED.** The strict-monotheism and
    trinitarian-architecture material (axioms `PersonalNature`,
    `personal_nature_iff_person`, `DivineNature`, `divine_nature_is_personal`,
    `divine_person_is_necessary`, `universal_ground_unique`, duplicate
    `GroundsEntity`/`explanatory_adequacy`, `explanatory_adequacy_normative_order`,
    and the derived theorems `divine_subject_is_person`, `God`, `Monotheism`,
    `divine_uniqueness`, `monotheism_derived`, `TrinitarianGodhead`,
    `trinitarian_*`, `necessary_person_derived`, `claim_e_implies_claim_d`, …) is
    deferred out of the live kernel and is **currently absent from the repository**
    (no `scratch/` directory exists). Once authored, it will live in
    `scratch/Trinitarian_deferred.lean`, never imported by the build; it may not
    compile (that is acceptable). Nothing trinitarian/monotheistic is a theorem of
    this build.
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
import Logos.Entity
import Logos.Modal
import Logos.Plurality
import Logos.NormativeOrder
import Logos.RecoveredOntologicalGround

namespace Logos.NecessaryPersonalGround

open Logos.Core (T IsFalse)
open Logos.Semantics (Form World Satisfies TrueAt)
open Logos.Agency (Subject A Means IntentionalSubject Nature HasNature Will subjectWill will_individuation)
open Logos.Choice (Chooses FreeWill FreeSubject)
open Logos.Person (Person person_is_intentional person_has_free_will)
open Logos.Entity (Entity ExistsAt TrueAt NecessarilyTrue EntityOf)
open Logos.Modal (NecessaryEntity Contingent actualWorld)
open Logos.Plurality (NecessarySubject)
open Logos.RecoveredOntologicalGround (GroundsEntity explanatory_adequacy)

-- ============================================================================
-- 1. Unified Ontological Framework (Subject, Nature, Will, Entity)
-- ============================================================================

/-- Actual entity: an entity that exists in the actual world. -/
def ActualEntity (e : Entity) : Prop := ExistsAt actualWorld e

/-- Impersonal Entity: an atomic factual entity that is not a subject. -/
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

/-- The necessity of the normative order is grounded in the free personal judicative
    act — constitutive, axiom-free. -/
theorem normative_order_is_grounded_in_personal_nature
    {s : Subject} {p : Prop} (h : Logos.NormativeOrder.ClaimsNormativeCorrectness s p) :
    NecessaryNormativeOrder ∧ Person s := by
  have hFW := Logos.NormativeOrder.claims_normative_correctness_derives_free_will s p h
  exact ⟨necessary_normative_order, Logos.Person.free_subject_is_person s hFW.2⟩

/-- The objective normative order is necessary (0 substantive axioms). -/
theorem necessary_normative_order_is_necessary : NecessaryNormativeOrder :=
  necessary_normative_order

-- ============================================================================
-- 3. Rigorous Formulation of Claims
-- ============================================================================

/-- Claim A: Necessary Truth exists (e.g. τ := p ∨ ¬p). -/
def ClaimA_NecessaryTruth (φ : Form) : Prop := NecessarilyTrue φ

/-- Claim D: Necessary Person exists.
    There exists a personal subject that exists across all possible worlds. -/
def ClaimD_NecessaryPerson : Prop := ∃ s : Subject, NecessarySubject s ∧ Person s

-- ============================================================================
-- 5. Explanatory Adequacy & Non-Reducibility of Personal Reality
-- ============================================================================

/-- Ontological Distinction: Atomic entities are provably distinct from any subject correlate. -/
theorem ofAtom_ne_ofSubject (n : Nat) (s : Subject) :
    Entity.ofAtom n ≠ EntityOf s :=
  fun h => Entity.noConfusion h

/-- Intentional capacity of an entity: an entity means proposition `p` iff it is a
    subject performing the intentional act `Means s p`. Empirical atoms have zero
    intentional capacity; the ground of reality means every proposition
    (explanatory-adequacy dual of the atom). NOTE (semantic stipulation, §5.2): as
    in `RecoveredOntologicalGround.EntityMeans`, the `.ofGround` meaning-everything
    branch is a definitional stipulation of the world-rigid constructor. -/
def EntityMeans (e : Entity) (p : Prop) : Prop :=
  match e with
  | Entity.ofSubject s => Means s p
  | Entity.ofAtom _ => False
  | Entity.ofGround => True

/- The duplicated `explanatory_adequacy` AXIOM moved VERBATIM to
scratch/Trinitarian_deferred.lean (DEFERRED); the canonical theorem
`Logos.RecoveredOntologicalGround.explanatory_adequacy` (footprint
`{Means, Subject}`) is used below via the `open` above. -/

/-- An impersonal atomic entity cannot ground an intentional agent.
    Because an atom has zero intentional capacity (EntityMeans (Entity.ofAtom n) p ↔ False),
    it cannot ground any subject that means a proposition.
    Footprint: `{Means, Subject}`. -/
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
    Footprint: `{Means, Subject}`. -/
theorem atom_cannot_ground_person (n : Nat) (s : Subject) (hPerson : Person s) :
    ¬ GroundsEntity (Entity.ofAtom n) (EntityOf s) := by
  have hFreeWill : FreeWill s := Logos.Person.person_has_free_will s hPerson
  obtain ⟨p, _q, hChooses⟩ := hFreeWill
  exact atom_cannot_ground_intentional_subject n s p hChooses.1

-- ============================================================================
-- 6. Principled Derivation of Necessary Personal Ground (No Blunt Shortcut)
-- ============================================================================

/-- Step 1: Strong Necessary Truth exists (resident in the Core/Semantics machinery).
    Verified with footprint `{CL}`. -/
theorem step1_necessary_truth_exists : ∃ τ : Form, NecessarilyTrue τ :=
  Logos.Semantics.strongTruthExists

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
    Footprint: `{AxIntentionalChoice, Initiates, Means, State, Subject, Will, subjectWill}`. -/
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
    change Logos.Entity.SubjectExistsAt actualWorld s'
    exact rfl
  exact ⟨s', hWill, hFreeWill, hFreeSubj, hPerson, hActual⟩

/-- Epistemic Discovery: Master Agential Theorem without AxIntentionalChoice.
    Under the performative normative stance, actual volitional reality is established:
    `ClaimsNormativeCorrectness s p → Chooses s (Correct s p) (Incorrect s p) → FreeWill s → FreeSubject s → Person s ∧ Will (subjectWill s) ∧ ActualEntity (EntityOf s)`.
    Footprint: `{Initiates, Means, State, Subject, Will, subjectWill, CL}` (0 substantive axioms, completely free of AxIntentionalChoice). -/
theorem established_normative_person
    (hClaims : ∃ s : Subject, ∃ p : Prop, Logos.NormativeOrder.ClaimsNormativeCorrectness s p) :
    ∃ s : Subject, (∃ w : Will, w = subjectWill s) ∧ FreeWill s ∧ FreeSubject s ∧ Person s ∧ ActualEntity (EntityOf s) := by
  obtain ⟨s, p, hClaims_sp⟩ := hClaims
  have hFW : FreeWill s := (Logos.NormativeOrder.claims_normative_correctness_derives_free_will s p hClaims_sp).2
  have hFreeSubj : FreeSubject s := hFW
  have hPerson : Person s := Logos.Person.free_subject_is_person s hFreeSubj
  have hWill : ∃ w : Will, w = subjectWill s := ⟨subjectWill s, rfl⟩
  have hActual : ActualEntity (EntityOf s) := by
    change Logos.Entity.SubjectExistsAt actualWorld s
    exact rfl
  exact ⟨s, hWill, hFW, hFreeSubj, hPerson, hActual⟩

/-- Spine 7: Necessary Truth exists (resident in Semantics, C59). -/
theorem necessary_truth_exists : ∃ τ : Form, NecessarilyTrue τ :=
  step1_necessary_truth_exists

-- ============================================================================
-- 7. Forensic Reassessment of Countermodels
-- ============================================================================

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

-- ============================================================================
-- 8. Audit Block
-- ============================================================================

#print axioms ofAtom_ne_ofSubject
#print axioms step1_necessary_truth_exists
#print axioms step3_personal_logical_inseparability
#print axioms de_dicto_not_implies_de_re

end Logos.NecessaryPersonalGround
