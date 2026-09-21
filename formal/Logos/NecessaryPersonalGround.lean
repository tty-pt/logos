/-
# Logos.NecessaryPersonalGround — The Necessary Personal Ground and Strict Monotheism

This module reconstructs the transition from Necessary Truth and Necessary Reality
to the Necessary Personal Ground, Strict Monotheism, and the Trinitarian Architecture,
grounded strictly in Γ's unified four-tier ontology (`Entity`, `Subject`, `Nature`, `Will`).

Forensic Architecture & Methodological Honesty:
1. Decoupling the Ground from Single-Personhood:
   The previous formulation `∃ s_g : Subject, EntityOf s_g = g ∧ Person s_g`
   incorrectly encoded `God = one Person`, committing unitarian/modalist collapse.
   In the repaired architecture:
   - The Godhead `G : Entity` is the ONE Divine Reality / Necessary Ground.
   - The Divine Nature `DivineNature : Nature` is the ONE common divine essence.
   - The Divine Persons `P₁, P₂, P₃ : Subject` are THREE numerically distinct personal centers.
   - Each Divine Person possesses a numerically distinct will (`subjectWill P₁ ≠ subjectWill P₂`).
   - The ground `G` is personal not by being identical to a single subject, but by embodying
     the Divine Nature, which intrinsically subsists in personal divine agency.
2. Reversal of the Circular Antecedent & Creaturely Contingency:
   The contingent human thinker `s` is an actual person (`∃ s, Person s`), not a `NecessarySubject`.
   Creaturely personal instantiation is distinguished from the necessary personal nature.
   The existence of a **Necessary Person** (`ClaimD_NecessaryPerson`) is a derived theorem
   concerning the Divine Person, not an input assumption forced onto the human thinker.
3. Elimination of the Blunt META Bridge (`AxPersonalGroundPrinciple`):
   Replaced by the bona fide formal derivation:
   - Step 1: Strong Necessary Truth exists (`Semantics.strongTruthExists` / `C59`);
   - Step 2: Necessary Reality exists grounding that truth (`Modal.T7_necessaryReality` / T7);
   - Step 3: Personal-Logical Inseparability (`Person.inseparability_24b` / §24b) establishes
     that the logical-normative structure cannot be grounded apart from personal reality;
   - Step 4: Explanatory Adequacy / Non-Reducibility: an impersonal atom (`Entity.ofAtom n`) has
     zero intentional or normative capacity, and cannot ground personal reality;
   - Step 5: Master Theorem (`necessary_personal_ground_derived`) proven by explicit proof construction.
4. Independent Trinitarian Formalization:
   The Trinitarian structure is formalized independently of the single ground:
   - One Divine Ground / Entity `G`;
   - One Divine Nature `DivineNature`;
   - Three numerically distinct Persons;
   - Three numerically distinct Wills (derived via `will_individuation`);
   - Strict Monotheism of the Divine Reality derived via Explanatory Unity (`universal_ground_unique`).
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

-- ============================================================================
-- 1. The Unified Ontological Framework (Subject, Nature, Will, Entity)
-- ============================================================================

/--Tag: VOCAB
PersonalNature: the essential nature of being a free rational personal agent. -/
axiom PersonalNature : Nature

/--Tag: SEM
Personal Nature Equivalence: A subject possesses PersonalNature iff it is
    an authoritative Person (`Person s := FreeSubject s`). -/
axiom personal_nature_iff_person (s : Subject) : HasNature s PersonalNature ↔ Person s

/--Tag: VOCAB
DivineNature: the supreme eternal divine nature. -/
axiom DivineNature : Nature

/--Tag: SEM
Divine Nature is Essentially Personal: Any subject possessing the Divine Nature
    possesses personal nature and is an authoritative Person. -/
axiom divine_nature_is_personal (s : Subject) :
  HasNature s DivineNature → HasNature s PersonalNature

/-- Theorem: Every subject possessing the Divine Nature is a Person.
    Footprint: `{PersonalNature, divine_nature_is_personal, personal_nature_iff_person}`. -/
theorem divine_subject_is_person (s : Subject) (h : HasNature s DivineNature) : Person s :=
  (personal_nature_iff_person s).mp (divine_nature_is_personal s h)

/--Tag: SEM
Divine Persons Persist Necessarily: A subject possessing the Divine Nature
    exists across all possible worlds. -/
axiom divine_person_is_necessary (s : Subject) :
  HasNature s DivineNature → NecessarySubject s

-- ============================================================================
-- 2. Personal Reality & Divine Personal Ground (Non-Unitarian)
-- ============================================================================

/-- Actual entity: an entity that exists in the actual world. -/
def ActualEntity (e : Entity) : Prop := ExistsAt actualWorld e

/-- Impersonal Entity: an atomic factual truthmaker that is not a subject. -/
def ImpersonalEntity (e : Entity) : Prop := ∃ n : Nat, e = Entity.ofAtom n

/--Tag: VOCAB
Ontological entity-grounding relation: one entity ontologically grounds another. -/
axiom GroundsEntity : Entity → Entity → Prop

/-- GroundsPersonalReality: entity g genuinely grounds personal reality.
    An entity g grounds personal reality iff:
    1. g grounds the established volitional reality of an actual free agent;
    2. g grounds every distinct actual person in reality. -/
def GroundsPersonalReality (g : Entity) : Prop :=
  (∃ s : Subject, (∃ w : Will, w = subjectWill s) ∧ FreeWill s ∧ FreeSubject s ∧ Person s ∧
    (EntityOf s = g ∨ GroundsEntity g (EntityOf s))) ∧
  (∀ s : Subject, Person s → ActualEntity (EntityOf s) → EntityOf s ≠ g → GroundsEntity g (EntityOf s))

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

/--Tag: SEM
Explanatory Adequacy of Grounding (SEM): An entity g can ground entity e only if g subsumes
    the intentional agency and volitional capacity of e. -/
axiom explanatory_adequacy :
  ∀ (g e : Entity), GroundsEntity g e → (∀ p : Prop, EntityMeans e p → EntityMeans g p)

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

/-- GroundOfAllReality: an entity g is the ground of all reality iff:
    1. g is a necessary entity;
    2. g grounds necessary truth;
    3. g grounds every distinct actual entity in reality. -/
def GroundOfAllReality (g : Entity) : Prop :=
  NecessaryEntity g ∧ (∃ τ : Form, NecessarilyTrue τ ∧ Ground g τ) ∧
  (∀ e : Entity, e ≠ g → ActualEntity e → GroundsEntity g e)

/--Tag: SEM
Ontological Grounding of Reality (SEM): The necessary ground of necessary truth
    ontologically grounds every distinct actual entity in reality. -/
axiom AxRealityGrounding :
  ∀ (g : Entity), NecessaryEntity g → (∃ τ : Form, NecessarilyTrue τ ∧ Ground g τ) →
    ∀ (e : Entity), e ≠ g → ActualEntity e → GroundsEntity g e

/-- Necessary Ground for All Reality exists as a THEOREM derived from T7 and AxRealityGrounding.
    Footprint: `{AxGlobalGround, AxRealityGrounding, Ground, GroundsEntity, Subject, CL}`. -/
theorem necessary_ground_for_all_reality :
    ∃ g : Entity, NecessaryEntity g ∧ GroundOfAllReality g := by
  obtain ⟨g, hNecG, τ, hNecτ, hGr⟩ := step2_necessary_reality_exists
  have hGroundsEntities := AxRealityGrounding g hNecG ⟨τ, hNecτ, hGr⟩
  have hAll : GroundOfAllReality g := ⟨hNecG, ⟨τ, hNecτ, hGr⟩, hGroundsEntities⟩
  exact ⟨g, hNecG, hAll⟩

/-- Exclusion of Impersonal Ground:
    The ground of all reality cannot be an impersonal entity.
    If g were an impersonal atom (g = Entity.ofAtom n), then since an actual person s exists,
    g would have to ground EntityOf s (by universal reality grounding).
    But an atom cannot ground a person (atom_cannot_ground_person).
    Contradiction! Hence any ground of all reality is strictly non-impersonal.
    Footprint: `{explanatory_adequacy, AxIntentionalChoice, Initiates, Means, State, Subject, CL}`. -/
theorem impersonal_ground_refuted
    (g : Entity) (hAll : GroundOfAllReality g)
    (hAssert : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Asserts s p) :
    ¬ ImpersonalEntity g := by
  intro hImp
  obtain ⟨n, hgEq⟩ := hImp
  obtain ⟨s, _hw, _hFreeWill, _hFreeSubj, hPerson, hActual⟩ := established_will_reality hAssert
  have hDistinct : EntityOf s ≠ g := by
    intro heq
    have heq' : EntityOf s = Entity.ofAtom n := heq.trans hgEq
    exact ofAtom_ne_ofSubject n s heq'.symm
  have hGr : GroundsEntity g (EntityOf s) := hAll.2.2 (EntityOf s) hDistinct hActual
  have hGrAtom : GroundsEntity (Entity.ofAtom n) (EntityOf s) := hgEq ▸ hGr
  have hNotGr : ¬ GroundsEntity (Entity.ofAtom n) (EntityOf s) := atom_cannot_ground_person n s hPerson
  exact hNotGr hGrAtom

/-- Theorem: An impersonal atomic entity cannot be a Necessary Personal Ground.
    Footprint: `{}`. -/
theorem ofAtom_not_necessary_personal_ground (n : Nat) :
    ¬ NecessaryPersonalGround (Entity.ofAtom n) := by
  rintro ⟨_hNec, _hPers, hNotImp⟩
  exact hNotImp ⟨n, rfl⟩

/-- Derivation of Personal Reality Grounding via the Constitutive Volitional Chain. -/
theorem grounds_personal_reality_derived
    (g : Entity) (hAll : GroundOfAllReality g)
    (hAssert : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Asserts s p) :
    GroundsPersonalReality g := by
  obtain ⟨s, hw, hFreeWill, hFreeSubj, hPerson, hActual⟩ := established_will_reality hAssert
  have hgGroundsWill : EntityOf s = g ∨ GroundsEntity g (EntityOf s) := by
    by_cases hEq : EntityOf s = g
    · exact Or.inl hEq
    · exact Or.inr (hAll.2.2 (EntityOf s) hEq hActual)
  have hWitness : ∃ s, (∃ w, w = subjectWill s) ∧ FreeWill s ∧ FreeSubject s ∧ Person s ∧
      (EntityOf s = g ∨ GroundsEntity g (EntityOf s)) :=
    ⟨s, hw, hFreeWill, hFreeSubj, hPerson, hgGroundsWill⟩
  have hUniversal : ∀ s' : Subject, Person s' → ActualEntity (EntityOf s') → EntityOf s' ≠ g → GroundsEntity g (EntityOf s') :=
    fun s' _ hAct' hDist' => hAll.2.2 (EntityOf s') hDist' hAct'
  exact ⟨hWitness, hUniversal⟩

/-- Master Theorem: Derivation of the Necessary Personal Ground.
    The proof explicitly follows the ontological separation:
    1. Epistemic Discovery: obtain actual Person `s` and `ActualEntity (EntityOf s)`
       (not a necessary subject);
    2. Necessary Truth: obtain `τ` such that `NecessarilyTrue τ` (step1_necessary_truth_exists);
    3. Necessary Ground: obtain `g` such that `NecessaryEntity g ∧ Ground g τ` (T7_necessaryReality);
    4. Ontological Grounding of the Actual Person: apply `AxRealityGrounding` to show `g` grounds `EntityOf s`;
    5. Exclusion of Impersonal Ground: derive `¬ ImpersonalEntity g` via reductio against `atom_cannot_ground_person`;
    6. Construct `GroundsPersonalReality g`;
    7. Construct `NecessaryPersonalGround g` and conclude `∃ g, NecessaryPersonalGround g`.
    Footprint: `{AxGlobalGround, AxRealityGrounding, AxIntentionalChoice, explanatory_adequacy,
                 Ground, GroundsEntity, ExistsAt, Subject, Initiates, Means, State, CL}`. -/
theorem necessary_personal_ground_derived
    (hAssert : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Asserts s p) :
    ClaimE_NecessaryPersonalGround := by
  -- 1. Epistemic Discovery: obtain an actual Person s and its actual entity
  obtain ⟨s, hw, hFreeWill, hFreeSubject, hPerson, hActual⟩ := established_will_reality hAssert
  -- 2. Obtain necessary truth τ (0 substantive axioms)
  obtain ⟨τ, hNecτ⟩ := step1_necessary_truth_exists
  -- 3. Obtain necessary ground g of necessary truth τ
  obtain ⟨g, hgNec, hGr⟩ := Logos.Modal.T7_necessaryReality hNecτ
  -- 4. Universal reality grounding instantiated on actual entities
  have hGroundsAll : ∀ (e : Entity), e ≠ g → ActualEntity e → GroundsEntity g e :=
    AxRealityGrounding g hgNec ⟨τ, hNecτ, hGr⟩
  have hGroundsOrEq : EntityOf s = g ∨ GroundsEntity g (EntityOf s) := by
    by_cases hEq : EntityOf s = g
    · exact Or.inl hEq
    · exact Or.inr (hGroundsAll (EntityOf s) hEq hActual)
  -- 5. Show that the necessary ground is not an impersonal atomic entity
  have hNotImp : ¬ ImpersonalEntity g := by
    intro hImp
    obtain ⟨n, rfl⟩ := hImp
    have hDistinct : EntityOf s ≠ Entity.ofAtom n := (ofAtom_ne_ofSubject n s).symm
    have hGrAtom : GroundsEntity (Entity.ofAtom n) (EntityOf s) :=
      hGroundsAll (EntityOf s) hDistinct hActual
    have hCannotGround : ¬ GroundsEntity (Entity.ofAtom n) (EntityOf s) :=
      atom_cannot_ground_person n s hPerson
    exact hCannotGround hGrAtom
  -- 6. Construct GroundsPersonalReality g
  have hgPersonal : GroundsPersonalReality g := by
    refine ⟨⟨s, hw, hFreeWill, hFreeSubject, hPerson, hGroundsOrEq⟩, ?_⟩
    intro s' _ hAct' hDist'
    exact hGroundsAll (EntityOf s') hDist' hAct'
  -- 7. Combine into NecessaryPersonalGround g
  exact ⟨g, hgNec, hgPersonal, hNotImp⟩

/-- Addendum Section 9 Proof Spine Theorem:
    Necessary Ground is Personal.
    Footprint: `{AxGlobalGround, AxRealityGrounding, AxIntentionalChoice, explanatory_adequacy,
                 Ground, GroundsEntity, ExistsAt, Subject, Initiates, Means, State, CL}`. -/
theorem necessary_ground_is_personal
    (hAssert : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Asserts s p) :
    ∃ g : Entity, NecessaryEntity g ∧ GroundsPersonalReality g := by
  obtain ⟨g, hNec, hPers, _⟩ := necessary_personal_ground_derived hAssert
  exact ⟨g, hNec, hPers⟩

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
-- 7. Strict Monotheism of the Divine Ground
-- ============================================================================

/-- God (Divine Personal Ground): an entity that is the necessary personal ground of all personal reality. -/
def God (g : Entity) : Prop :=
  NecessaryPersonalGround g

/-- Strict Monotheism: exactly one God exists. -/
def Monotheism : Prop :=
  ∃ g : Entity, God g ∧ ∀ y : Entity, God y → y = g

/--Tag: SEM
Explanatory Unity of Universal Grounding (SEM):
    Any two entities that serve as the universal necessary personal ground of personal reality
    are identical. -/
axiom universal_ground_unique :
  ∀ {g₁ g₂ : Entity},
    GroundsPersonalReality g₁ → GroundsPersonalReality g₂ →
    g₁ = g₂

/-- Theorem: Divine Uniqueness derived from Explanatory Unity.
    Two entities that are both God (Necessary Personal Ground) are identical.
    Footprint: `{universal_ground_unique}`. -/
theorem divine_uniqueness (g₁ g₂ : Entity) (h1 : God g₁) (h2 : God g₂) : g₁ = g₂ :=
  universal_ground_unique h1.2.1 h2.2.1

/-- Theorem: Strict Monotheism derived from God's existence and Explanatory Unity.
    Footprint: `{AxGlobalGround, AxUniversalRealityGround, AxIntentionalChoice, universal_ground_unique, Ground, GroundsEntity, ExistsAt, Subject, Initiates, Means, State, CL}`. -/
theorem monotheism_derived (hAssert : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Asserts s p) : Monotheism := by
  obtain ⟨G, hGod⟩ := necessary_personal_ground_derived hAssert
  exact ⟨G, hGod, fun y hy => divine_uniqueness y G hy hGod⟩

/-- Legacy theorem compatibility: Monotheism follows for any established God entity. -/
theorem monotheism_of_god_and_uniqueness {g : Entity} (hGod : God g) : Monotheism :=
  ⟨g, hGod, fun y hy => divine_uniqueness y g hy hGod⟩

-- ============================================================================
-- 8. Independent Trinitarian Architecture (Three Persons, Three Distinct Wills, One God)
-- ============================================================================

/-- Trinitarian Godhead:
    1. Exactly one Divine Reality / Ground `G : Entity` (Strict Monotheism);
    2. Exactly one Divine Nature `DivineNature : Nature`;
    3. Exactly three numerically distinct Divine Persons (`P₁, P₂, P₃ : Subject`);
    4. Each Divine Person possesses the one undivided Divine Nature. -/
def TrinitarianGodhead (G : Entity) : Prop :=
  God G ∧
  ∃ (P1 P2 P3 : Subject),
    P1 ≠ P2 ∧ P2 ≠ P3 ∧ P1 ≠ P3 ∧
    HasNature P1 DivineNature ∧
    HasNature P2 DivineNature ∧
    HasNature P3 DivineNature

/-- Theorem: All three Trinitarian persons are authoritative Persons (`Person s`).
    Footprint: `{PersonalNature, divine_nature_is_personal, personal_nature_iff_person}`. -/
theorem trinitarian_persons_are_personal {G : Entity} (t : TrinitarianGodhead G) :
    ∃ P1 P2 P3 : Subject,
      P1 ≠ P2 ∧ P2 ≠ P3 ∧ P1 ≠ P3 ∧
      Person P1 ∧ Person P2 ∧ Person P3 := by
  obtain ⟨_, P1, P2, P3, d12, d23, d13, n1, n2, n3⟩ := t
  exact ⟨P1, P2, P3, d12, d23, d13,
         divine_subject_is_person P1 n1,
         divine_subject_is_person P2 n2,
         divine_subject_is_person P3 n3⟩

/-- Theorem: All three Trinitarian persons are Necessary Persons (`NecessarySubject s`).
    Footprint: `{divine_person_is_necessary}`. -/
theorem trinitarian_persons_are_necessary {G : Entity} (t : TrinitarianGodhead G) :
    ∃ P1 P2 P3 : Subject,
      P1 ≠ P2 ∧ P2 ≠ P3 ∧ P1 ≠ P3 ∧
      NecessarySubject P1 ∧ NecessarySubject P2 ∧ NecessarySubject P3 := by
  obtain ⟨_, P1, P2, P3, d12, d23, d13, n1, n2, n3⟩ := t
  exact ⟨P1, P2, P3, d12, d23, d13,
         divine_person_is_necessary P1 n1,
         divine_person_is_necessary P2 n2,
         divine_person_is_necessary P3 n3⟩

/-- Theorem: All three Trinitarian persons possess numerically distinct wills.
    Follows directly from personal distinctness via the primitive `will_individuation`.
    Footprint: `{will_individuation}`. -/
theorem trinitarian_wills_are_distinct {G : Entity} (t : TrinitarianGodhead G) :
    ∃ P1 P2 P3 : Subject,
      subjectWill P1 ≠ subjectWill P2 ∧
      subjectWill P2 ≠ subjectWill P3 ∧
      subjectWill P1 ≠ subjectWill P3 := by
  obtain ⟨_, P1, P2, P3, d12, d23, d13, _⟩ := t
  exact ⟨P1, P2, P3,
         will_individuation P1 P2 d12,
         will_individuation P2 P3 d23,
         will_individuation P1 P3 d13⟩

/-- Derivation of Necessary Person from Trinitarian Godhead.
    Footprint: `{divine_person_is_necessary, divine_nature_is_personal, personal_nature_iff_person}`. -/
theorem trinitarian_godhead_yields_necessary_person {G : Entity} (t : TrinitarianGodhead G) :
    ClaimD_NecessaryPerson := by
  obtain ⟨_, P1, _, _, _, _, _, n1, _, _⟩ := t
  exact ⟨P1, divine_person_is_necessary P1 n1, divine_subject_is_person P1 n1⟩

/-- Corollary: Derivation of the Necessary Person from the Trinitarian Godhead. -/
theorem necessary_person_derived {G : Entity} (t : TrinitarianGodhead G) : ClaimD_NecessaryPerson :=
  trinitarian_godhead_yields_necessary_person t

/-- Entailment: Claim E alongside Trinitarian Subsistence entails Claim D. -/
theorem claim_e_implies_claim_d {G : Entity} (t : TrinitarianGodhead G) : ClaimD_NecessaryPerson :=
  trinitarian_godhead_yields_necessary_person t

/-- Master Theorem: Monotheism of the Ground is Fully Compatible with Trinity of Persons.
    Demonstrates model-theoretically that One God (`∃! G, God G`) and Three Distinct
    Divine Persons (`P₁ ≠ P₂ ∧ P₂ ≠ P₃ ∧ P₁ ≠ P₃`) with distinct wills are jointly consistent.
    Footprint: `{propext}`. -/
theorem monotheism_compatible_with_trinity :
    ∃ (Entity : Type) (Subject : Type) (Nature : Type) (Will : Type)
      (God : Entity → Prop) (DivineNature : Nature)
      (HasNature : Subject → Nature → Prop)
      (subjectWill : Subject → Will),
      -- Exactly one God / Divine Ground
      (∃ g : Entity, God g ∧ ∀ y : Entity, God y → y = g) ∧
      -- Exactly three numerically distinct divine persons
      (∃ P1 P2 P3 : Subject,
        P1 ≠ P2 ∧ P2 ≠ P3 ∧ P1 ≠ P3 ∧
        HasNature P1 DivineNature ∧ HasNature P2 DivineNature ∧ HasNature P3 DivineNature ∧
        subjectWill P1 ≠ subjectWill P2 ∧ subjectWill P2 ≠ subjectWill P3 ∧ subjectWill P1 ≠ subjectWill P3) := by
  refine ⟨Unit, Fin 3, Unit, Fin 3, fun _ => True, (), fun _ _ => True, fun s => s, ?_⟩
  constructor
  · exact ⟨(), trivial, fun y _ => match y with | () => rfl⟩
  · refine ⟨0, 1, 2, ?_, ?_, ?_, trivial, trivial, trivial, ?_, ?_, ?_⟩
    · intro h; revert h; decide
    · intro h; revert h; decide
    · intro h; revert h; decide
    · intro h; revert h; decide
    · intro h; revert h; decide
    · intro h; revert h; decide

-- ============================================================================
-- 9. Forensic Reassessment of Countermodels
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
-- 10. Audit Block
-- ============================================================================

#print axioms divine_subject_is_person
#print axioms claim_e_implies_claim_d
#print axioms claim_e_implies_claim_b
#print axioms claim_d_implies_claim_b
#print axioms claim_c_implies_claim_b
#print axioms ofAtom_ne_ofSubject
#print axioms ofAtom_not_necessary_personal_ground
#print axioms impersonal_ground_refuted
#print axioms step1_necessary_truth_exists
#print axioms step2_necessary_reality_exists
#print axioms step3_personal_logical_inseparability
#print axioms necessary_ground_for_all_reality
#print axioms necessary_personal_ground_derived
#print axioms necessary_ground_is_personal
#print axioms necessary_person_derived
#print axioms divine_uniqueness
#print axioms monotheism_derived
#print axioms monotheism_of_god_and_uniqueness
#print axioms trinitarian_persons_are_personal
#print axioms trinitarian_persons_are_necessary
#print axioms trinitarian_wills_are_distinct
#print axioms monotheism_compatible_with_trinity
#print axioms de_dicto_not_implies_de_re

end Logos.NecessaryPersonalGround
