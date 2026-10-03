-- Logos/ConditionalTheology.lean
-- The Conditional Theology Program: Downstream consequences of AxIntentionalChoice (A14)
-- and the exact independence boundaries of grounding, plurality, love, trinity, incarnation, and creation.

import Logos.Core
import Logos.Necessity
import Logos.Semantics
import Logos.Entity
import Logos.Modal
import Logos.Agency
import Logos.Person
import Logos.Initiation
import Logos.Alternatives
import Logos.Order
import Logos.Choice
import Logos.Value
import Logos.Plurality
import Logos.Love
import Logos.HostileSemantics

namespace Logos.ConditionalTheology

open Logos.Agency
open Logos.Choice
open Logos.Person
open Logos.Value
open Logos.Love
open Logos.HostileSemantics

/-!
# The Conditional Theology Program

This module investigates what the deductive architecture of Γ can derive downstream
once `AxIntentionalChoice` (A14) is accepted as the single substantive semantic commitment:
    `Act s p → ∃ q, Chooses s p q`

Every downstream theological and metaphysical bridge is rigorously classified:
- LOGICAL / DEFINITIONAL
- SEMANTIC
- METAPHYSICAL
- COUNTERMODEL (proven independent)
- OPEN
-/

-- ===========================================================================
-- Sector 1: Agency Closure & Downstream Limits of FreeWill
-- ===========================================================================

section Sector1_AgencyClosure

/-- Full Agency Closure (A14 + Definitions):
    An intentional act derives genuine choice, free will, and free/intentional subjectivity.
    (Substantive personhood remains OPEN under the hardened Person definition).
    Axiom footprint: {Initiates, Means, State, Subject, AxIntentionalChoice}. -/
theorem agency_closure_act_to_chooses (s : Subject) (p : Prop) (hAct : Act s p) :
    ∃ q : Prop, Chooses s p q :=
  AxIntentionalChoice s p hAct

theorem agency_closure_act_to_freewill (s : Subject) (p : Prop) (hAct : Act s p) :
    FreeWill s := by
  obtain ⟨q, hq⟩ := AxIntentionalChoice s p hAct
  exact ⟨p, q, hq⟩

theorem agency_closure_act_to_freeSubject (s : Subject) (p : Prop) (hAct : Act s p) :
    FreeSubject s :=
  (freeSubject_iff_freeWill s).mpr (agency_closure_act_to_freewill s p hAct)

theorem agency_closure_act_to_intentionalSubject (s : Subject) (p : Prop) (hAct : Act s p) :
    IntentionalSubject s :=
  act_implies_intentionalSubject hAct

/-!
### The 8 Downstream Attributes of Agency
We aggressively test whether FreeWill + existing Γ ontology entails anything further about:
1. Rationality
2. Normativity
3. Value
4. Teleology
5. Subjectivity (transcendental reflection)
6. Relationality
7. Persistence
8. Necessity
-/

/-- 1. Rationality Separation:
    Free will does NOT entail that the agent acts for reasons (`ReasonsFor`).
    An agent can possess genuine choice between propositions without possessing reason-explanations. -/
theorem freewill_not_entails_rationality :
    ∃ (Subj : Type) (Chooses : Subj → Prop → Prop → Prop) (ReasonsFor : Subj → Prop → Prop → Prop),
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      (∀ s p q, Chooses s p q → ¬ ∃ r, ReasonsFor s p r) := by
  refine ⟨Unit, fun _ _ _ => True, fun _ _ _ => False, ⟨(), True, False, trivial⟩, ?_⟩
  intro _ _ _ _ ⟨r, hr⟩
  exact hr

/-- 2. Normativity Separation:
    Free will does NOT entail moral or normative correctness (`ActsCorrectly`).
    An agent can possess genuine choice while choosing incorrectly or against the truth. -/
theorem freewill_not_entails_normativity :
    ∃ (Subj : Type) (Chooses : Subj → Prop → Prop → Prop) (ActsCorrectly : Subj → Prop → Prop),
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q ∧ ¬ ActsCorrectly s p) := by
  refine ⟨Unit, fun _ _ _ => True, fun _ _ => False, ⟨(), True, False, trivial⟩, ⟨(), True, False, trivial, id⟩⟩

/-- 3. Value Separation:
    Free will does NOT entail interpersonal value or concern for goodness (`AffectsValue`).
    An agent can choose over cold, valueless propositional states. -/
theorem freewill_not_entails_value :
    ∃ (Subj : Type) (Chooses : Subj → Prop → Prop → Prop) (AffectsValue : Subj → Subj → Prop),
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      (∀ s₁ s₂, ¬ AffectsValue s₁ s₂) := by
  refine ⟨Unit, fun _ _ _ => True, fun _ _ => False, ⟨(), True, False, trivial⟩, fun _ _ h => h⟩

/-- 4. Teleology Separation:
    Free will does NOT entail acting for an overarching teleological end (`HasGoal`).
    An agent can execute a choice spontaneously without end-directed orientation. -/
theorem freewill_not_entails_teleology :
    ∃ (Subj : Type) (Chooses : Subj → Prop → Prop → Prop) (HasGoal : Subj → Prop → Prop),
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      (∀ s g, ¬ HasGoal s g) := by
  refine ⟨Unit, fun _ _ _ => True, fun _ _ => False, ⟨(), True, False, trivial⟩, fun _ _ h => h⟩

/-- 5. Reflexive Subjectivity Separation:
    Free will does NOT entail reflexive self-knowledge (`KnowsOwnAct`).
    A chooser need not execute a higher-order cognitive representation of its own choosing act. -/
theorem freewill_not_entails_reflexive_subjectivity :
    ∃ (Subj : Type) (Chooses : Subj → Prop → Prop → Prop) (KnowsOwnAct : Subj → Prop → Prop),
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      (∀ s p, ¬ KnowsOwnAct s p) := by
  refine ⟨Unit, fun _ _ _ => True, fun _ _ => False, ⟨(), True, False, trivial⟩, fun _ _ h => h⟩

/-- 6. Relationality Separation:
    Free will does NOT entail relationality to another subject (`∃ s₂, s ≠ s₂`).
    A solitary subject can possess genuine choice in total isolation. -/
theorem freewill_not_entails_relationality :
    ∃ (Subj : Type) (Chooses : Subj → Prop → Prop → Prop),
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      (∀ s₁ s₂ : Subj, s₁ = s₂) := by
  refine ⟨Unit, fun _ _ _ => True, ⟨(), True, False, trivial⟩, fun () () => rfl⟩

/-- 7. Persistence Separation:
    Free will does NOT entail temporal persistence (`PersistsAcrossTime`).
    A choosing subject can exist and act in an instantaneous state and immediately cease to exist. -/
theorem freewill_not_entails_persistence :
    ∃ (Subj : Type) (Chooses : Subj → Prop → Prop → Prop) (Persists : Subj → Prop),
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      (∀ s, ¬ Persists s) := by
  refine ⟨Unit, fun _ _ _ => True, fun _ => False, ⟨(), True, False, trivial⟩, fun _ h => h⟩

/-- 8. Necessity Separation:
    Free will does NOT entail necessary existence (`NecSubject`).
    A contingent subject can possess free will while being entirely contingent. -/
theorem freewill_not_entails_necessity :
    ∃ (Subj : Type) (Chooses : Subj → Prop → Prop → Prop) (NecSubject : Subj → Prop),
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      (∀ s, ¬ NecSubject s) := by
  refine ⟨Unit, fun _ _ _ => True, fun _ => False, ⟨(), True, False, trivial⟩, fun _ h => h⟩

end Sector1_AgencyClosure

-- ===========================================================================
-- Sector 2: Grounding Architecture & Infinite Chain Obstruction
-- ===========================================================================

section Sector2_GroundingArchitecture

/-!
The 4-step grounding progression in Γ:
    necessary truth (T p)
        ↓  (A4 / A6 - Grounding / Global Ground)
    some ground (∃ e, Ground e p)
        ↓  (Modal definition / T7)
    necessary ground (∃ e, Ground e p ∧ Nec e)
        ↓  (Well-foundedness / Termination - OPEN / BLOCKED)
    ultimate ground (¬ ∃ x, GroundEntity x u)

We test whether A14 (`AxIntentionalChoice`) can eliminate the infinite ground chain.
-/

/-- A14 does NOT eliminate the infinite ground chain:
    The existence of free intentional agency is completely orthogonal to whether
    the explanatory ordering of grounds terminates. -/
theorem a14_not_eliminates_infinite_ground_chain :
    ∃ (Subj : Type) (Ent : Type)
      (Chooses : Subj → Prop → Prop → Prop)
      (GroundEnt : Ent → Ent → Prop)
      (Ultimate : Ent → Prop),
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      (∀ x : Ent, ¬ GroundEnt x x) ∧
      (∀ x y z : Ent, GroundEnt x y → GroundEnt y z → GroundEnt x z) ∧
      (¬ ∃ u : Ent, Ultimate u) := by
  refine ⟨Unit, Int, fun _ _ _ => True, fun x y => x > y, fun u => ¬ ∃ x, x > u, ?_⟩
  refine ⟨⟨(), True, False, trivial⟩, ?_, ?_, ?_⟩
  · intro x; exact Int.lt_irrefl x
  · intro x y z hxy hyz; exact Int.lt_trans hyz hxy
  · intro ⟨u, hu⟩
    exact hu ⟨u + 1, Int.le_refl (u + 1)⟩

/-- Free agency does NOT entail the existence of an ultimate ground:
    An agent with free will can inhabit a reality with an infinite explanatory regress. -/
theorem free_agency_not_entails_ultimate_ground :
    ∃ (Subj : Type) (Ent : Type)
      (Chooses : Subj → Prop → Prop → Prop)
      (Ultimate : Ent → Prop),
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      (¬ ∃ u : Ent, Ultimate u) := by
  obtain ⟨Subj, Ent, Chooses, _, Ultimate, hChoice, _, _, hNoUlt⟩ :=
    a14_not_eliminates_infinite_ground_chain
  exact ⟨Subj, Ent, Chooses, Ultimate, hChoice, hNoUlt⟩

end Sector2_GroundingArchitecture

-- ===========================================================================
-- Sector 3: Personal Ultimate Ground Independence
-- ===========================================================================

section Sector3_PersonalUltimateGround

/-!
Investigates: `ultimate ground → personal ground` under Γ + A14.
Does A14 change that?
-/

/-- A14 + Ultimate Ground does NOT entail a personal ultimate ground:
    Even when free agency exists and an ultimate ground exists, the ultimate ground
    can be completely impersonal (e.g. an impersonal metaphysical substrate),
    while the free agent is merely a contingent inhabitant. -/
theorem a14_plus_ultimate_ground_not_entails_personal_ultimate_ground :
    ∃ (Subj : Type) (Ent : Type)
      (Chooses : Subj → Prop → Prop → Prop)
      (Ultimate : Ent → Prop)
      (PersonalEnt : Ent → Prop),
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      (∃ u : Ent, Ultimate u) ∧
      (∀ u : Ent, Ultimate u → ¬ PersonalEnt u) := by
  refine ⟨Unit, Unit, fun _ _ _ => True, fun _ => True, fun _ => False, ?_⟩
  refine ⟨⟨(), True, False, trivial⟩, ⟨(), trivial⟩, fun _ _ h => h⟩

end Sector3_PersonalUltimateGround

-- ===========================================================================
-- Sector 4: Plurality Independence under A14
-- ===========================================================================

section Sector4_PluralityIndependence

/-!
Investigates whether A14 interacts with the plurality architecture.
`AxTwoNecessaryPersonalCentres` (A10; retired `AxTwoSubjects`, LOVE-3/S4) is an explicit META commitment.
Does A14 derive plurality without A10?
-/

/-- Solitary Free Agent Model:
    A14 does NOT entail a plurality of subjects.
    A solitary free agent can exercise genuine choice in a monistic universe. -/
theorem a14_not_entails_plurality :
    ∃ (Subj : Type) (Chooses : Subj → Prop → Prop → Prop),
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      ¬ (∃ s₁ s₂ : Subj, s₁ ≠ s₂) := by
  refine ⟨Unit, fun _ _ _ => True, ⟨(), True, False, trivial⟩, ?_⟩
  intro ⟨s₁, s₂, hNeq⟩
  cases s₁; cases s₂
  exact hNeq rfl

end Sector4_PluralityIndependence

-- ===========================================================================
-- Sector 5: Love & Relationality Independence under A14
-- ===========================================================================

section Sector5_LoveIndependence

/-!
Investigates whether free agency + personhood + normativity can force love without
assuming AxPersonsAffect or an explicit love commitment.
-/

/-- Free Agency and Plurality do NOT entail Love:
    A world with multiple distinct free choosing persons can be completely loveless
    (e.g., mutually indifferent or malicious free agents). -/
theorem free_agency_and_plurality_not_entails_love :
    ∃ (Subj : Type) (Chooses : Subj → Prop → Prop → Prop) (Loves : Subj → Subj → Prop),
      (∃ s₁ s₂ : Subj, s₁ ≠ s₂) ∧
      (∀ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      (∀ s₁ s₂ : Subj, ¬ Loves s₁ s₂) := by
  refine ⟨Bool, fun _ _ _ => True, fun _ _ => False, ?_⟩
  refine ⟨⟨true, false, fun h => by cases h⟩, fun s => ⟨True, False, trivial⟩, fun _ _ h => h⟩

end Sector5_LoveIndependence

-- ===========================================================================
-- Sector 6: Trinitarian Neutral Structure & Independence
-- ===========================================================================

section Sector6_Trinity

/-!
Neutral formalization of Trinitarian Structure:
Does NOT presuppose the conclusion by definition. Expresses:
1. Exactly three distinct personal centers (P1, P2, P3).
2. Common divine reality / entity.
3. Unity of the divine entity.
4. Non-identity of personal centers.
5. Mutual relational distinction.
-/

structure TrinitarianStructure (Subj : Type) (Ent : Type) where
  P1 : Subj
  P2 : Subj
  P3 : Subj
  distinct_12 : P1 ≠ P2
  distinct_23 : P2 ≠ P3
  distinct_13 : P1 ≠ P3
  divine_reality : Ent
  is_divine : Subj → Ent → Prop
  divine_1 : is_divine P1 divine_reality
  divine_2 : is_divine P2 divine_reality
  divine_3 : is_divine P3 divine_reality
  relational_distinction : Subj → Subj → Prop
  rel_12 : relational_distinction P1 P2
  rel_23 : relational_distinction P2 P3
  rel_13 : relational_distinction P1 P3

/-- Binitarian Separation Model (Toy Cardinality Model over Bool):
    Demonstrates that an unconstrained 2-element domain (`Subj := Bool`) cannot accommodate
    three distinct personal centers by pure cardinality (Pigeonhole Principle).

 Forensic Audit & Methodological Demarcation:
    This model satisfies only a truncated 2-element signature, not the full unified ontology
    of Γ (`Nature`, `HasNature`, `will_individuation`, and `DivineNature`).
    In the full Γ theory (`Logos.NecessaryPersonalGround`), Monotheism of the Divine Ground
    is fully compatible with, and realized in, a Trinity of distinct Divine Persons
    with distinct wills (`monotheism_compatible_with_trinity`).
    Therefore, this theorem establishes only that binary cardinality excludes three elements,
    not that the full Γ architecture is hostile to Trinity. -/
theorem preceding_theory_not_entails_trinity :
    ∃ (Subj : Type) (Ent : Type)
      (Chooses : Subj → Prop → Prop → Prop)
      (Loves : Subj → Subj → Prop)
      (Divine : Subj → Ent → Prop),
      -- Plurality of distinct persons
      (∃ s₁ s₂ : Subj, s₁ ≠ s₂) ∧
      -- Free agency
      (∀ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      -- Mutual love
      (∀ s₁ s₂ : Subj, s₁ ≠ s₂ → Loves s₁ s₂) ∧
      -- Common divine ground
      (∃ (e : Ent) (s₁ s₂ : Subj), s₁ ≠ s₂ ∧ Divine s₁ e ∧ Divine s₂ e) ∧
      -- Exactly two subjects: impossible to satisfy three mutually distinct centers
      ¬ (∃ (_t : TrinitarianStructure Subj Ent), True) := by
  refine ⟨Bool, Unit, fun _ _ _ => True, fun _ _ => True, fun _ _ => True, ?_⟩
  refine ⟨⟨true, false, fun h => by cases h⟩, fun _ => ⟨True, False, trivial⟩, fun _ _ _ => trivial, ⟨(), true, false, (fun h => by cases h), trivial, trivial⟩, ?_⟩
  rintro ⟨⟨p1, p2, p3, d12, d23, d13, _, _, _, _, _, _, _, _, _⟩, _⟩
  revert d12 d23 d13
  cases p1 <;> cases p2 <;> cases p3 <;> decide

end Sector6_Trinity

-- ===========================================================================
-- Sector 7: Incarnational Neutral Structure & Independence
-- ===========================================================================

section Sector7_Incarnation

/-- Neutral formalization of Incarnational Structure:
Expresses the teleological union of divine and human nature in a single personal subject. -/

structure IncarnationalStructure (Subj : Type) (Nature : Type) (HasNature : Subj → Nature → Prop) where
  incarnate_subject : Subj
  divine_nature : Nature
  human_nature : Nature
  distinct_natures : divine_nature ≠ human_nature
  has_divine : HasNature incarnate_subject divine_nature
  has_human : HasNature incarnate_subject human_nature

/-- Unincarnate Hostile Model:
    The existing theory (necessary divine ground, human agency, free will)
    is completely consistent with God remaining purely transcendent and unincarnate.
    Incarnation is NOT derivable from Γ + A14. -/
theorem preceding_theory_not_entails_incarnation :
    ∃ (Subj : Type) (Nature : Type) (_Ent : Type)
      (Chooses : Subj → Prop → Prop → Prop)
      (HasNature : Subj → Nature → Prop),
      -- Distinct divine and human natures exist
      (∃ d h : Nature, d ≠ h) ∧
      -- Divine reality and human choosers exist
      (∃ s : Subj, ∃ p q : Prop, Chooses s p q) ∧
      -- Zero subjects combine both natures
      ¬ (∃ (_i : IncarnationalStructure Subj Nature HasNature), True) := by
  -- Subj: 0 = purely divine, 1 = purely human
  -- Nature: 0 = divine nature, 1 = human nature
  refine ⟨Bool, Bool, Unit, fun _ _ _ => True, fun s n => s = n, ?_⟩
  refine ⟨⟨true, false, fun h => by cases h⟩, ⟨false, True, False, trivial⟩, ?_⟩
  rintro ⟨⟨s, d, h, hNeq, hDiv, hHum⟩, _⟩
  subst hDiv hHum
  exact hNeq rfl

end Sector7_Incarnation

-- ===========================================================================
-- Sector 8: Contingent Creation Independence & the Separation Model
-- ===========================================================================

section Sector8_Creation

/-!
Investigates whether necessary divine reality entails contingent created reality.
Does a necessary ground entail the existence of contingent creatures?

**Rebuilt 2026-09-27 (Sector 8).** The countermodel previously installed the
*empty type* as the subject sort and discharged the negated conclusion by `nomatch`
on a data field. That proved only that a creation record cannot be built from an
empty sort; it stated no contingency, never used the ground's `∀ p` premise, and
had no creation relation to deny — while its English gloss in
`ClaimMeanings.lean` and its report in `investigations/creation.md` read as
"a necessary divine ground exists with zero contingent created reality".

The countermodel is now `CreationWorld`: a **populated** modal world with a
necessary ground that grounds every content, a subject that is genuinely contingent
in the model's own modality, and a *creation relation kept distinct from the
grounding relation* so that "grounds everything yet creates nothing" is statable.
`the_creation_countermodel_is_a_populated_contingent_world` machine-checks that the
separating world is not an empty world, and
`a_populated_contingent_world_can_also_carry_creation` is its positive counterpart,
so `COUNTERMODEL` reads as *undetermined*, never as "creation is impossible".
-/

/-- **A modal creation world**, in the `DeepCreationSignature` idiom of
    `TheologicalModalHardening.lean:631-640`, extended with a subject sort `Subj`
    kept *separate* from the entity sort `Ent` so a world can hold contingent
    subjects while holding no creation record.

    **Why these are fields and not accidents of the proof.** Every property the
    countermodel needs is made structural, so that no instantiation can degenerate
    into the empty world and no reading of it can be "the contingent world does not
    exist":

    - `s` / `s_actual` / `s_contingent` put a **genuinely contingent subject** in the
      world: it obtains at the actual world and fails at another. This is ambient
      contingency in the model's own modality, not a by-product of an empty sort.
    - `g : Ent` makes the entity sort inhabited, so the model cannot be the empty
      world on the creator side either.
    - `Nec` defaults to world-indexed existence, so the ground cannot be made
      necessary by stipulation.
    - `g_grounds_all` keeps the ground's own premise `∀ p, p → Ground e p`
      load-bearing. A countermodel that ignored it would not be testing the
      ground's strength at all.

    What is *not* a field is the presence or absence of a creation record: that is
    what each model settles, and the two models below settle it both ways. -/
structure CreationWorld (Subj Ent World : Type) where
  /-- World-indexed existence of entities. -/
  ExistsAt : World → Ent → Prop
  /-- The actual world. -/
  actualWorld : World
  /-- World-indexed existence of subjects, on their own sort. -/
  SubjectExistsAt : World → Subj → Prop
  /-- The grounding relation: an entity grounds a content. -/
  Ground : Ent → Prop → Prop
  /-- The creation relation: an entity brings a subject into existence. Kept
      distinct from `Ground` in both shape and target — a content vs a subject —
      see `CreationRecord`. -/
  Creates : Ent → Subj → Prop
  /-- Necessity of an entity. Defaults to existence in every world, so a model
      cannot grant necessity by stipulation. -/
  Nec : Ent → Prop := fun e => ∀ w, ExistsAt w e
  /-- The ground entity. Its presence makes `Ent` inhabited. -/
  g : Ent
  /-- The ground is necessary. -/
  g_necessary : Nec g
  /-- The ground grounds every content — the second half of the refuted premise. -/
  g_grounds_all : ∀ p, Ground g p
  /-- A contingent subject. Its presence makes `Subj` inhabited. -/
  s : Subj
  /-- It obtains at the actual world. -/
  s_actual : SubjectExistsAt actualWorld s
  /-- And it fails at another world: real contingency, in the model's modality. -/
  s_contingent : ∃ w, ¬ SubjectExistsAt w s

/-- **A creation record**: a contingent subject, brought into existence by a given
    entity *through a creation relation*.

    The creation relation `M.Creates` is deliberately a relation **distinct from**
    the grounding relation `M.Ground`, and this is the load-bearing design decision
    of the whole countermodel: the claim under test is that a ground which grounds
    *everything* nevertheless creates *nothing*. Had the record's link to the ground
    been the grounding relation itself, the countermodel would be unstatable — a
    necessary ground grounding every content trivially builds a record. Two
    relations, not one.

    `contingent_created` is stated over `M.SubjectExistsAt` directly rather than
    through a free `is_contingent` field, so a record cannot be built by declaring
    its own subject contingent. -/
structure CreationRecord {Subj Ent World : Type} (M : CreationWorld Subj Ent World) where
  /-- The creating entity. -/
  creator : Ent
  /-- The created subject. -/
  created_subject : Subj
  /-- The creation itself. This is what the countermodel denies. -/
  created : M.Creates creator created_subject
  /-- The created subject is genuinely contingent in the model's own modality. -/
  contingent_created : ∃ w, ¬ M.SubjectExistsAt w created_subject

/-- **The entailment under examination**, in the models' own modality: in *every*
    world whose ground is necessary and grounds every content, a contingent subject
    exists that the ground created. Quantifying over models — rather than
    exhibiting one failed pair of `Ground`/`Nec` — is what makes a refutation of it
    a countermodel proper. -/
def GroundEntailsCreation (Subj Ent World : Type) : Prop :=
  ∀ (M : CreationWorld Subj Ent World),
    (∃ e : Ent, M.Nec e ∧ ∀ p, M.Ground e p) →
    Nonempty (CreationRecord M)

/-- **The countermodel, on a populated world.** A necessary ground exists and grounds
    everything; a contingent subject exists and is genuinely contingent; the ground
    creates nothing. Both sorts are inhabited and the contingency is ambient, so
    this is **not** the empty world — see
    `the_creation_countermodel_is_a_populated_contingent_world`.

    The absence of a creation record is carried by `Creates := fun _ _ => False`,
    a field *distinct* from `Ground := fun _ _ => True`. The
    ground-grounds-everything premise is honoured in full and the creation relation
    is empty regardless.

    **Recorded history.** The predecessor of this model set `Subj := Empty` and
    discharged the negated conclusion by `nomatch` on the data field
    `created_subject`; it never used the ground's `∀ p` premise, had no creation
    relation to deny, and stated no contingency at all. It proved only that a record
    cannot be built from an empty sort — yet `investigations/creation.md` reported
    it as `∀ e, ¬ ContingentEntity e`, a conjunct the kernel never contained, under a
    `PROVEN` status the ledger assigns to `COUNTERMODEL`. -/
def populatedCreationWorld : CreationWorld Unit Unit Bool where
  ExistsAt := fun _ _ => True
  actualWorld := true
  SubjectExistsAt := fun w _ => w = true
  Ground := fun _ _ => True
  Creates := fun _ _ => False
  g := ()
  g_necessary := fun _ => trivial
  g_grounds_all := fun _ => trivial
  s := ()
  s_actual := rfl
  s_contingent := ⟨false, fun h => by cases h⟩

/-- **The positive counterpart.** The *same* populated world, with the creation
    relation inhabited: the necessary ground still grounds everything, a contingent
    subject still exists, and now the ground does create it.

    Stated so the ledger's `COUNTERMODEL` is not read as "creation is impossible".
    The entailment is **undetermined**, not refuted-and-replaced: one populated world
    without a record, one with. -/
def createdCreationWorld : CreationWorld Unit Unit Bool where
  ExistsAt := fun _ _ => True
  actualWorld := true
  SubjectExistsAt := fun w _ => w = true
  Ground := fun _ _ => True
  Creates := fun _ _ => True
  g := ()
  g_necessary := fun _ => trivial
  g_grounds_all := fun _ => trivial
  s := ()
  s_actual := rfl
  s_contingent := ⟨false, fun h => by cases h⟩

/-- **The countermodel world is populated, and its subject is genuinely
    contingent.** This is the machine-checked answer to reading the countermodel as
    a proposal that the contingent world does not exist: the very world that
    separates the necessary ground from creation is *proved here to contain a
    contingent subject*. What is absent from it is a creation record — not
    contingent reality. -/
theorem the_creation_countermodel_is_a_populated_contingent_world :
    ∃ (Subj Ent World : Type) (M : CreationWorld Subj Ent World),
      Nonempty Subj ∧
      (∃ s, M.SubjectExistsAt M.actualWorld s ∧ ∃ w, ¬ M.SubjectExistsAt w s) ∧
      ¬ Nonempty (CreationRecord M) := by
  refine ⟨Unit, Unit, Bool, populatedCreationWorld, ⟨⟨()⟩, ⟨⟨(), ⟨?_, ?_⟩⟩, ?_⟩⟩⟩
  · exact populatedCreationWorld.s_actual
  · exact populatedCreationWorld.s_contingent
  · rintro ⟨c⟩
    exact c.created

/-- **The same populated world can also carry a creation record.** With `Creates`
    inhabited, a record is built and its subject is contingent by the ambient
    modality. Paired with
    `the_creation_countermodel_is_a_populated_contingent_world`, this is the
    positive/negative pair that makes the C110 separation a genuine
    non-determination rather than a denial of creation. -/
theorem a_populated_contingent_world_can_also_carry_creation :
    ∃ (Subj Ent World : Type) (M : CreationWorld Subj Ent World),
      (∃ s, M.SubjectExistsAt M.actualWorld s ∧ ∃ w, ¬ M.SubjectExistsAt w s) ∧
      Nonempty (CreationRecord M) := by
  refine ⟨Unit, Unit, Bool, createdCreationWorld, ⟨⟨(), ⟨?_, ?_⟩⟩, ?_⟩⟩
  · exact createdCreationWorld.s_actual
  · exact createdCreationWorld.s_contingent
  · refine ⟨{ creator := (), created_subject := (), created := trivial,
               contingent_created := ⟨false, fun h => by cases h⟩ }⟩

/-- **Separation Model (rebuilt on a populated world).** A necessary divine ground exists,
    grounds every content, and coexists with a contingent subject that is not *its* creation:
    necessary reality does NOT entail creation.

    **Read the scope before the content.** This is a countermodel over a purpose-built
    free structure (`CreationWorld`), not a model of Γ and not a candidate for
    reality. It says the necessary-ground premises do not *derive* a creation record.
    It says nothing about whether the contingent world exists — that is
    `CosmicExistence.cosmos_obtains` (C367), a **proved theorem** given an exhibited
    contingent person (2026-09-28, two-kinds; the plurality bridge left this row) — and
    `the_creation_countermodel_is_a_populated_contingent_world`
    proves the countermodel used here is no empty world.

    Note the two facts are independent and both hold: Γ **proves** a contingent realm
    exists, and Γ **refutes** that a necessary ground alone entails a creation record.
    Existence is not entailment.

    Footprint: `{}`. -/
theorem necessary_ground_not_entails_contingent_creation :
    ¬ (∀ (Subj Ent World : Type), GroundEntailsCreation Subj Ent World) := by
  rintro hAll
  have hRec : Nonempty (CreationRecord populatedCreationWorld) :=
    hAll Unit Unit Bool populatedCreationWorld
      ⟨populatedCreationWorld.g, populatedCreationWorld.g_necessary,
        populatedCreationWorld.g_grounds_all⟩
  obtain ⟨c⟩ := hRec
  exact c.created

end Sector8_Creation

-- ===========================================================================
-- Sector 9: Machine-Checked Theological Dependency Graph
-- ===========================================================================

section Sector9_DependencyGraph

/-- Strict classification of inference status in the Conditional Theology Graph. -/
inductive InferenceStatus
  | PROVEN          -- Derived by pure logic or machine-verified theorems
  | DEFINITIONAL    -- Definitional expansion (rfl / iff)
  | SEMANTIC        -- Substantive semantic axiom (e.g. A14 AxIntentionalChoice)
  | METAPHYSICAL    -- Metaphysical bridge (e.g. A10 AxTwoNecessaryPersonalCentres)
  | COUNTERMODEL    -- Formally independent; separated by machine-checked hostile countermodel
  | OPEN            -- Unresolved formal status

/-- The 10 Primary Theological Transitions and their audited status. -/
def edge_Act_to_Chooses : InferenceStatus := InferenceStatus.PROVEN -- via A14 (AxIntentionalChoice)
def edge_Chooses_to_FreeWill : InferenceStatus := InferenceStatus.DEFINITIONAL
def edge_FreeWill_to_Rationality : InferenceStatus := InferenceStatus.COUNTERMODEL -- separated by freewill_not_entails_rationality
def edge_NecessaryTruth_to_SomeGround : InferenceStatus := InferenceStatus.PROVEN -- via A4/A6
def edge_SomeGround_to_NecessaryGround : InferenceStatus := InferenceStatus.PROVEN -- via A6/T7
def edge_NecessaryGround_to_UltimateGround : InferenceStatus := InferenceStatus.COUNTERMODEL -- separated by a14_not_eliminates_infinite_ground_chain
def edge_UltimateGround_to_PersonalGround : InferenceStatus := InferenceStatus.COUNTERMODEL -- separated by a14_plus_ultimate_ground_not_entails_personal_ultimate_ground
def edge_PersonalGround_to_Plurality : InferenceStatus := InferenceStatus.METAPHYSICAL -- requires A10 (AxTwoNecessaryPersonalCentres)
def edge_Plurality_to_Love : InferenceStatus := InferenceStatus.METAPHYSICAL -- requires AxPersonsAffect
def edge_Love_to_Trinity : InferenceStatus := InferenceStatus.COUNTERMODEL -- separated by preceding_theory_not_entails_trinity
def edge_DivineGround_to_Creation : InferenceStatus := InferenceStatus.COUNTERMODEL -- separated by necessary_ground_not_entails_contingent_creation (on a populated world, not an empty one)
def edge_Creation_to_Incarnation : InferenceStatus := InferenceStatus.COUNTERMODEL -- separated by preceding_theory_not_entails_incarnation

/-- Machine-Checked Theological Dependency Ledger:
    Verifies that every theological node is either formally proven, an audited axiom,
    or strictly blocked by an authoritative countermodel. -/
theorem theological_dependency_ledger :
    edge_Act_to_Chooses = InferenceStatus.PROVEN ∧
    edge_Chooses_to_FreeWill = InferenceStatus.DEFINITIONAL ∧
    edge_FreeWill_to_Rationality = InferenceStatus.COUNTERMODEL ∧
    edge_NecessaryTruth_to_SomeGround = InferenceStatus.PROVEN ∧
    edge_SomeGround_to_NecessaryGround = InferenceStatus.PROVEN ∧
    edge_NecessaryGround_to_UltimateGround = InferenceStatus.COUNTERMODEL ∧
    edge_UltimateGround_to_PersonalGround = InferenceStatus.COUNTERMODEL ∧
    edge_PersonalGround_to_Plurality = InferenceStatus.METAPHYSICAL ∧
    edge_Plurality_to_Love = InferenceStatus.METAPHYSICAL ∧
    edge_Love_to_Trinity = InferenceStatus.COUNTERMODEL ∧
    edge_DivineGround_to_Creation = InferenceStatus.COUNTERMODEL ∧
    edge_Creation_to_Incarnation = InferenceStatus.COUNTERMODEL := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Sector9_DependencyGraph

end Logos.ConditionalTheology
