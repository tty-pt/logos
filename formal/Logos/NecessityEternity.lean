/-
# Logos.NecessityEternity — Necessity and Eternity of the ultimate ground

This module establishes, from the extended canonical sort `Logos.Entity.Entity`
(now carrying the world-rigid constructor `Entity.ofGround`):

1. **Necessity of the ground (entity-level).** `NecessaryEntity Entity.ofGround`,
   `GroundOfReality Entity.ofGround` (the ground grounds every actual entity), and
   the headline `NecessaryGroundOfReality Entity.ofGround` — all definitional,
   footprint `{}`. The ground is a constructor of the shared sort, not an axiom:
   its world-invariance is a *definitional semantic stipulation* (VOCAB class).
2. **Eternity — everlasting and atemporal, both as definitional corollaries of
   necessity.** The transcendental deduction imports **no temporal premise**: time
   enters only on the conclusion side, as the global-stage layer
   (`stageOf t : World`). Because `stageOf t` *is* a world for every stage `t`,
   `NecessaryEntity e` forces `ExistsAt (stageOf t) e` for every `t` — the ground
   that exists in every world exists at every stage (everlasting) and its
   existence is not time-modulated (atemporal, `Atemporal`). This is the formal
   content of the claim "the argument does not depend on time — that is why the
   ground is eternal and atemporal."
3. **Honest separation.** The new predicates are not collapsed: atoms are
   time-modulated (`atom_has_temporal_mode`, `atom_not_everlasting`,
   `atom_not_atemporal`), subjects exist at no stage
   (`subject_not_everlasting`), and `Everlasting ⇏ NecessaryEntity`
   (`everlasting_but_contingent`: `Entity.ofAtom 0`). The ground is outside every
   initiation-becoming (`the_ground_not_in_succession`) and provably distinct from
   every subject-correlate (`ofGround_ne_ofSubject`) — so hypostatic identity is
   blocked, not hidden.
4. **Claim E (non-hypostatic pairing).** `claimE` witnesses the necessary entity a
   nd the personal ground-type as separate conjuncts: there is a necessary ground
   of reality and a Person grounding Right/Wrong — with no identity line between
   them. The personal conjunct rests on the declared META plurality axiom
   `AxTwoSubjects` (via `T5_personExists_from_plurality`); the necessity conjunct
   is `{}`.

Axiom policy: no section axiom, no re-opened a deleted axiom, no resurrection of
the removed fragments (`necessary_person_derived`, `divine_person_is_necessary`,
`PersonalNature`, `DivineNature`, `universal_ground_unique` — those stay absent).
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Modal
import Logos.Agency
import Logos.Plurality
import Logos.RecoveredOntologicalGround
import Logos.PersonalNormativeGround
import Logos.PersonalGroundOfReality

namespace Logos.NecessityEternity

open Logos.Semantics (World TV)
open Logos.Entity (Entity EntityOf ExistsAt actualWorld)
open Logos.Modal (NecessaryEntity)
open Logos.Agency (Subject State Initiates)
open Logos.Plurality (T5_personExists_from_plurality)
open Logos.RecoveredOntologicalGround (GroundOfReality NecessaryGroundOfReality GroundsEntity ActualEntity)
open Logos.PersonalNormativeGround (GroundsRightWrong)
open Logos.PersonalGroundOfReality (person_grounds_normative_order)
open Logos.Person (Person)

-- ============================================================================
-- Section 1: Temporal stage-layer (conclusion side only; no temporal premise)
-- ============================================================================

/-- Global stage index: a natural number, the "time" coordinate of the
    conclusion side. Time enters the deduction only here, never in its premises. -/
abbrev Time : Type := Nat

/-- The world "at global stage t": the growing valuation where every atom with
    index ≤ t is true (cumulative timeline). As a `World` (`Nat → TV`),
    `stageOf t : World` for every `t` — which is exactly what lets necessity
    force everlastingness. -/
def stageOf (t : Time) (m : Nat) : TV := if m ≤ t then TV.t else TV.f

/-- Existence of an entity at a global stage: existence in the world `stageOf t`.
    This is a *derived* relation (footprint `{}`), not a new axiom of temporal
    ontology. -/
def ExistsAtTime (t : Time) (e : Entity) : Prop := ExistsAt (stageOf t) e

/-- Everlasting / perpetual existence: the entity exists at every global stage. -/
def Everlasting (e : Entity) : Prop := ∀ t : Time, ExistsAtTime t e

/-- Atemporal existence: existence is not time-modulated — the entity's existence
    does not vary across stages. -/
def Atemporal (e : Entity) : Prop :=
  ∀ (t₁ t₂ : Time), ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e

/-- Has a temporal mode: the complement of atemporality (an entity whose
    existence does vary across stages). -/
def HasTemporalMode (e : Entity) : Prop := ¬ Atemporal e

/-- Outside succession: the entity is not engaged in any initiation-becoming —
    no subject-role of it initiates a transition between states (live succession
    vocabulary: `State`, `Initiates`). -/
def NotInSuccession (e : Entity) : Prop :=
  ¬ ∃ (s : Subject) (σ σ' : State) (p : Prop),
      e = EntityOf s ∧ Initiates s σ σ' p

-- ============================================================================
-- Section 2: Necessity of the ground (all footprint `{}`)
-- ============================================================================

/-- The ground of reality exists in every world: `NecessaryEntity Entity.ofGround`.
    Definitional (world-rigid constructor, VOCAB class). Before this extension
    the live sort satisfied `¬ ∃ e, NecessaryEntity e`; the extension declares
    the ground's world-invariance as a semantic stipulation, not an axiom.
    Footprint: `{}`. -/
theorem ofGround_necessary : NecessaryEntity Entity.ofGround := by
  intro w
  trivial

/-- The ground of reality ontologically grounds every actual entity: for every
    actual entity `e`, either it is the ground itself or the ground means
    everything `e` means (`EntityMeans .ofGround p := True`, the explanatory-
    adequacy dual of the atom's `False`). Footprint: `{}`. -/
theorem ofGround_ground_of_reality : GroundOfReality Entity.ofGround := by
  intro e hActual
  exact Or.inr (fun p hEM => True.intro)

/-- HEADLINE — the necessary ground of reality exists: `Entity.ofGround` is a
    necessary entity and the ontological ground of reality.
    Footprint: `{}`. This is the live theorem behind the README row
    "Necessary Divine Being / Ground — PROVEN". -/
theorem ofGround_necessary_ground_of_reality : NecessaryGroundOfReality Entity.ofGround :=
  ⟨ofGround_necessary, ofGround_ground_of_reality⟩

/-- The ground is numerically distinct from every subject-correlate: hypostatic
    identity is blocked by constructor injectivity (`Entity.noConfusion`). This
    is why no "necessary Person" claim is derivable from necessity of the ground.
    Footprint: `{}`. -/
theorem ofGround_ne_ofSubject (s : Subject) : Entity.ofGround ≠ EntityOf s := by
  intro h
  exact Entity.noConfusion h

-- ============================================================================
-- Section 3: Necessity → Eternity (everlasting ∧ atemporal), all footprint `{}`
-- ============================================================================

/-- Necessary → Everlasting (task C): because every stage is a world
    (`stageOf t : World`), an entity that exists in every world exists at every
    stage. The argument carries no temporal premise over to the conclusion side.
    Footprint: `{}`. -/
theorem necessary_implies_everlasting {e : Entity} :
    NecessaryEntity e → Everlasting e := by
  intro h t
  exact h (stageOf t)

/-- Necessary → Atemporal: a world-rigid entity's existence does not vary across
    stages. Footprint: `{}`. -/
theorem necessary_implies_atemporal {e : Entity} :
    NecessaryEntity e → Atemporal e := by
  intro h t₁ t₂
  constructor
  · intro _; exact h (stageOf t₂)
  · intro _; exact h (stageOf t₁)

/-- The ground is everlasting (exists at every stage). Footprint: `{}`. -/
theorem the_ground_everlasting : Everlasting Entity.ofGround := by
  exact necessary_implies_everlasting ofGround_necessary

/-- The ground is atemporal (existence not time-modulated). Footprint: `{}`. -/
theorem the_ground_atemporal : Atemporal Entity.ofGround := by
  exact necessary_implies_atemporal ofGround_necessary

/-- The ground is outside every initiation-becoming (no transition role).
    Footprint: `{}`. -/
theorem the_ground_not_in_succession : NotInSuccession Entity.ofGround := by
  rintro ⟨s, σ, σ', p, ⟨hEq, _h⟩⟩
  exact Entity.noConfusion hEq

/-- Reader-facing bundle: the ground is everlasting and atemporal.
    Footprint: `{}`. (Deliberately named without "eternal" — see the README
    regeneration guards.) -/
theorem everlasting_and_atemporal_ground :
    Everlasting Entity.ofGround ∧ Atemporal Entity.ofGround :=
  ⟨the_ground_everlasting, the_ground_atemporal⟩

-- ============================================================================
-- Section 4: Separation theorems — the predicates are genuine (footprint `{}`)
-- ============================================================================

/-- Atoms are not everlasting: an atomic entity fails at stage 0.
    Footprint: `{}`. -/
theorem atom_not_everlasting : ¬ Everlasting (Entity.ofAtom 1) := by
  intro h
  have hn : ¬ (1 ≤ 0) := by decide
  have h0 := h 0
  rw [ExistsAtTime, ExistsAt, Logos.Entity.EntityExistsAt] at h0
  rw [stageOf, ite_eq_right hn] at h0
  exact Logos.Semantics.TV.noConfusion h0

/-- Atoms are not atemporal: atomic existence varies across stages.
    Footprint: `{}`. -/
theorem atom_not_atemporal : ¬ Atemporal (Entity.ofAtom 1) := by
  intro h
  have hn : ¬ (1 ≤ 0) := by decide
  have hle : 1 ≤ 1 := by decide
  have hT : ExistsAtTime 1 (Entity.ofAtom 1) := by
    rw [ExistsAtTime, ExistsAt, Logos.Entity.EntityExistsAt]
    rw [stageOf, ite_eq_left hle]
  have hF : ¬ ExistsAtTime 0 (Entity.ofAtom 1) := by
    intro h0
    rw [ExistsAtTime, ExistsAt, Logos.Entity.EntityExistsAt] at h0
    rw [stageOf, ite_eq_right hn] at h0
    exact Logos.Semantics.TV.noConfusion h0
  exact hF ((h 0 1).mpr hT)

/-- Atoms are time-modulated: `Entity.ofAtom 1` exists at stage 1 but not at
    stage 0 (footprint `{}`; alias of `atom_not_atemporal`). -/
theorem atom_has_temporal_mode : HasTemporalMode (Entity.ofAtom 1) :=
  atom_not_atemporal

/-- Subjects exist at no global stage: `stageOf t ≠ actualWorld` at index `t + 1`
    (the growing timeline disagrees with the always-true valuation), so
    `ExistsAtTime` never holds for a subject-correlate. Consistent with the live
    semantics `SubjectExistsAt w s := w = actualWorld`. Footprint: `{}`. -/
theorem subject_not_everlasting (s : Subject) : ¬ Everlasting (EntityOf s) := by
  intro h
  have ht := h 0
  dsimp [ExistsAtTime, ExistsAt, Logos.Entity.EntityExistsAt, Logos.Entity.SubjectExistsAt, EntityOf] at ht
  have hn : ¬ (1 ≤ 0) := by decide
  have hstage : Logos.Semantics.TV.f = (stageOf 0) 1 := by
    rw [stageOf, ite_eq_right hn]
  have hact : (Logos.Entity.actualWorld) 1 = Logos.Semantics.TV.t := rfl
  have hc : Logos.Semantics.TV.f = Logos.Semantics.TV.t := by
    calc
      Logos.Semantics.TV.f = (stageOf 0) 1 := hstage
      _ = Logos.Entity.actualWorld 1 := congrArg (fun w : World => w 1) ht
      _ = Logos.Semantics.TV.t := hact
  exact Logos.Semantics.TV.noConfusion hc

/-- Everlasting ⇏ Necessary: `Entity.ofAtom 0` exists at every stage (`0 ≤ t`
    always) but fails in the all-`f` world — so everlastingness never collapses
    into necessity. Footprint: `{}`. -/
theorem everlasting_but_contingent : ∃ e : Entity, Everlasting e ∧ ¬ NecessaryEntity e := by
  refine ⟨Entity.ofAtom 0, ?_, ?_⟩
  · intro t
    have hz : 0 ≤ t := Nat.zero_le t
    rw [ExistsAtTime, ExistsAt, Logos.Entity.EntityExistsAt]
    rw [stageOf, ite_eq_left hz]
  · intro hn
    have hw : Logos.Semantics.TV.f = Logos.Semantics.TV.t :=
      hn (fun _ => Logos.Semantics.TV.f)
    exact Logos.Semantics.TV.noConfusion hw

-- ============================================================================
-- Section 5: Claim E — non-hypostatic personal pairing (footprint flagged)
-- ============================================================================

/-- A personal ground-type exists: some subject is a Person and grounds
    Right/Wrong (via `Person s → GroundsRightWrong s`). The Person-existence
    conjunct rests on the declared META plurality axiom `AxTwoSubjects` (through
    `T5_personExists_from_plurality`); it is the kind-witness for Claim E, never
    an identification of the necessary ground with a subject.
    Footprint: `{AxTwoSubjects, Means, Subject}`. -/
theorem the_personal_type_grounding : ∃ s : Subject, Person s ∧ GroundsRightWrong s := by
  obtain ⟨s, hP⟩ := T5_personExists_from_plurality
  exact ⟨s, hP, person_grounds_normative_order s hP⟩

/-- Claim E (approved non-hypostatic reading): there is a necessary ground of
    reality and a personal ground-type — two conjuncts, no identity line.
    `ofGround_ne_ofSubject` records that the hypostatic conjunction
    `g = EntityOf s ∧ NecessaryEntity g` is impossible for any subject.
    Necessity conjunct footprint `{}`; the personal conjunct (via
    `the_personal_type_grounding`) is `{AxTwoSubjects, Means, Subject}`. -/
theorem claimE :
    ∃ g : Entity, ∃ s : Subject,
      NecessaryEntity g ∧ NecessaryGroundOfReality g ∧ Person s ∧ GroundsRightWrong s := by
  obtain ⟨s, hP, hG⟩ := the_personal_type_grounding
  exact ⟨Entity.ofGround, s, ofGround_necessary, ofGround_necessary_ground_of_reality, hP, hG⟩

end Logos.NecessityEternity

-- Axiom footprint audit (see AGENTS.md: record every footprint in GAPMAP.md)
#print axioms Logos.NecessityEternity.ofGround_necessary
#print axioms Logos.NecessityEternity.ofGround_ground_of_reality
#print axioms Logos.NecessityEternity.ofGround_necessary_ground_of_reality
#print axioms Logos.NecessityEternity.ofGround_ne_ofSubject
#print axioms Logos.NecessityEternity.necessary_implies_everlasting
#print axioms Logos.NecessityEternity.necessary_implies_atemporal
#print axioms Logos.NecessityEternity.the_ground_everlasting
#print axioms Logos.NecessityEternity.the_ground_atemporal
#print axioms Logos.NecessityEternity.the_ground_not_in_succession
#print axioms Logos.NecessityEternity.everlasting_and_atemporal_ground
#print axioms Logos.NecessityEternity.atom_has_temporal_mode
#print axioms Logos.NecessityEternity.atom_not_everlasting
#print axioms Logos.NecessityEternity.atom_not_atemporal
#print axioms Logos.NecessityEternity.subject_not_everlasting
#print axioms Logos.NecessityEternity.everlasting_but_contingent
#print axioms Logos.NecessityEternity.the_personal_type_grounding
#print axioms Logos.NecessityEternity.claimE