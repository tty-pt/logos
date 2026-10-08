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
   `atom_not_atemporal`), subjects of the contingent kind exist at no stage
   (`subject_not_everlasting`, now carrying the `ContingentSubjectKind s`
   hypothesis that was always its real content), and `Everlasting ⇏
   NecessaryEntity` (`everlasting_but_contingent`: `Entity.ofAtom 0`). The
   ground is outside every initiation-becoming (`the_ground_not_in_succession`
   — read with the 2026-09-28 succession audit, C458–C462: this is a *non-correlateness*
   result, its proof discarding the `Initiates` conjunct, and C459 shows the same predicate
   holds of every atom) and provably distinct from every subject-correlate
   (`ofGround_ne_ofSubject`) — so hypostatic identity is blocked, not hidden.
   The necessary kind of subject is everlasting instead, by
   `Plurality.necessaryKindSubject_is_necessary` with
   `necessary_implies_everlasting`; the two kinds are differentiated, never
   collapsed.
4. **Claim E (non-hypostatic pairing).** `claimE` witnesses the necessary entity a
   nd the personal ground-type as separate conjuncts: there is a necessary ground
   of reality and a Person grounding Right/Wrong — with no identity line between
   them. The personal conjunct rests on the declared META plurality axiom
   `AxTwoNecessaryPersonalCentres` (via `T5_personExists_from_plurality`); the necessity conjunct
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
open Logos.Agency (Subject State Initiates NecessarySubjectKind ContingentSubjectKind)
open Logos.Plurality (T5_personExists_from_plurality)
open Logos.RecoveredOntologicalGround (GroundOfReality NecessaryGroundOfReality OneEssence ActualEntity)
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
    This is a *derived* relation (footprint `{NecessarySubjectKind, Subject}`), not a new axiom of temporal
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
    vocabulary: `State`, `Initiates`).

    **READING, 2026-09-28 (C458–C462).** The predicate quantifies genuinely and is *real*, but
    it is **non-discriminating**: non-correlateness suffices for it (C458) and it holds of every
    atom as well (C459), so it cannot separate the ground from an atom. Nothing in its body
    mentions an entity-level agency relation, which is why a ground may *produce* while
    `NotInSuccession` holds (C461, `{}`; and live, C467). -/
def NotInSuccession (e : Entity) : Prop :=
  ¬ ∃ (s : Subject) (σ σ' : State) (p : Prop),
      e = EntityOf s ∧ Initiates s σ σ' p

/-- Generic modal transport: if an entity exists in every world, then it is
    present at every stage corresponding to one of those worlds, and its stage
    occurrences are equivalent. This conditional, type-generic lemma does not
    instantiate `Entity.ofGround` or establish metaphysical eternity.
    Footprint: `{}`. -/
theorem necessary_existence_is_stage_uniform
    {World Stage Entity : Type}
    (ExistsAt : World → Entity → Prop)
    (At : Stage → Entity → Prop)
    (stage : Stage → World)
    (e : Entity)
    (hNecessary : ∀ w : World, ExistsAt w e)
    (hAt : ∀ t : Stage, At t e ↔ ExistsAt (stage t) e) :
    ∀ t : Stage, At t e ∧ ∀ u : Stage, At t e ↔ At u e := by
  intro t
  refine ⟨(hAt t).2 (hNecessary (stage t)), fun u => ?_⟩
  constructor
  · intro _
    exact (hAt u).2 (hNecessary (stage u))
  · intro _
    exact (hAt t).2 (hNecessary (stage t))

-- ============================================================================
-- Section 2: Necessity of the ground (all footprint `{}`)
-- ============================================================================

/-- The ground of reality exists in every world: `NecessaryEntity Entity.ofGround`.
    Definitional (world-rigid constructor, VOCAB class). Before this extension
    the live sort satisfied `¬ ∃ e, NecessaryEntity e`; the extension declares
    the ground's world-invariance as a semantic stipulation, not an axiom.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem ofGround_necessary : NecessaryEntity Entity.ofGround := by
  intro w
  trivial

/-- The ground of reality ontologically grounds every actual entity: for every
    actual entity `e`, either it is the ground itself or the ground means
    everything `e` means (`EntityMeans .ofGround p := True`, the explanatory-
    adequacy dual of the atom's `False`). Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_ground_of_reality : GroundOfReality Entity.ofGround := by
  intro e hActual
  exact Or.inr (fun p hEM => True.intro)

/-- HEADLINE — the necessary ground of reality exists: `Entity.ofGround` is a
    necessary entity and the ontological ground of reality.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. This is the live theorem behind the README row
    "Necessary Divine Being / Ground — PROVEN". -/
theorem ofGround_necessary_ground_of_reality : NecessaryGroundOfReality Entity.ofGround :=
  ⟨ofGround_necessary, ofGround_ground_of_reality⟩

/-- The ground is numerically distinct from every subject-correlate: hypostatic
    identity is blocked by constructor injectivity (`Entity.noConfusion`). This
    is why no "necessary Person" claim is derivable from necessity of the ground.
    Footprint: `{Subject}`. -/
theorem ofGround_ne_ofSubject (s : Subject) : Entity.ofGround ≠ EntityOf s := by
  intro h
  exact Entity.noConfusion h

-- ============================================================================
-- Section 3: Necessity → Eternity (everlasting ∧ atemporal), all footprint `{}`
-- ============================================================================

/-- Necessary → Everlasting (task C): because every stage is a world
    (`stageOf t : World`), an entity that exists in every world exists at every
    stage. The argument carries no temporal premise over to the conclusion side.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem necessary_implies_everlasting {e : Entity} :
    NecessaryEntity e → Everlasting e := by
  intro h t
  exact h (stageOf t)

/-- Necessary → Atemporal: a world-rigid entity's existence does not vary across
    stages. Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem necessary_implies_atemporal {e : Entity} :
    NecessaryEntity e → Atemporal e := by
  intro h t₁ t₂
  constructor
  · intro _; exact h (stageOf t₂)
  · intro _; exact h (stageOf t₁)

/-- The ground is everlasting (exists at every stage). Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem the_ground_everlasting : Everlasting Entity.ofGround := by
  exact necessary_implies_everlasting ofGround_necessary

/-- The ground is atemporal (existence not time-modulated). Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem the_ground_atemporal : Atemporal Entity.ofGround := by
  exact necessary_implies_atemporal ofGround_necessary

/-- The ground is outside every initiation-becoming (no transition role).
    Footprint: `{Initiates, State, Subject}`. -/
theorem the_ground_not_in_succession : NotInSuccession Entity.ofGround := by
  rintro ⟨s, σ, σ', p, ⟨hEq, _h⟩⟩
  exact Entity.noConfusion hEq

/-- Reader-facing bundle: the ground is everlasting and atemporal.
    Footprint: `{NecessarySubjectKind, Subject}`. (Deliberately named without "eternal" — see the README
    regeneration guards.) -/
theorem everlasting_and_atemporal_ground :
    Everlasting Entity.ofGround ∧ Atemporal Entity.ofGround :=
  ⟨the_ground_everlasting, the_ground_atemporal⟩

-- ============================================================================
-- Section 4: Separation theorems — the predicates are genuine (footprint `{}`)
-- ============================================================================

/-- Atoms are not everlasting: an atomic entity fails at stage 0.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem atom_not_everlasting : ¬ Everlasting (Entity.ofAtom 1) := by
  intro h
  have hn : ¬ (1 ≤ 0) := by decide
  have h0 := h 0
  rw [ExistsAtTime, ExistsAt, Logos.Entity.EntityExistsAt] at h0
  rw [stageOf, ite_eq_right hn] at h0
  exact Logos.Semantics.TV.noConfusion h0

/-- Atoms are not atemporal: atomic existence varies across stages.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
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
    stage 0 (alias of `atom_not_atemporal`). Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem atom_has_temporal_mode : HasTemporalMode (Entity.ofAtom 1) :=
  atom_not_atemporal

/-- Subjects of the contingent kind exist at no global stage: `stageOf t ≠
    actualWorld` at index `t + 1` (the growing timeline disagrees with the
    always-true valuation), so `ExistsAtTime` never holds for a
    contingent-kind subject-correlate. This is the kind-relative form of the
    old unconditional reading: the hypothesis `ContingentSubjectKind s` is what
    the old semantics `SubjectExistsAt w s := w = actualWorld` asserted of every
    subject. The necessary kind is everlasting instead
    (`Plurality.necessaryKindSubject_is_necessary` with
    `necessary_implies_everlasting`). Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem subject_not_everlasting (s : Subject) (hKind : ContingentSubjectKind s) :
    ¬ Everlasting (EntityOf s) := by
  intro h
  have ht := h 0
  dsimp [ExistsAtTime, ExistsAt, Logos.Entity.EntityExistsAt, Logos.Entity.SubjectExistsAt, EntityOf] at ht
  rcases ht with hk | heq
  · exact hKind hk
  · have hn : ¬ (1 ≤ 0) := by decide
    have hstage : Logos.Semantics.TV.f = (stageOf 0) 1 := by
      rw [stageOf, ite_eq_right hn]
    have hact : (Logos.Entity.actualWorld) 1 = Logos.Semantics.TV.t := rfl
    have hc : Logos.Semantics.TV.f = Logos.Semantics.TV.t := by
      calc
        Logos.Semantics.TV.f = (stageOf 0) 1 := hstage
        _ = Logos.Entity.actualWorld 1 := congrArg (fun w : World => w 1) heq
        _ = Logos.Semantics.TV.t := hact
    exact Logos.Semantics.TV.noConfusion hc

/-- Everlasting ⇏ Necessary: `Entity.ofAtom 0` exists at every stage (`0 ≤ t`
    always) but fails in the all-`f` world — so everlastingness never collapses
    into necessity. Footprint: `{NecessarySubjectKind, Subject}`. -/
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
    conjunct rests on the declared META plurality axiom `AxTwoNecessaryPersonalCentres` (through
    `T5_personExists_from_plurality`; retired `AxTwoSubjects`, LOVE-3/S4); it is the kind-witness for Claim E, never
    an identification of the necessary ground with a subject.
    Footprint: `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem the_personal_type_grounding : ∃ s : Subject, Person s ∧ GroundsRightWrong s := by
  obtain ⟨s, hP⟩ := T5_personExists_from_plurality
  exact ⟨s, hP, person_grounds_normative_order s hP⟩

/-- Claim E (approved non-hypostatic reading): there is a necessary ground of
    reality and a personal ground-type — two conjuncts, no identity line.
    `ofGround_ne_ofSubject` records that the hypostatic conjunction
    `g = EntityOf s ∧ NecessaryEntity g` is impossible for any subject.
    Necessity conjunct: `{Means, Subject}` (via `ofGround_necessary` and
    `ofGround_necessary_ground_of_reality`); the personal conjunct (via
    `the_personal_type_grounding`) is `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem claimE :
    ∃ g : Entity, ∃ s : Subject,
      NecessaryEntity g ∧ NecessaryGroundOfReality g ∧ Person s ∧ GroundsRightWrong s := by
  obtain ⟨s, hP, hG⟩ := the_personal_type_grounding
  exact ⟨Entity.ofGround, s, ofGround_necessary, ofGround_necessary_ground_of_reality, hP, hG⟩

-- ============================================================================
-- Section 6: timelessness vs everlastingness — the two notions separated
-- ============================================================================
-- Section 6: timelessness vs everlastingness — the two notions separated
-- ============================================================================

/-- **Everlasting implies timeless.** The generic step, at the level of the
    predicates and not only at the ground.

    `Everlasting e := ∀ t, ExistsAtTime t e` and
    `Atemporal e := ∀ t₁ t₂, ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e`, so the
    second is literally the first stated twice, and the `↔` is discharged by the
    two one-directional instances. The corpus previously had only the
    ground-level instances (`the_ground_everlasting`, `the_ground_atemporal`,
    both routed through `ofGround_necessary`), which is why
    `CHARACTERISTICS.md` §8 could still list "the text does not distinguish
    timelessness from everlastingness" as open: nothing stated the relation.

    Footprint: `{NecessarySubjectKind, Subject}`. The step is one line, but the
    *predicates* it unfolds are not axiom-free: `ExistsAtTime` → `ExistsAt` →
    `EntityExistsAt` → `SubjectExistsAt` → `NecessarySubjectKind`. The row reads
    no predicate, and this is the same reason `necessary_implies_everlasting` is
    `{NecessarySubjectKind, Subject}` rather than `{}`.
    -/
theorem everlasting_implies_atemporal (e : Entity) :
    Everlasting e → Atemporal e := by
  intro h t₁ t₂
  exact ⟨fun _ => h t₂, fun _ => h t₁⟩

/-- **A contingent-kind subject is timeless but not everlasting.** The
    discriminating counterexample: §8's two notions are not coextensive.

    The second conjunct is `subject_not_everlasting` (this module), which already
    refutes everlastingness at stage 0. The first conjunct is new, and it holds
    for a reason that must be disclosed rather than glossed: under
    `ContingentSubjectKind s` the existence clause reduces to
    `stageOf t = actualWorld`, which is **false at every** `t` — at index `t+1`
    one has `stageOf t (t+1) = TV.f` while `actualWorld (t+1) = TV.t`. So both
    sides of `Atemporal`'s `↔` are false and `Atemporal` is satisfied
    *vacuously*.

    That vacuity is the point of the row, not a defect: it is precisely how an
    entity can be "timeless" while not existing everywhere. A reader who wants
    non-vacuous timelessness in Γ must go through `necessary_implies_atemporal`,
    which is the *necessary* kind, not the contingent one.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem contingent_subject_is_timeless_but_not_everlasting (s : Subject)
    (hKind : ContingentSubjectKind s) :
    Atemporal (EntityOf s) ∧ ¬ Everlasting (EntityOf s) := by
  have hNo : ∀ t : Time, ¬ ExistsAtTime t (EntityOf s) := by
    intro t h
    have h' : NecessarySubjectKind s ∨ Logos.NecessityEternity.stageOf t = actualWorld := by
      simpa [ExistsAtTime, ExistsAt, Logos.Entity.EntityExistsAt,
        Logos.Entity.SubjectExistsAt, EntityOf] using h
    rcases h' with hk | heq
    · exact hKind hk
    · have hn : ¬ (t + 1 ≤ t) := by
        intro hc
        exact absurd (Nat.lt_of_lt_of_le (Nat.lt_succ_self t) hc) (Nat.lt_irrefl _)
      have hstage : TV.f = (Logos.NecessityEternity.stageOf t) (t + 1) := by
        rw [Logos.NecessityEternity.stageOf, ite_eq_right hn]
      have hact : actualWorld (t + 1) = TV.t := rfl
      exact TV.noConfusion
        (hstage.trans ((congrArg (fun w : World => w (t + 1)) heq).trans hact))
  exact ⟨fun t₁ t₂ => ⟨fun h => False.elim (hNo t₁ h), fun h => False.elim (hNo t₂ h)⟩,
    subject_not_everlasting s hKind⟩

/-- **Reader-facing: §8's two temporal notions are distinct, and how.**
    The bundle of the generic implication with the separating counterexample,
    discharging `CHARACTERISTICS.md` §8's "the text does not distinguish
    timelessness from everlastingness" together with the `NÃO reivindicada`
    boundary of `base.txt:1521-1524`.

    **What is established:** `Everlasting` is strictly stronger than `Atemporal`
    *as a shape of statement*, and Γ's vocabulary supplies a kind of entity that
    satisfies the weaker without the stronger.

    **What is NOT established, and must not be read into this row:** Γ has **no
    theorem inhabiting `ContingentSubjectKind`**. Every occurrence of it in the
    corpus is a hypothesis — `LovesAsGround.lean:196`, `CosmicExistence.lean:299`
    and following, with the `Creates` row at `CosmicExistence.lean:695` still
    BLOCKED on a `Creates` relation Γ does not have. So the separating region is
    inhabited in the *models*, not in the *kernel*: this bundle proves the
    vocabulary distinguishes the two notions, **not** that some subject of Γ
    actually falls in the difference. The unconditional schema
    `¬ (Atemporal e → Everlasting e)` is **not derivable** and is deliberately
    not stated — the ground is atemporal and everlasting, and so is
    `Entity.ofAtom 0`.

    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem everlastingness_and_timelessness_are_distinct :
    (∀ e : Entity, Everlasting e → Atemporal e) ∧
      (∀ s : Subject, ContingentSubjectKind s →
        Atemporal (EntityOf s) ∧ ¬ Everlasting (EntityOf s)) :=
  ⟨everlasting_implies_atemporal, fun s hKind =>
    contingent_subject_is_timeless_but_not_everlasting s hKind⟩

end Logos.NecessityEternity

-- Axiom footprint audit (see AGENTS.md: record every footprint in GAPMAP.md)
#print axioms Logos.NecessityEternity.ofGround_necessary
#print axioms Logos.NecessityEternity.ofGround_ground_of_reality
#print axioms Logos.NecessityEternity.ofGround_necessary_ground_of_reality
#print axioms Logos.NecessityEternity.ofGround_ne_ofSubject
#print axioms Logos.NecessityEternity.necessary_existence_is_stage_uniform
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
#print axioms Logos.NecessityEternity.everlasting_implies_atemporal
#print axioms Logos.NecessityEternity.contingent_subject_is_timeless_but_not_everlasting
#print axioms Logos.NecessityEternity.everlastingness_and_timelessness_are_distinct
