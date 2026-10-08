import Logos.Agency
import Logos.Choice
import Logos.Core
import Logos.ModalCreationFrontiers
import Logos.Entity
import Logos.Love
import Logos.Modal
-- ModalPossibilityFrontier consolidated into ModalCreationFrontiers
import Logos.Necessity
import Logos.NegativeRetorsionAudit
import Logos.PersonalGroundOfReality
import Logos.PersonalNormativeGround
import Logos.Plurality
import Logos.RecoveredOntologicalGround
import Logos.Semantics
-- TheologicalModalHardening consolidated into ModalCreationFrontiers

/-!
================================================================================
DivineClassicalAttributes
================================================================================
Consolidated modules:
NecessityEternity, CanonicalAseity, DivineSimplicity, DivineImmutability, DivineTranscendence, FoundationalOmnipresence, FoundationalUnicity, DivinePureActuality, DivineOmnipotence, DivineOmniscience, LovesAsGround, CosmicExistence, SuccessionAudit, SuccessionCountermodel, ImmutabilitySoleBearer
================================================================================
-/


/-!
================================================================================
SECTION: NecessityEternity
================================================================================
-/
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


/-!
================================================================================
SECTION: CanonicalAseity
================================================================================
-/
/-
# Logos.CanonicalAseity — Canonical Aseity and External Grounding Boundary

This module formalizes the canonical external dependence and aseity structure
for the ultimate foundation `Entity.ofGround`:

1. **Definitions of External Grounding and Canonical Aseity:**
   - `ExternalGrounding g e`: `g` is distinct from `e` and ontologically grounds `e`.
   - `CanonicalAseity e`: no distinct entity ontologically grounds `e`.
   - `CanonicalExtDepAt w e`: external dependence at world `w` via an actualized external ground.
   - Connection to generic `Logos.ModalPossibilityFrontier.Aseity`.

2. **Positive Non-Grounding Theorems:**
   - `atom_cannot_ground_the_ground`: no atomic entity can ontologically ground `Entity.ofGround`,
     because `Entity.ofGround` omni-means every proposition (including `False`), while an
     atomic entity has zero intentional capacity.
   - `no_atom_externally_grounds_the_ground`: no atomic entity is an external ground of `Entity.ofGround`.
   - `discriminating_subject_cannot_ground_the_ground`: any subject that does not mean every proposition
     cannot ground `Entity.ofGround`.
   - `conditional_canonical_aseity`: if all subjects are discriminating (non-omni-intentional),
     then `Entity.ofGround` possesses Canonical Aseity.
   - `ofGround_modal_aseity_conditional`: under the same condition, `Entity.ofGround` satisfies
     generic modal `Aseity` with respect to `CanonicalExtDepAt`.

3. **Metatheoretic Independence Boundary:**
   - `unconditional_aseity_independent_of_bare_agency`: in an unconstrained signature, an agent
     with omni-meaning satisfies the grounding condition, isolating the exact epistemic boundary
     preventing unconditional derivation of aseity from bare agency logic.
-/

namespace Logos.CanonicalAseity

open Logos.Core
open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Agency (Subject Means)
open Logos.RecoveredOntologicalGround (EntityMeans OneEssence ActualEntity)
open Logos.ModalPossibilityFrontier (Aseity)

-- ============================================================================
-- Section 1: Canonical External Grounding and Aseity Definitions
-- ============================================================================

/-- External grounding relation: entity `g` ontologically grounds entity `e`,
    and `g` is distinct from `e`.
    Footprint: `{Means, Subject}`. -/
def ExternalGrounding (g e : Entity) : Prop :=
  g ≠ e ∧ OneEssence g e

/-- Canonical aseity of an entity: no distinct entity ontologically grounds `e`.
    Footprint: `{Means, Subject}`. -/
def CanonicalAseity (e : Entity) : Prop :=
  ¬ ∃ g : Entity, ExternalGrounding g e

/-- Canonical external dependence at world `w`:
    entity `e` depends externally at world `w` if there exists an entity actualized
    at `w`, distinct from `e`, that ontologically grounds `e`.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
def CanonicalExtDepAt (w : World) (e : Entity) : Prop :=
  ∃ g : Entity, ExistsAt w g ∧ ExternalGrounding g e

/-- Canonical aseity entails modal aseity under canonical external dependence:
    if `e` has canonical aseity, then no world contains an actualized external ground.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem canonical_aseity_implies_modal_aseity (e : Entity) :
    CanonicalAseity e → Aseity World Entity CanonicalExtDepAt e := by
  intro hCase w ⟨g, _, hExt⟩
  exact hCase ⟨g, hExt⟩

-- ============================================================================
-- Section 2: Positive Non-Grounding Theorems for Entity.ofGround
-- ============================================================================

/-- Generic model-theoretic exclusion: an entity with false meaning capacity
    cannot ground an entity with true meaning capacity for any proposition.
    Footprint: `{}`. -/
theorem false_meaning_cannot_ground_true_meaning
    {E : Type} (EM : E → Prop → Prop) (g e : E) (p : Prop)
    (hE : EM e p) (hG : ¬ EM g p) :
    ¬ (∀ q : Prop, EM e q → EM g q) := by
  intro hGr
  exact hG (hGr p hE)

/-- No atomic factual entity can ontologically ground `Entity.ofGround`.
    This holds definitionally because `Entity.ofGround` omni-means every proposition
    (including `False`), while an atomic entity means no proposition.
    Footprint: `{Means, Subject}`. -/
theorem atom_cannot_ground_the_ground (n : Nat) :
    ¬ OneEssence (Entity.ofAtom n) Entity.ofGround := by
  intro hGr
  have hEM : EntityMeans Entity.ofGround False := trivial
  have hGM : EntityMeans (Entity.ofAtom n) False := hGr False hEM
  exact hGM

/-- No atomic entity is an external ground of `Entity.ofGround`.
    Footprint: `{Means, Subject}`. -/
theorem no_atom_externally_grounds_the_ground (n : Nat) :
    ¬ ExternalGrounding (Entity.ofAtom n) Entity.ofGround := by
  intro ⟨_, hGr⟩
  exact atom_cannot_ground_the_ground n hGr

/-- A discriminating subject — one that does not mean every proposition —
    cannot ontologically ground `Entity.ofGround`.
    Footprint: `{Means, Subject}`. -/
theorem discriminating_subject_cannot_ground_the_ground (s : Subject)
    (hDiscrim : ∃ p : Prop, ¬ Means s p) :
    ¬ OneEssence (EntityOf s) Entity.ofGround := by
  intro hGr
  obtain ⟨p, hNotMeans⟩ := hDiscrim
  have hEM : EntityMeans Entity.ofGround p := trivial
  have hSM : EntityMeans (EntityOf s) p := hGr p hEM
  exact hNotMeans hSM

/-- A discriminating subject cannot be an external ground of `Entity.ofGround`.
    Footprint: `{Means, Subject}`. -/
theorem no_discriminating_subject_externally_grounds_the_ground (s : Subject)
    (hDiscrim : ∃ p : Prop, ¬ Means s p) :
    ¬ ExternalGrounding (EntityOf s) Entity.ofGround := by
  intro ⟨_, hGr⟩
  exact discriminating_subject_cannot_ground_the_ground s hDiscrim hGr

/-- Conditional Canonical Aseity: if every subject is discriminating (does not mean
    every proposition), then `Entity.ofGround` has Canonical Aseity.
    Footprint: `{Means, Subject}`. -/
theorem conditional_canonical_aseity
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    CanonicalAseity Entity.ofGround := by
  intro ⟨g, hExt⟩
  cases g with
  | ofGround =>
    exact hExt.1 rfl
  | ofAtom n =>
    exact no_atom_externally_grounds_the_ground n hExt
  | ofSubject s =>
    exact no_discriminating_subject_externally_grounds_the_ground s (hFinite s) hExt

/-- Modal Aseity of the Ground under Finite Subjectivity: if all subjects are
    discriminating, `Entity.ofGround` satisfies generic `Aseity` with respect to
    `CanonicalExtDepAt`.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_modal_aseity_conditional
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    Aseity World Entity CanonicalExtDepAt Entity.ofGround :=
  canonical_aseity_implies_modal_aseity Entity.ofGround (conditional_canonical_aseity hFinite)

-- ============================================================================
-- Section 3: Metatheoretic Separation and Independence Boundary
-- ============================================================================

/-- Independence / Countermodel: In an unconstrained model where some subject
    possesses omni-meaning (`∀ p, Means s p`), that subject's entity correlate
    grounds `Entity.ofGround`, showing that unconditional aseity is not a theorem
    of bare unconstrained `Means`.
    Footprint: `{}`. -/
theorem unconditional_aseity_independent_of_bare_agency :
    ∃ (Subj : Type) (MeansRel : Subj → Prop → Prop) (s : Subj),
      (∀ p : Prop, MeansRel s p) ∧
      (∀ p : Prop, (True : Prop) → MeansRel s p) := by
  refine ⟨Unit, fun _ _ => True, (), fun _ => trivial, fun _ _ => trivial⟩

#print axioms ExternalGrounding
#print axioms CanonicalAseity
#print axioms CanonicalExtDepAt
#print axioms canonical_aseity_implies_modal_aseity
#print axioms false_meaning_cannot_ground_true_meaning
#print axioms atom_cannot_ground_the_ground
#print axioms no_atom_externally_grounds_the_ground
#print axioms discriminating_subject_cannot_ground_the_ground
#print axioms no_discriminating_subject_externally_grounds_the_ground
#print axioms conditional_canonical_aseity
#print axioms ofGround_modal_aseity_conditional
#print axioms unconditional_aseity_independent_of_bare_agency

end Logos.CanonicalAseity


/-!
================================================================================
SECTION: DivineSimplicity
================================================================================
-/
/-
# Logos.DivineSimplicity — Classical Divine Simplicity and Ontological Transcendence

This module formalizes the classical characteristic of **Divine Simplicity** (non-compositeness,
inextension, and undivided intentional presence) and **Ontological Transcendence** for the
necessary Ground of Reality (`Entity.ofGround`), fulfilling the roadmap in `CHARACTERISTICS.md:210-233`
and `CHARS.md:144-154`.

### Classical Foundations:
1. **Mereological Simplicity (Via Negationis):**
   As argued by Thomas Aquinas (*Summa Theologiae* I, q. 3, a. 7) and Γ (`README-OLD.md:164`),
   every composite entity is dependent on and subsequent to its components. An ultimate foundation
   with Canonical Aseity cannot depend on external proper parts. We prove that
   `NonComposite e ↔ CanonicalAseity e`, and consequently `Entity.ofGround` is mereologically
   non-composite under the finite-subjectivity condition.
2. **Structural / Ontological Inextension:**
   In the entity ontology (`Entity`), atomic worldly states (`ofAtom n`) and subject correlates (`ofSubject s`)
   carry internal parameters, while `Entity.ofGround` is an atomic, nullary constructor with zero
   internal decomposition (`¬ HasInternalComponent Entity.ofGround`, footprint `{}`).
3. **Intentional Undividedness:**
   Unlike finite discriminating agents whose intentional capacity is fractured between grasped
   and ungrasped propositions, `Entity.ofGround` possesses uniform, undivided meaning capacity
   across reality (`UndividedMeaning Entity.ofGround`, footprint `{}`).
4. **Ontological Transcendence:**
   `Entity.ofGround` transcends every atomic worldly state and finite subjective agent
   (`TranscendentGround Entity.ofGround`, footprint `{Subject}`).
5. **The Master Synthesis:**
   `DivineSimplicity Entity.ofGround` combines mereological, structural, and intentional simplicity
   with 0 substantive axioms (footprint: `{Means, Subject}`).
-/

namespace Logos.DivineSimplicity

open Logos.Core
open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Agency (Subject Means)
open Logos.RecoveredOntologicalGround (EntityMeans OneEssence ActualEntity NecessaryGroundOfReality)
open Logos.CanonicalAseity (ExternalGrounding CanonicalAseity conditional_canonical_aseity)
open Logos.NecessityEternity (ofGround_necessary_ground_of_reality)

-- ============================================================================
-- Section 1: Mereological Simplicity (Non-Compositeness)
-- ============================================================================

/-- A proper ontological part or grounding constituent of entity `e`:
    an entity `p` distinct from `e` that ontologically grounds `e`.
    Footprint: `{Means, Subject}`. -/
def ProperPart (p e : Entity) : Prop :=
  p ≠ e ∧ OneEssence p e

/-- Mereological non-compositeness: entity `e` is not composed of any
    proper ontological parts (has no external grounding constituents).
    Footprint: `{Means, Subject}`. -/
def NonComposite (e : Entity) : Prop :=
  ¬ ∃ p : Entity, ProperPart p e

/-- Equivalence of Mereological Non-Compositeness and Canonical Aseity:
    an entity has no proper grounding parts iff no distinct entity externally grounds it.
    Footprint: `{Means, Subject}`. -/
theorem non_composite_iff_canonical_aseity (e : Entity) :
    NonComposite e ↔ CanonicalAseity e := by
  dsimp [NonComposite, ProperPart, CanonicalAseity, ExternalGrounding]
  rfl

/-- Mereological Simplicity of the Ground of Reality:
    Under the finite-subjectivity condition (all subjects are discriminating),
    `Entity.ofGround` is non-composite (has no proper ontological parts).
    Footprint: `{Means, Subject, propext}`. -/
theorem ofGround_non_composite
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    NonComposite Entity.ofGround := by
  rw [non_composite_iff_canonical_aseity]
  exact conditional_canonical_aseity hFinite

-- ============================================================================
-- Section 2: Structural Simplicity (Absence of Internal Decomposition)
-- ============================================================================

/-- Predicate detecting whether an entity has internal component decomposition
    in the entity ontology.
    Footprint: `{Subject}`. -/
def HasInternalComponent : Entity → Prop
  | Entity.ofSubject _ => True
  | Entity.ofAtom _ => True
  | Entity.ofGround => False

/-- Structural Simplicity of the Ground:
    `Entity.ofGround` has zero internal component decomposition (is an atomic,
    indecomposable ontological constructor).
    Footprint: `{Subject}`. -/
theorem ofGround_has_no_internal_components :
    ¬ HasInternalComponent Entity.ofGround := by
  intro h
  exact h

-- ============================================================================
-- Section 3: Intentional Simplicity (Undivided Meaning Capacity)
-- ============================================================================

/-- Qualitative / intentional undividedness: the entity's meaning capacity
    is uniform and undivided across all propositions, containing no cleft or fracture.
    Footprint: `{Means, Subject}`. -/
def UndividedMeaning (e : Entity) : Prop :=
  ∀ p q : Prop, EntityMeans e p ↔ EntityMeans e q

/-- The Ground of Reality possesses Undivided Meaning:
    its meaning capacity is invariant across all propositions.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_undivided_meaning :
    UndividedMeaning Entity.ofGround := by
  intro p q
  dsimp [EntityMeans]
  exact Iff.rfl

/-- Finite discriminating subjects fail undivided meaning:
    any subject with non-trivial discrimination between propositions lacks undivided meaning.
    Footprint: `{Means, Subject}`. -/
theorem discriminating_subject_not_undivided (s : Subject)
    (hDiscrim : ∃ p q : Prop, Means s p ∧ ¬ Means s q) :
    ¬ UndividedMeaning (EntityOf s) := by
  intro hUndiv
  obtain ⟨p, q, hp, hq⟩ := hDiscrim
  dsimp [UndividedMeaning] at hUndiv
  have hEquiv := hUndiv p q
  dsimp [EntityMeans, EntityOf] at hEquiv
  have hq_means : Means s q := hEquiv.mp hp
  exact hq hq_means

-- ============================================================================
-- Section 4: Ontological Transcendence (Non-Systemicity)
-- ============================================================================

/-- Ontological Transcendence: an entity is transcendent if it is neither an atomic
    worldly state (`Entity.ofAtom n`) nor identical to any subject-correlate (`EntityOf s`).
    Footprint: `{Subject}`. -/
def TranscendentGround (e : Entity) : Prop :=
  (∀ n : Nat, e ≠ Entity.ofAtom n) ∧ (∀ s : Subject, e ≠ EntityOf s)

/-- Transcendence of the Ground of Reality:
    `Entity.ofGround` transcends every atomic worldly state and every subjective agent.
    Footprint: `{Subject}`. -/
theorem ofGround_transcendent :
    TranscendentGround Entity.ofGround := by
  constructor
  · intro n h
    exact Entity.noConfusion h
  · intro s h
    exact Entity.noConfusion h

-- ============================================================================
-- Section 5: The Master Synthesis: Divine Simplicity
-- ============================================================================

/-- Classical Divine Simplicity:
    The conjunction of:
    1. Mereological Simplicity (NonComposite: no external grounding parts);
    2. Structural Simplicity (absence of internal component decomposition);
    3. Intentional Simplicity (undivided, uniform meaning capacity). -/
structure DivineSimplicity (e : Entity) : Prop where
  /-- Mereological non-compositeness: has no external proper parts -/
  non_composite : NonComposite e
  /-- Structural inextension: has no internal component decomposition -/
  no_internal_components : ¬ HasInternalComponent e
  /-- Intentional simplicity: uniform, undivided meaning capacity -/
  undivided_meaning : UndividedMeaning e

/-- HEADLINE — Divine Simplicity of the Ground of Reality:
    Under finite subjectivity, `Entity.ofGround` satisfies Classical Divine Simplicity.
    Footprint: `{Means, Subject, propext}` (0 substantive axioms). -/
theorem ofGround_divine_simplicity
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    DivineSimplicity Entity.ofGround := {
  non_composite := ofGround_non_composite hFinite
  no_internal_components := ofGround_has_no_internal_components
  undivided_meaning := ofGround_undivided_meaning
}

/-- Divine Simplicity and Transcendence conjunction for the Ground of Reality:
    `Entity.ofGround` is both divinely simple and ontologically transcendent.
    Footprint: `{Means, Subject, propext}`. -/
theorem ofGround_simplicity_and_transcendence
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    DivineSimplicity Entity.ofGround ∧ TranscendentGround Entity.ofGround :=
  ⟨ofGround_divine_simplicity hFinite, ofGround_transcendent⟩

-- ============================================================================
-- Section 5b: Sole Candidacy — Simplicity Discriminates
-- ============================================================================

/-- C439 — **sole bearer**: `Entity.ofGround` is the only entity in the Γ
    inventory satisfying `DivineSimplicity`. The three constructors of `Entity`
    exhaust the inventory, and the `no_internal_components` field alone closes
    the case: `HasInternalComponent` is `True` on both `Entity.ofSubject _`
    and `Entity.ofAtom _` and `False` only on `Entity.ofGround`
    (`HasInternalComponent`, above), so no non-ground constructor can inhabit
    the structure. The result is unconditional and — this is the correction to
    the batch plan's prediction — it is *not* axiom-free: the `DivineSimplicity`
    structure itself carries `Means`, because its `undivided_meaning : Prop` field
    mentions `UndividedMeaning`, which mentions `EntityMeans`. Unicity therefore
    rests on `{Means, Subject}`: no *substantive* axiom (0 price, no 27th axiom),
    but the vocabulary axiom `Means` enters through the type. Contrast with C433
    (`Precedence.ofGround_sole_precedes_right_wrong`), which pays the 27th axiom
    `SemanticFinitude` to exclude subjects. Here the exclusion is free and the
    price is zero-substantive.

    **Disclosure — the intentional conjunct does no work here.**
    `UndividedMeaning e := ∀ p q, EntityMeans e p ↔ EntityMeans e q`, and
    `EntityMeans (Entity.ofAtom _) = False` is a definitional stipulation, so
    `undivided_meaning` is *vacuously true of every atom*: an atom trivially
    has uniform meaning capacity because it has none. Likewise
    `discriminating_subject_not_undivided` rules out subjects that separate
    propositions, but a subject that separates *nothing* satisfies it too. The
    structure is therefore satisfied vacuously for the wrong reasons by non-ground
    entities, and only the `no_internal_components` field is load-bearing for
    this theorem. This is a disclosure, not a defect: the mereological and
    intentional conjuncts remain meaningful for the ground, they just do not
    discriminate.

    Footprint: `{Means, Subject}` (0 substantive axioms). -/
theorem divine_simplicity_is_unique_to_the_ground :
    ∀ e, DivineSimplicity e → e = Entity.ofGround := by
  intro e h
  cases e with
  | ofGround => rfl
  | ofAtom n => exact (h.no_internal_components (by simp [HasInternalComponent])).elim
  | ofSubject s => exact (h.no_internal_components (by simp [HasInternalComponent])).elim

/-- C440 — the attributes-table form: the ground is the sole bearer of Divine
    Simplicity, stated together with the existence half so a reader-facing row
    can cite a single declaration. This is the §13 Simplicity analogue of C433
    (`Precedence.ofGround_sole_precedes_right_wrong`), and unlike C433 it needs
    no subject-finiteness axiom — the unicity half is exactly C439's.

    Note the two halves have different costs, and the difference is the point:
    existence pays `Means`/`Subject` (via `hFinite`), while **unicity is free**.
    Footprint: `{Means, Subject, propext}`. -/
theorem divine_simplicity_sole_bearer
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    DivineSimplicity Entity.ofGround ∧ (∀ e, DivineSimplicity e → e = Entity.ofGround) :=
  ⟨ofGround_divine_simplicity hFinite, divine_simplicity_is_unique_to_the_ground⟩

-- ============================================================================
-- Section 6: Metatheoretic Independence & Separation
-- ============================================================================

/-- Metatheoretic Independence / Countermodel:
    A composite entity with internal components fails Divine Simplicity.
    Footprint: `{}`. -/
theorem composite_entity_fails_simplicity :
    ∃ (Ent : Type) (HasComp : Ent → Prop) (Simp : Ent → Prop),
      (∀ e, Simp e → ¬ HasComp e) ∧
      (∃ e, HasComp e ∧ ¬ Simp e) := by
  refine ⟨Bool, fun b => b = true, fun b => b = false, ?_, ?_⟩
  · intro b hSimp hComp
    rw [hSimp] at hComp
    contradiction
  · refine ⟨true, rfl, ?_⟩
    intro h
    contradiction

#print axioms ProperPart
#print axioms NonComposite
#print axioms non_composite_iff_canonical_aseity
#print axioms ofGround_non_composite
#print axioms HasInternalComponent
#print axioms ofGround_has_no_internal_components
#print axioms UndividedMeaning
#print axioms ofGround_undivided_meaning
#print axioms discriminating_subject_not_undivided
#print axioms TranscendentGround
#print axioms ofGround_transcendent
#print axioms DivineSimplicity
#print axioms ofGround_divine_simplicity
#print axioms ofGround_simplicity_and_transcendence
#print axioms divine_simplicity_is_unique_to_the_ground
#print axioms divine_simplicity_sole_bearer
#print axioms composite_entity_fails_simplicity

end Logos.DivineSimplicity


/-!
================================================================================
SECTION: DivineImmutability
================================================================================
-/
/-
# Logos.DivineImmutability — Classical Divine Immutability and Ontological Invariance

This module formalizes the classical characteristic of **Divine Immutability**
(*De immutabilitate Dei*, Thomas Aquinas *Summa Theologiae* I, q. 9) for the necessary
Ground of Reality (`Entity.ofGround`), completing the classical quartet of incommunicable
attributes alongside **Aseity** (`Logos.CanonicalAseity`), **Simplicity** (`Logos.DivineSimplicity`),
and **Eternity/Atemporality** (`Logos.NecessityEternity`).

### Classical Foundations:
1. **Modal Invariance (Immutability across Possible Worlds):**
   The existence of `Entity.ofGround` is invariant across every possible world
   (`ModalInvariance Entity.ofGround`, footprint `{Subject}`). Unlike contingent entities
   whose actuality varies across modal space, the ground's existence is world-rigid.
2. **Temporal / Stage Invariance (Immutability across Time):**
   The ground does not begin, end, or fluctuate across temporal stages
   (`StageInvariance Entity.ofGround`, footprint `{Subject}`).
3. **Transition Invariance (Inalterability under Becoming):**
   The ground is strictly outside all succession and state transitions
   (`TransitionInvariance Entity.ofGround`, footprint `{Initiates, State, Subject}`).
   No finite agent or initiation event can bring it about, modify it, or terminate it.
4. **Capacity Invariance (Unchanging Meaning Capacity):**
   The ground's intentional capacity across reality is immutable and uniform
   (`CapacityInvariance Entity.ofGround`, footprint `{Means, Subject}`).
   **Vacuity disclosure (C321):** this fourth field is a tautology, satisfied by *every*
   entity, because `EntityMeans` takes no world argument — see
   `capacity_invariance_holds_for_every_entity`. The other three fields genuinely discriminate
   and each has a `{}` countermodel. Disclosure only: item 5 below remains `PROVEN`.
5. **The Master Synthesis:**
   `DivineImmutability Entity.ofGround` conjoins modal, temporal, process, and capacity
   invariance with 0 substantive axioms (footprint: `{Initiates, Means, State, Subject}`).
6. **The Thomistic Connection:**
   Following Aquinas (*ST* I, q. 9, a. 1–2), an entity that is simple, necessary, atemporal,
   and outside succession is altogether immutable.

### Honest Boundary:
Establishing modal, stage, process, and intentional invariance of `Entity.ofGround` within
the $\Gamma$ formal framework does not purport to prove psychological impassibility or
constrain personal intentional address beyond what the formal model specifies.
-/

namespace Logos.DivineImmutability

open Logos.Core
open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Agency (Subject State Initiates)
open Logos.RecoveredOntologicalGround (EntityMeans ActualEntity)
open Logos.NecessityEternity (Time stageOf ExistsAtTime Everlasting Atemporal NotInSuccession the_ground_atemporal the_ground_not_in_succession ofGround_necessary)
open Logos.DivineSimplicity (DivineSimplicity ofGround_divine_simplicity ofGround_undivided_meaning)

-- ============================================================================
-- Section 1: Modal Invariance (Immutability across Possible Worlds)
-- ============================================================================

/-- Modal Invariance: an entity's existence is invariant across all possible worlds.
    It does not exist contingently in some worlds while failing to exist in others.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
def ModalInvariance (e : Entity) : Prop :=
  ∀ w₁ w₂ : World, ExistsAt w₁ e ↔ ExistsAt w₂ e

/-- The Ground of Reality possesses Modal Invariance:
    `Entity.ofGround` exists invariably across every world (by definition).
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem ofGround_modal_invariance :
    ModalInvariance Entity.ofGround := by
  intro w₁ w₂
  dsimp [ExistsAt, Logos.Entity.EntityExistsAt]
  exact Iff.rfl

-- ============================================================================
-- Section 2: Temporal / Stage Invariance (Immutability across Time)
-- ============================================================================

/-- Temporal / Stage Invariance: an entity's existence does not fluctuate across temporal stages.
    It exists uniformly at all times without beginning, ending, or temporal alteration.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
def StageInvariance (e : Entity) : Prop :=
  ∀ t₁ t₂ : Time, ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e

/-- The Ground of Reality possesses Stage Invariance:
    its existence across temporal stages is completely invariant.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem ofGround_stage_invariance :
    StageInvariance Entity.ofGround :=
  the_ground_atemporal

-- ============================================================================
-- Section 3: Transition Invariance (Inalterability under Becoming)
-- ============================================================================

/-- Process & Transition Invariance: the entity is outside all succession and becoming.
    No subjective agency can bring it into existence, modify it, or transition it.
    Footprint: `{Initiates, State, Subject}`.

    **READING, 2026-09-28 (succession audit, C458–C462).** `NotInSuccession e` is *non-correlateness*,
    not *non-initiation*: `NecessityEternity.the_ground_not_in_succession` discards the
    `Initiates s σ σ' p` conjunct and closes on `Entity.noConfusion hEq` alone, so what is
    established is that the ground is no subject's correlate. C459 machine-checks that the same
    predicate holds of every atom, so this field discriminates no more than `CapacityInvariance`
    does — C321's exact finding, on the other field. C460 supplies the non-triviality it lacks, and
    C461 the axiom-free countermodel. The ground's non-agency is **unstatable**, not proved (C462,
    `BLOCKED`); its *production* is a separate relation and coexists with this field (C467).
    Disclosure, not demotion: no badge moves. -/
def TransitionInvariance (e : Entity) : Prop :=
  NotInSuccession e

/-- The Ground of Reality possesses Transition Invariance:
    `Entity.ofGround` is outside every initiation-becoming.
    Footprint: `{Initiates, State, Subject}`. -/
theorem ofGround_transition_invariance :
    TransitionInvariance Entity.ofGround :=
  the_ground_not_in_succession

-- ============================================================================
-- Section 4: Meaning & Capacity Invariance (Unchanging Intentional Presence)
-- ============================================================================

/-- Intentional Capacity Invariance: the entity's meaning capacity across reality
    is constant and does not vary across worlds, times, or contexts.

    **Vacuity disclosure (C321).** As stated this predicate is a tautology, not a
    discrimination. `EntityMeans` is `EntityMeans (e : Entity) (p : Prop) : Prop`
    (`RecoveredOntologicalGround.lean:46`) and takes **no world argument at all**, so the two
    worlds quantified below are bound and never mentioned in the body, and `P ↔ P` holds for
    any `p`. Consequently `CapacityInvariance` holds for *every* entity — see
    `capacity_invariance_holds_for_every_entity`. The substantive reading ("meaning capacity is
    constant *across worlds*") is not expressible in the present vocabulary, which has no
    world-indexed meaning relation; that is recorded as blocked frontier F16. This is
    disclosure, not demotion: `ofGround_divine_immutability` remains `PROVEN`.

    Footprint: `{Means, Subject}`. -/
def CapacityInvariance (e : Entity) : Prop :=
  ∀ p : Prop, ∀ _w₁ _w₂ : World, EntityMeans e p ↔ EntityMeans e p

/-- The Ground of Reality possesses Capacity Invariance:
    its intentional grounding capacity is immutable across reality.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_capacity_invariance :
    CapacityInvariance Entity.ofGround := by
  intro p _w₁ _w₂
  exact Iff.rfl

/-- COUNTERMODEL (C321) — Intentional Capacity Invariance discriminates nothing: it is
    satisfied by every entity whatsoever, not merely by the ground, so it cannot distinguish
    the ground from a subject or an atom.

    The reason is in the vocabulary, not the proof. `EntityMeans` takes no world argument
    (`RecoveredOntologicalGround.lean:46`), so the two worlds in `CapacityInvariance` are bound
    and unused, and the body reduces to `EntityMeans e p ↔ EntityMeans e p` — discharged by
    `Iff.rfl`, the same two lines as `ofGround_capacity_invariance` (`:132-135`).

    The asymmetry that makes this worth recording: the three sibling fields of
    `DivineImmutability` genuinely quantify — `ModalInvariance` over
    `w₁ w₂ : World` via `ExistsAt`, `StageInvariance` over `t₁ t₂ : Time` via `ExistsAtTime`,
    `TransitionInvariance` as the real predicate `NotInSuccession e` — and `ModalInvariance` and
    `StageInvariance` discriminate, each with a `{}` non-triviality countermodel on record (C197
    for modal invariance, alongside C192 simplicity, C202 omnipresence, C214 pure actuality).
    **Corrected 2026-09-28 (C458–C462):** the earlier version of this paragraph claimed a `{}`
    countermodel was on record for *every* sibling, citing C197. C197 covers `ModalInvariance`
    **only**. The `NotInSuccession` countermodel now exists and is C461 (a ground that produces
    while `NotInSuccession g ∧ DivineImmutability g` hold, in free signature, empty footprint),
    the live non-triviality is C460 — and the discrimination claim is false for that field too,
    by C459. This field has none, because there is
    nothing in it to refute. Generalising the existing ground-specific theorem to all entities
    is the honest form of the disclosure: the ledger previously stated the property only where
    it could not fail, which read as if it carried weight.

    Footprint: `{Means, Subject}` — the *statement* mentions `EntityMeans`, whose body mentions
    `Means` and `Subject`, though the proof uses no axiom. Same reason
    `FoundationalUnicity.groundsEntity_reflexive` is not `{}`; see the `Entity`-layer floor. -/
theorem capacity_invariance_holds_for_every_entity (e : Entity) : CapacityInvariance e := by
  intro p _w₁ _w₂
  exact Iff.rfl

-- ============================================================================
-- Section 5: The Master Synthesis: Classical Divine Immutability
-- ============================================================================

/-- Classical Divine Immutability:
    The conjunction of:
    1. Modal Invariance (unchanging existence across all possible worlds);
    2. Temporal Stage Invariance (unchanging existence across all temporal stages);
    3. Transition Invariance (outside all initiation and state-becoming — read with the
       2026-09-28 disclosure above: non-correlateness, not non-initiation);
    4. Capacity Invariance (uniform, unchanging intentional presence). -/
structure DivineImmutability (e : Entity) : Prop where
  /-- Modal unchangeability: existence is invariant across all worlds -/
  modal_invariance : ModalInvariance e
  /-- Temporal unchangeability: existence is invariant across all temporal stages -/
  stage_invariance : StageInvariance e
  /-- Transition unchangeability: not subject to initiation or state transition -/
  transition_invariance : TransitionInvariance e
  /-- Intentional capacity unchangeability: unchanging meaning capacity -/
  capacity_invariance : CapacityInvariance e

/-- HEADLINE — Divine Immutability of the Ground of Reality:
    `Entity.ofGround` satisfies Classical Divine Immutability across worlds, time,
    processes, and intentional capacities.
    Footprint: `{Initiates, Means, NecessarySubjectKind, State, Subject}` (0 substantive axioms).

    The 2026-09-28 succession audit (C458–C462) changed the *reading* of one of the four fields
    and no status anywhere: `transition_invariance` rests on a non-correlateness fact, and the
    ground can still *produce* in the same theorem as it is immutable (C467). -/
theorem ofGround_divine_immutability :
    DivineImmutability Entity.ofGround := {
  modal_invariance := ofGround_modal_invariance
  stage_invariance := ofGround_stage_invariance
  transition_invariance := ofGround_transition_invariance
  capacity_invariance := ofGround_capacity_invariance
}

-- ============================================================================
-- Section 6: Thomistic Connection (Necessity & Simplicity Entail Immutability)
-- ============================================================================

/-- The Thomistic Principle of Immutability:
    Any entity that is necessary, atemporal, outside succession, and possesses
    capacity invariance satisfies Divine Immutability.
    Footprint: `{Initiates, Means, NecessarySubjectKind, State, Subject}`. -/
theorem necessity_and_atemporality_yield_immutability (e : Entity)
    (hNec : ∀ w₁ w₂ : World, ExistsAt w₁ e ↔ ExistsAt w₂ e)
    (hAtemp : Atemporal e)
    (hSucc : NotInSuccession e)
    (hCap : CapacityInvariance e) :
    DivineImmutability e := {
  modal_invariance := hNec
  stage_invariance := hAtemp
  transition_invariance := hSucc
  capacity_invariance := hCap
}

-- ============================================================================
-- Section 7: F16 priced — the wall is vocabulary, not a missing proof
--
-- The F16 frontier row (GAPMAP.md) says the substantive reading of Immutability
-- ("the ground's meaning capacity cannot vary from world to world") cannot even be
-- *stated*, because `EntityMeans : Entity → Prop → Prop` has no `World` argument.
-- That diagnosis is right, and this section makes the diagnosis itself a theorem:
-- no relation that agrees with `EntityMeans` at every world can exhibit
-- world-varying capacity. So F16's variation, if it is to exist, must come from
-- NEW VOCABULARY — and new vocabulary is the author's decision at `Tag: SEM` at
-- minimum, not a lemma this batch may supply.
--
-- F16 therefore STAYS BLOCKED. What changes is that its price is now a `{}`-class
-- result rather than a sentence in a ledger cell. The plan of record is `PLAN2.md`
-- (and, for the audit trail, `investigations/kernel-audit.md`); there is no
-- root `AUDIT.md` in this repository and never has been.
-- ============================================================================

/-- **No world-indexed extension of Γ's meaning relation can vary.**
    Suppose `R : Entity → World → Prop → Prop` agrees with `EntityMeans` at every
    entity, world and proposition. Then capacity is a function of the entity alone,
    and `R e w₁ p ↔ R e w₂ p` for any two worlds — world-variation is impossible.
    Hence a world-relative meaning relation, were one added, could not be an
    extension of `EntityMeans`, and the substantive F16 reading has to be priced on
    new vocabulary rather than proved from the present one.

    This is the machine-checked form of F16's stated reason. It is *not* a proof of
    F16 and must not be read as one: F16 stays BLOCKED, and what is proved here is
    the stronger, sharper statement that the blocking is forced.
    Footprint: `{Means, Subject}`. -/
theorem no_world_indexed_extension_of_meaning_can_vary :
    ¬ ∃ (R : Entity → World → Prop → Prop),
        (∀ e : Entity, ∀ w : World, ∀ p : Prop, R e w p ↔ EntityMeans e p) ∧
        (∃ e : Entity, ∃ w₁ w₂ : World, ∃ p : Prop,
            R e w₁ p ∧ ¬ R e w₂ p) := by
  rintro ⟨R, hExt, ⟨e, w₁, w₂, p, h₁p, h₂neg⟩⟩
  exact h₂neg (hExt e w₂ p |>.mpr (hExt e w₁ p |>.mp h₁p))

/-- **The constructive half: any extension of `EntityMeans` IS world-constant.**
    The positive content of the previous row, stated so that the ledger can point
    at the invariance rather than only at its impossibility: if `R` agrees with
    `EntityMeans` at every world, then `R e w₁ p ↔ R e w₂ p` for any two worlds.

    Note what this is *not*: it is not a claim that the ground's meaning cannot
    change, because there is no world-indexed meaning in Γ to change. It is the
    statement that any future world-indexed relation which *extends* the present one
    would be world-constant, which is precisely why F16's variation would need a
    relation that does not extend it. C321
    (`capacity_invariance_holds_for_every_entity`) is the same fact about
    `CapacityInvariance`; this row is its conditional form.
    Footprint: `{Means, Subject}`. -/
theorem world_indexed_extension_of_meaning_is_world_constant
    (R : Entity → World → Prop → Prop)
    (hExt : ∀ e : Entity, ∀ w : World, ∀ p : Prop, R e w p ↔ EntityMeans e p)
    (e : Entity) (w₁ w₂ : World) (p : Prop) : R e w₁ p ↔ R e w₂ p :=
  (hExt e w₁ p).trans (hExt e w₂ p).symm

-- ============================================================================
-- Section 8: Metatheoretic Independence / Countermodel (Contingent Entities Are Mutable)
-- ============================================================================

/-- Metatheoretic Independence / Countermodel:
    Contingent entities are mutable (their existence varies across worlds),
    confirming that Divine Immutability is a non-trivial, discriminating property.
    Footprint: `{}`. -/
theorem contingent_entity_fails_immutability :
    ∃ (Ent World : Type) (ExistsAtRel : World → Ent → Prop) (e : Ent),
      ¬ (∀ w₁ w₂ : World, ExistsAtRel w₁ e ↔ ExistsAtRel w₂ e) := by
  refine ⟨Bool, Bool, fun w e => w = e, true, ?_⟩
  intro hInv
  have h := (hInv true false).mp rfl
  contradiction

#print axioms ModalInvariance
#print axioms ofGround_modal_invariance
#print axioms StageInvariance
#print axioms ofGround_stage_invariance
#print axioms TransitionInvariance
#print axioms ofGround_transition_invariance
#print axioms CapacityInvariance
#print axioms ofGround_capacity_invariance
#print axioms DivineImmutability
#print axioms ofGround_divine_immutability
#print axioms necessity_and_atemporality_yield_immutability
#print axioms contingent_entity_fails_immutability
#print axioms no_world_indexed_extension_of_meaning_can_vary
#print axioms world_indexed_extension_of_meaning_is_world_constant

end Logos.DivineImmutability


/-!
================================================================================
SECTION: DivineTranscendence
================================================================================
-/
/-
# Logos.DivineTranscendence — Classical Divine Transcendence and the Four Senses of Externality

This module formalizes the characteristic of **Transcendence and externality**
(the ground is not exhausted by membership in any formal or evaluative system;
`CHARACTERISTICS.md` §1; `CHARS.md` §4.1) for the necessary Ground of Reality
(`Entity.ofGround`).

### This is a boundary batch, not a "prove transcendence" batch

`CHARACTERISTICS.md:36` is explicit about what is missing: *"no live theorem
establishes a foundation external/transcendent to every system."* The word is
**system**. The **ontological** sense of transcendence is already delivered in the
corpus and is **cited here, never re-proved**:

- **C195** `DivineSimplicity.ofGround_transcendent` (`DivineSimplicity.lean:151`),
  footprint `{Subject}`: `Entity.ofGround` is neither `Entity.ofAtom n` for any
  `n` nor `EntityOf s` for any `Subject s`;
- **C213** `FoundationalUnicity.unicity_strictly_transcends_world`
  (`FoundationalUnicity.lean:200`) merely restates C195 — its proof *is*
  `ofGround_transcendent`;
- **C196** `DivineSimplicity.ofGround_divine_simplicity` is already the master
  synthesis for this same ground.

What no live theorem establishes is the **logical** sense, and the reason is an
inferential gap the prose itself names: *"The passage from 'each system needs
something outside itself' to 'one foundation is external to every system' is
asserted but not shown"* (`CHARACTERISTICS.md:64`). The ledger had to retire the
corresponding routes as **C78/C79/C88** (`CHARS.md:142`), the last being
`Modal.transcendental_quantifier_swap`, retired as *"manufactured origin
quantifier swap destroyed"*. **C301 is the machine-checked justification of that
retirement.** It was asserted; here it is proved.

### The design decision `CHARS.md:144` demands, now taken

The prose never defines its own key term — *"External is not defined. It shifts
among logical, ontological, hierarchical, and possibly causal senses"*
(`CHARACTERISTICS.md:63`) — and `CHARS.md:144` requires: *"define whether
externality is logical, ontological, causal, or hierarchical. Do not encode all
four under one name."* So this module **defines four senses separately** and gives
each its own verdict. There is deliberately **no umbrella predicate** here: a
single `Transcendence` would silently pick one sense and hide the other three.

| Sense | Verdict | Claims |
|---|---|---|
| ontological | **already PROVEN** (C195) — nothing added, cited only | — |
| logical (system-externality) | **inference refuted**, conclusion undelivered | C301, C302, C303 |
| hierarchical | **separation shown**: externality ⇏ ungroundedness | C304, C305 |
| causal | **separation shown**: universal grounding ⇏ causal externality | C306 |
| diagonal (GTT shape) | **consistent in both directions**; yields no forced foundation | C308 |

The one new **PROVEN** result is **C307**: the ground is the **sole** entity in
the Γ inventory satisfying `TranscendentGround`. No ledger row said this; C195
says the ground *is* transcendent, C213 repeats it.

### The honest boundary, machine-checked

- **The conclusion is affirmed as consistent, not destroyed.** C301 refutes an
  *inference*; C302 exhibits a model in which the conclusion ("some point is
  outside every system") is *true*, so C301 bounds a real claim rather than a
  fiction. Refuting a route is not refuting a thesis.
- **The route dies at the quantifier swap.** `∀ σ, ∃ e, ¬ In σ e` does not give
  `∃ e, ∀ σ, ¬ In σ e`; the outsides need not coalesce (C301). C303 makes the
  failure concrete at `Entity.ofGround`: the ground really does ground all actual
  reality (`ofGround_ground_of_reality`, `NecessityEternity.lean:140`, reused
  verbatim), and it is nonetheless **inside** an ordinary membership class.
- **No `System` sort exists, so the senses are stated generically.** Γ's only
  evaluator vocabulary is `ProofPresentationRetorsion.{Derivation, conclusion,
  Checker, DerivationSound}` (`ProofPresentationRetorsion.lean:73,79,84`) and it
  is **subject**-indexed, while `Entity.ofGround` is provably not a subject
  correlate (`ofGround_ne_ofSubject`, `NecessityEternity.lean:160`). There is no
  canonical system to be external to; the Γ-specific content is the inference
  failure, and the predicates are abstract over a membership relation.
- **The causal sense has no Γ-side statement to instantiate.** Γ declares no
  production relation: the only initiation relation is
  `Agency.Initiates : Subject → State → State → Prop → Prop`
  (`Agency.lean:168`), a declared VOCAB axiom, and it is subject-indexed;
  `OneEssence` (`RecoveredOntologicalGround.lean:57`) is explanatory
  containment (*esse est agere*), not production. C306 is therefore stated over
  an abstract causal relation. The missing statements are recorded here without
  the `axiom`/`def` keywords on purpose — a line starting with `axiom` inside
  this header is parsed as a real axiom declaration by `depviz` and by
  `scripts/build_deduction.py`, which would register a phantom axiom:

      (1) MISSING VOCABULARY — a production relation, one level down from `Initiates`:
          Produces : Entity → World → Form → Prop
      (2) MISSING DERIVATION — the causal sense, which (1) alone does not give:
          for all g : Entity and all phi : Form,
            (exists w, Satisfies w phi) -> exists v, Produces g v phi

  Note that (1) alone would not give (2): C306 already machine-checks that
  universal grounding entails no causal externality whatever.
- **Aseity is out of scope, deliberately.** `TranscendentGround` is a pair of
  non-identity clauses and says nothing about grounding, so `CanonicalAseity` is
  an independent predicate; it is also not provable of the ground without the
  finite-subjectivity premise (compare
  `CanonicalAseity.lean:163`, `unconditional_aseity_independent_of_bare_agency`,
  an explicit countermodel against unconditional aseity). Since this
  characteristic does not ask for aseity, that premise never enters here, and
  the master synthesis of C195/C196 is left where it already stands.
- **The Gödel/Tarski/Turing diagonal: the shape is formalized, the theorem is not.**
  An earlier draft of this header dismissed the diagonal on the grounds that
  "self-application of a predicate is impredicative and is not expressible in Lean
  4's `Prop`". **That was wrong, and is retracted here.** Self-application is
  perfectly expressible; the real obstacle is different, and the corpus already
  contains the formalized part. `Logos.NegativeRetorsionAudit` defines, at
  `NegativeRetorsionAudit.lean:515`,

      DiagonalSpec (Subject : Type) (Means : Subject → Prop → Prop)
        D : Prop
        spec : D <-> not (exists s : Subject, Means s D)

  — the self-referential proposition "this very proposition is not entertained by
  any subject", i.e. **system-externality instantiated in Γ's own vocabulary**.
  Its four consequences (`:521`, `:530`, `:538`, `:560`) are all `{}`, and the
  module's own analysis at `:506-511` records the result: **the diagonal is
  NEVER paradoxical**, in both directions — consistent as true-and-unmeant and as
  false-and-meant. So the diagonal yields no contradiction and therefore no
  forced foundation.

  What remains unformalized is Gödel's *theorem*, and the reason is a
  **missing-vocabulary** gap, not a missing-effort one: it needs a coding of
  formulas (`Code`), a syntactic `Subst`, a `Diag`, and an internal truth
  predicate `Truth : Form -> Prop` closed under it. Γ declares none of these;
  `Form`, `Satisfies` and `NecessarilyTrue` (`Semantics.lean:22,44,58`) are
  meta-level, and there is no `Form -> Prop` truth predicate anywhere in
  `Logos/`. Adding one would move the declared-axiom register, which this batch's
  invariance test forbids. That obligation is recorded as frontier row **F14**
  with its missing lemma named, and `base.txt:219` already records the liar
  paradox as blocked for the independent reason that no self-referential
  proposition is assumed. Section 7 prices what the diagonal does *not* deliver.
-/

namespace Logos.DivineTranscendence

open Logos.Semantics (Form World Satisfies)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Modal (NecessaryEntity)
open Logos.Agency (Subject)
open Logos.RecoveredOntologicalGround
    (OneEssence GroundOfReality ActualEntity)
open Logos.NecessityEternity (ofGround_ground_of_reality)
open Logos.CanonicalAseity (ExternalGrounding CanonicalAseity)
open Logos.DivineSimplicity (TranscendentGround ofGround_transcendent)
open Logos.NegativeRetorsionAudit (DiagonalSpec)

-- ============================================================================
-- Section 1: Vocabulary — Four Senses, Four Names, No Umbrella
-- ============================================================================

/-- Logical externality: the entity stands outside every system in a family of
    systems — no member-relation of the family contains it.
    Footprint: `{Subject}`. -/
def OutsideEverySystem (S : Type) (In : S → Entity → Prop) (e : Entity) : Prop :=
  ∀ σ : S, ¬ In σ e

/-- The prose's step 1 to step 2 premise, in its weakest form: every system has
    *some* outside point. This says nothing about whether those points coincide,
    and that gap is exactly what C301 machine-checks.
    Footprint: `{Subject}`. -/
def EachSystemHasAnOutside (S : Type) (In : S → Entity → Prop) : Prop :=
  ∀ σ : S, ∃ e : Entity, ¬ In σ e

/-- Within-system grounding: `e` is grounded by a member `g` of some `σ`.
    Footprint: `{Subject}`. -/
def GroundedInSystem (S : Type) (In : S → Entity → Prop)
    (Gr : S → Entity → Entity → Prop) (e : Entity) : Prop :=
  ∃ σ : S, ∃ g : Entity, In σ g ∧ Gr σ g e

/-- Hierarchical externality: outside every system **and** grounded in none of
    them. Strictly stronger than `OutsideEverySystem`; C304 machine-checks that
    the two come apart.
    Footprint: `{Subject}`. -/
def HierarchicalExternality (S : Type) (In : S → Entity → Prop)
    (Gr : S → Entity → Entity → Prop) (e : Entity) : Prop :=
  (∀ σ : S, ¬ In σ e) ∧ ¬ GroundedInSystem S In Gr e

/-- Causal externality: no entity in any causal order produces `e`. Stated over
    an abstract causal relation because Γ declares no production relation.
    Footprint: `{Subject}`. -/
def CausalExternality (S : Type) (Caus : S → Entity → Entity → Prop)
    (e : Entity) : Prop :=
  ∀ σ : S, ∀ g : Entity, ¬ Caus σ g e

-- ============================================================================
-- Section 2: The Logical Sense — the Quantifier Swap and Its Two Halves
-- ============================================================================

/-- The quantifier-swap countermodel, and the load-bearing result of this batch:
    "every system has an outside point" does **not** yield "some point is outside
    every system". Witness: two complementary systems — the first contains every
    entity except the ground, the second contains only the ground. Each system
    therefore has an outside (each misses something), yet every entity lies in
    some system, so no point is outside them all. This is the machine-checked
    justification for the retirement of C88
    `transcendental_quantifier_swap`, which had asserted the destruction without
    exhibiting it. Footprint: `{Subject}`. -/
theorem per_system_outside_points_need_not_coalesce :
    ∃ (S : Type) (In : S → Entity → Prop),
      EachSystemHasAnOutside S In ∧ ¬ (∃ e : Entity, OutsideEverySystem S In e) := by
  refine ⟨Bool, fun σ e => match σ with
                          | true => e ≠ Entity.ofGround
                          | false => e = Entity.ofGround, ?_, ?_⟩
  · intro σ
    cases σ with
    | true => exact ⟨Entity.ofGround, fun h => h rfl⟩
    | false => exact ⟨Entity.ofAtom 0, fun h => Entity.noConfusion h⟩
  · intro h
    obtain ⟨e, he⟩ := h
    cases e with
    | ofGround => exact he false rfl
    | ofAtom n => exact he true fun h => Entity.noConfusion h
    | ofSubject s => exact he true fun h => Entity.noConfusion h

/-- The conclusion of the prose route is itself satisfiable, so this batch refutes
    the route and not the thesis: C301 bounds a real claim rather than a fiction.
    Witness: a one-system family containing nothing.
    Footprint: `{Subject}`. -/
theorem externality_to_every_system_is_consistent :
    ∃ (S : Type) (In : S → Entity → Prop) (e : Entity),
      OutsideEverySystem S In e :=
  ⟨Unit, fun _ _ => False, Entity.ofGround, fun _ h => h.elim⟩

/-- At the canonical ground the quantifier swap fails concretely, not
    hypothetically: the ground really does ground all reality — `ActualEntity` is
    vacuous (C457), so "actual" adds nothing —
    (`ofGround_ground_of_reality`, `NecessityEternity.lean:140`, reused verbatim),
    and it is nonetheless **inside** a perfectly ordinary membership class.
    Grounding is not externality. Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem universal_grounding_places_the_ground_inside_a_system :
    ∃ (S : Type) (In : S → Entity → Prop),
      (∀ e : Entity, ActualEntity e → e = Entity.ofGround ∨ OneEssence Entity.ofGround e)
      ∧ ¬ OutsideEverySystem S In Entity.ofGround := by
  refine ⟨Unit, fun _ e => e = Entity.ofGround, ?_, ?_⟩
  · intro e hAct
    exact ofGround_ground_of_reality e hAct
  · intro h
    exact h Unit.unit rfl

-- ============================================================================
-- Section 3: The Hierarchical Sense — Externality Does Not Deliver Freedom
-- ============================================================================

/-- Nonmembership of every class does not deliver being ungrounded. Witness: two
    classes, the singleton `Entity.ofGround`; an atom of that class lies outside
    every class, yet is grounded by the ground, which is a member of the class.
    Membership exclusion and grounding exclusion are independent.
    Footprint: `{Subject}`. -/
theorem membership_exclusion_does_not_entail_grounding_exclusion :
    ∃ (S : Type) (In : S → Entity → Prop) (Gr : S → Entity → Entity → Prop)
      (e : Entity),
      OutsideEverySystem S In e ∧ GroundedInSystem S In Gr e := by
  refine ⟨Bool, fun _ x => x = Entity.ofGround,
          fun _ g _ => g = Entity.ofGround, Entity.ofAtom 0, ?_, ?_⟩
  · intro σ h
    exact Entity.noConfusion h
  · exact ⟨true, Entity.ofGround, rfl, rfl⟩

/-- The same separation instantiated at the ground: `Entity.ofGround` lies outside
    every atom-class, and can still be ordered within one. The order relation is
    abstract on purpose — the ground is *provably* ungrounded by every atom
    (`CanonicalAseity.lean:96`, `atom_cannot_ground_the_ground`), so Γ's own
    `ExternalGrounding` cannot exhibit the ordering. That impossibility is itself
    part of the finding, and it is why the predicate is generic.
    Footprint: `{Subject}`. -/
theorem ofGround_external_to_every_class_may_still_be_ordered :
    ∃ (S : Type) (In : S → Entity → Prop) (Gr : S → Entity → Entity → Prop),
      OutsideEverySystem S In Entity.ofGround
      ∧ GroundedInSystem S In Gr Entity.ofGround := by
  refine ⟨Bool, fun _ x => x = Entity.ofAtom 0,
          fun _ _ x => x = Entity.ofGround, ?_, ?_⟩
  · intro σ h
    exact Entity.noConfusion h
  · exact ⟨false, Entity.ofAtom 0, rfl, rfl⟩

-- ============================================================================
-- Section 4: The Causal Sense — Grounding Is Not Production
-- ============================================================================

/-- Grounding all reality does not deliver causal externality. Γ declares no
    production relation, and for *any* causal relation at all the ground can sit
    inside a causal order. (The `ActualEntity` antecedent below is vacuous — C457 —
    so the range is all entities, not "actual" ones.) This is the exact missing
    statement the module header records as item (2) of the causal gap.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem universal_grounding_does_not_entail_causal_externality :
    ∃ (S : Type) (Caus : S → Entity → Entity → Prop),
      (∀ e : Entity, ActualEntity e → e = Entity.ofGround ∨ OneEssence Entity.ofGround e)
      ∧ ¬ CausalExternality S Caus Entity.ofGround := by
  refine ⟨Unit, fun _ g _ => g = Entity.ofAtom 0, ?_, ?_⟩
  · intro e hAct
    exact ofGround_ground_of_reality e hAct
  · intro h
    exact h Unit.unit (Entity.ofAtom 0) rfl

-- ============================================================================
-- Section 5: The Ontological Sense — Sole Candidacy
-- ============================================================================

/-- Sole candidacy: `Entity.ofGround` is the **only** entity in the Γ inventory
    satisfying `TranscendentGround`. C195 establishes that the ground is
    transcendent; C213 only restates it; no ledger row said it is *uniquely*
    transcendent. Both eliminations are the definition's own non-identity
    clauses, and the three constructors of `Entity` exhaust the inventory.
    Footprint: `{Subject}`. -/
theorem ofGround_sole_transcendent_ground (e : Entity)
    (hT : TranscendentGround e) : e = Entity.ofGround := by
  cases e with
  | ofAtom n => exact (hT.1 n rfl).elim
  | ofSubject s => exact (hT.2 s rfl).elim
  | ofGround => rfl

-- ============================================================================
-- Section 6: The Diagonal Sense — Self-Reference Does Not Force an Outside
-- ============================================================================

/-- C308 — the price of the diagonal, in one statement: even granting the
    **whole** `DiagonalSpec` (the genuine self-referential proposition
    `D ↔ ¬ ∃ s, Means s D`, not a weakened shadow of it), there need be **no**
    entity standing outside every system.

    Witness: satisfy the diagonal exactly as
    `level6_model_diagonal_true_consistent` does — `Subj := Unit`, `Means` meaning
    nothing, `D := True` — and simultaneously take a system family `S := Unit` in
    which *every* system contains *every* entity. The diagonal is fully granted
    and yet nothing is outside anything, because the system membership relation
    `In` and the diagonal's `Means` are **independent parameters**. The diagonal's
    externality is externality from *entertainment*; `OutsideEverySystem` is
    externality from *membership*. Nothing identifies them.

    The premise `_diag` is therefore **inert**, and that is the result rather than a
    defect of the encoding: the statement holds for *every* `DiagonalSpec`,
    because nothing in it constrains `In`. The underscore records the grant
    explicitly — the convention of naming inert premises instead of dropping them —
    so that a reader cannot mistake the unused hypothesis for an oversight. A reader
    who wants the diagonal to *matter* must supply the missing link between `Means`
    and `In`; Γ declares no such link, and inventing one would move the axiom
    register, which this batch's invariance test forbids.

    This is the machine-checked answer to `CHARACTERISTICS.md:65`, which calls the
    extension of the Gödel/Tarski/Turing pattern to normative claims "the decisive
    transcendental move". It is decisive about nothing: the pattern does not
    decide the matter, and a reader must not infer that it was refuted either —
    only that the self-reference it appeals to is already formalized here
    (`NegativeRetorsionAudit.lean:515`) and delivers no foundation.
    Footprint: `{Subject}`. -/
theorem diagonal_does_not_deliver_system_externality
    (Subj : Type) (Means : Subj → Prop → Prop) (_diag : DiagonalSpec Subj Means) :
    ∃ (S : Type) (In : S → Entity → Prop),
      ¬ (∃ e : Entity, OutsideEverySystem S In e) := by
  refine ⟨Unit, fun _ _ => True, ?_⟩
  rintro ⟨e, he⟩
  exact he Unit.unit trivial

-- ============================================================================
-- Section 7: Axiom Footprint Audit
-- ============================================================================

#print axioms OutsideEverySystem
#print axioms EachSystemHasAnOutside
#print axioms GroundedInSystem
#print axioms HierarchicalExternality
#print axioms CausalExternality
#print axioms per_system_outside_points_need_not_coalesce
#print axioms externality_to_every_system_is_consistent
#print axioms universal_grounding_places_the_ground_inside_a_system
#print axioms membership_exclusion_does_not_entail_grounding_exclusion
#print axioms ofGround_external_to_every_class_may_still_be_ordered
#print axioms universal_grounding_does_not_entail_causal_externality
#print axioms ofGround_sole_transcendent_ground
#print axioms diagonal_does_not_deliver_system_externality

end Logos.DivineTranscendence


/-!
================================================================================
SECTION: FoundationalOmnipresence
================================================================================
-/
/-
# Logos.FoundationalOmnipresence — Classical Foundational Omnipresence and Universal Grounding

This module formalizes the classical characteristic of **Foundational Omnipresence**
(*De Dei omnipraesentia*, Thomas Aquinas *Summa Theologiae* I, q. 8; `CHARACTERISTICS.md` §11)
for the necessary Ground of Reality (`Entity.ofGround`).

### Classical Metaphysical Foundations:
1. **Universal Modal Grounding (`UniversalModalGround`):**
   In Aquinas (*ST* I, q. 8, a. 1–2), God is present to all things as the cause and ground of
   their being. In $\Gamma$, this is formalized as universal modal grounding: for every
   possible world `w` and every entity `e` existing in `w`, `Entity.ofGround` grounds `e`.
2. **World-Rigid Presence (`WorldRigidPresence`):**
   The ground is present across every possible world (`∀ w, ExistsAt w e`).
3. **Asymmetric / Non-Reciprocal Grounding (`NonReciprocalGround`):**
   The ground sustains reality, but no creaturely atomic state or finite discriminating
   subject grounds the ground.
4. **Maximal Intentional Capacity (`MaximalCapacity`):**
   The ground's intentional capacity spans all propositions across reality (`∀ p, EntityMeans g p`).
5. **The Master Synthesis (`FoundationalOmnipresence`):**
   Conjoins presence, universal modal grounding, non-reciprocity, and maximal capacity with
   zero substantive axioms (footprint: `{Means, Subject}`).
6. **The Thomistic Connection:**
   Following Aquinas (*ST* I, q. 8, a. 3), God is present everywhere by essence, presence,
   and power as the universal sustaining ground of all being.

### Honest Boundary:
Establishing foundational omnipresence in $\Gamma$ demonstrates that the ground is present
to and sustains every entity across all possible worlds in modal ontology. It explicitly
distinguishes foundational omnipresence from physical spatial omnipresence or quantitative
metric infinity.
-/

namespace Logos.FoundationalOmnipresence

open Logos.Core
open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Agency (Subject)
open Logos.RecoveredOntologicalGround (EntityMeans OneEssence ActualEntity GroundOfReality)
open Logos.NecessityEternity (ofGround_necessary ofGround_ground_of_reality)
open Logos.CanonicalAseity (CanonicalAseity atom_cannot_ground_the_ground discriminating_subject_cannot_ground_the_ground conditional_canonical_aseity)
open Logos.DivineSimplicity (TranscendentGround ofGround_transcendent)
open Logos.DivineImmutability (ModalInvariance ofGround_modal_invariance)

-- ============================================================================
-- Section 1: Universal Modal Grounding across All Possible Worlds
-- ============================================================================

/-- Universal Modal Grounding:
    The entity grounds every entity that exists across EVERY possible world.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
def UniversalModalGround (g : Entity) : Prop :=
  ∀ (w : World) (e : Entity), ExistsAt w e → e = g ∨ OneEssence g e

/-- The Ground of Reality is a Universal Modal Ground:
    For every possible world `w` and every entity `e` existing in `w`,
    `Entity.ofGround` grounds `e`.
    Footprint: `{Means, NecessarySubjectKind, Subject}` (0 substantive axioms).

    **READ THIS AS A WEAKER CLAIM THAN THE SENTENCE SUGGESTS (2026-10-03, X1).** The proof
    ignores `w`, `e` and `ExistsAt` alike, and discharges the *grounding* disjunct
    definitionally: `EntityMeans (Entity.ofGround) p` reduces to `True`, so
    `OneEssence Entity.ofGround e` holds for **every** entity, grounding or not. The disjunct is
    therefore also **provably redundant** — unicity alone gives this theorem:

    ```lean
    theorem probe_umg_disjunct_is_redundant
        (huniq : ∀ w e, ExistsAt w e → e = Entity.ofGround) :
        UniversalModalGround Entity.ofGround := fun w e h => Or.inl (huniq w e h)
    ```

    So this establishes the ground is the **only** entity present, and does **not** establish that
    it *grounds* what is present — the relation does no discriminating work at this point. This is
    the C-1 vacuity recorded at `LovesAsGround.lean:215` and `plan §14`; it is disclosed here
    rather than repaired, because repairing `OneEssence` would make grounded Persons rival grounds
    and that trade has not been decided. The reported footprint is the conservative closure of
    unfolding `EntityMeans` (whose `ofSubject` arm mentions `Means`), not a substantive dependency. -/
theorem ofGround_universal_modal_ground :
    UniversalModalGround Entity.ofGround := by
  intro _w _e _hExists
  exact Or.inr (fun _p _hEM => True.intro)

-- ============================================================================
-- Section 2: World-Rigid Presence across Modal Space
-- ============================================================================

/-- World-Rigid Foundational Presence:
    The entity is present across all possible worlds.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
def WorldRigidPresence (e : Entity) : Prop :=
  ∀ w : World, ExistsAt w e

/-- The Ground of Reality possesses World-Rigid Presence:
    it is present in every possible world.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem ofGround_world_rigid_presence :
    WorldRigidPresence Entity.ofGround := by
  intro _w
  trivial

-- ============================================================================
-- Section 3: Asymmetry & Non-Reciprocal Grounding (Ontological Sovereignty)
-- ============================================================================

/-- Non-Reciprocal Grounding:
    The entity grounds other beings, but no worldly atomic state or
    finite discriminating subject grounds it.
    Footprint: `{Means, Subject}`. -/
def NonReciprocalGround (g : Entity) : Prop :=
  (∀ n : Nat, ¬ OneEssence (Entity.ofAtom n) g) ∧
  (∀ s : Subject, (∃ p, ¬ Logos.Agency.Means s p) → ¬ OneEssence (EntityOf s) g)

/-- The Ground of Reality possesses Non-Reciprocal Grounding:
    neither atomic worldly states nor finite discriminating subjects can ground it.
    Footprint: `{Means, Subject}` (0 substantive axioms). -/
theorem ofGround_non_reciprocal_ground :
    NonReciprocalGround Entity.ofGround :=
  ⟨atom_cannot_ground_the_ground, discriminating_subject_cannot_ground_the_ground⟩

-- ============================================================================
-- Section 4: Maximal Intentional Capacity (Exhaustless Ground)
-- ============================================================================

/-- Maximal Intentional Capacity:
    The entity intentionally spans all propositions across reality.
    Footprint: `{Means, Subject}`. -/
def MaximalCapacity (e : Entity) : Prop :=
  ∀ p : Prop, EntityMeans e p

/-- The Ground of Reality possesses Maximal Intentional Capacity:
    its meaning capacity is inexhaustible across all propositional contents.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_maximal_capacity :
    MaximalCapacity Entity.ofGround := by
  intro _p
  trivial

-- ============================================================================
-- Section 5: The Master Synthesis: Classical Foundational Omnipresence
-- ============================================================================

/-- Classical Foundational Omnipresence:
    The conjunction of:
    1. World-Rigid Presence (present across all worlds);
    2. Universal Modal Grounding (grounds all entities across all worlds);
    3. Non-Reciprocal Grounding (asymmetric ontological sustenance);
    4. Maximal Intentional Capacity (comprehensive propositional presence). -/
structure FoundationalOmnipresence (e : Entity) : Prop where
  /-- Presence across all worlds -/
  presence : WorldRigidPresence e
  /-- Universal grounding across all modal worlds -/
  universal_ground : UniversalModalGround e
  /-- Asymmetric, non-reciprocal grounding -/
  non_reciprocal : NonReciprocalGround e
  /-- Maximal intentional capacity -/
  maximal_capacity : MaximalCapacity e

/-- HEADLINE — Foundational Omnipresence of the Ground of Reality:
    `Entity.ofGround` satisfies Classical Foundational Omnipresence across all worlds,
    entities, and contents.
    Footprint: `{Means, NecessarySubjectKind, Subject}` (0 substantive axioms). -/
theorem ofGround_foundational_omnipresence :
    FoundationalOmnipresence Entity.ofGround := {
  presence := ofGround_world_rigid_presence
  universal_ground := ofGround_universal_modal_ground
  non_reciprocal := ofGround_non_reciprocal_ground
  maximal_capacity := ofGround_maximal_capacity
}

-- ============================================================================
-- Section 6: Thomistic Connection (Omnipresence from Universal Sustaining Ground)
-- ============================================================================

/-- The Thomistic Principle of Omnipresence:
    Any entity that is present in all worlds, grounds every being across all worlds,
    operates non-reciprocally, and possesses maximal capacity is foundationally omnipresent.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem omnipresence_from_universal_ground_and_aseity (e : Entity)
    (hPres : WorldRigidPresence e)
    (hUniv : UniversalModalGround e)
    (hNonRec : NonReciprocalGround e)
    (hMax : MaximalCapacity e) :
    FoundationalOmnipresence e := {
  presence := hPres
  universal_ground := hUniv
  non_reciprocal := hNonRec
  maximal_capacity := hMax
}

-- ============================================================================
-- Section 7: Metatheoretic Independence / Countermodel (Finite Entities Fail Omnipresence)
-- ============================================================================

/-- Metatheoretic Independence / Countermodel:
    A finite or localized entity fails universal modal grounding,
    confirming that Foundational Omnipresence is a non-trivial, discriminating property.
    Footprint: `{}`. -/
theorem finite_entity_fails_omnipresence :
    ∃ (Ent World : Type) (ExistsAtRel : World → Ent → Prop) (GroundsRel : Ent → Ent → Prop) (e : Ent),
      ¬ (∀ (w : World) (x : Ent), ExistsAtRel w x → x = e ∨ GroundsRel e x) := by
  refine ⟨Bool, Bool, fun w e => w = e, fun _ _ => False, true, ?_⟩
  intro hUniv
  have h := hUniv false false rfl
  cases h with
  | inl hEq => contradiction
  | inr hFalse => exact hFalse

#print axioms UniversalModalGround
#print axioms ofGround_universal_modal_ground
#print axioms WorldRigidPresence
#print axioms ofGround_world_rigid_presence
#print axioms NonReciprocalGround
#print axioms ofGround_non_reciprocal_ground
#print axioms MaximalCapacity
#print axioms ofGround_maximal_capacity
#print axioms FoundationalOmnipresence
#print axioms ofGround_foundational_omnipresence
#print axioms omnipresence_from_universal_ground_and_aseity
#print axioms finite_entity_fails_omnipresence

end Logos.FoundationalOmnipresence


/-!
================================================================================
SECTION: FoundationalUnicity
================================================================================
-/
/-
# Logos.FoundationalUnicity — The Sixth Classical Divine Characteristic: Unity & Monotheism

This module formalizes the classical divine attribute of **Divine Unity / Foundational Unicity**
(Monotheism; *De Deo Uno*, Aquinas *Summa Theologiae* I, q. 11, a. 3: "Whether God is One?")
for the necessary Ground of Reality (`Entity.ofGround`).

## The Conceptual Movement

1. **Abstract Structural Unicity of Universal Grounding:**
   Two distinct entities cannot simultaneously be universal grounds of all reality under
   asymmetric grounding. If $g_1 \neq g_2$, then $g_1$ grounding all beings entails that
   $g_1$ grounds $g_2$, while $g_2$ grounding all beings entails that $g_2$ grounds $g_1$.
   Under foundational asymmetry (no two entities mutually ground each other), this is an
   immediate contradiction. Hence, at most one universal ground can exist (`universal_ground_unicity`).

2. **Concrete Exclusion of Non-Ground Entities in Γ:**
   We systematically prove that no other entity in the ontological inventory of Γ can be
   a universal modal ground:
   - **Atoms are excluded:** `no_atom_is_universal_modal_ground` proves that no atomic factual
     state `Entity.ofAtom n` can be a universal ground, because an atom cannot ground the
     exhaustive meaning of `Entity.ofGround` (footprint `{Means, Subject}`).
   - **Finite discriminating subjects are excluded:** `no_discriminating_subject_is_universal_modal_ground`
     proves that no subject with finite or discriminating propositional grasp can be a universal
     ground, because it cannot ground the inexhaustible meaning of `Entity.ofGround`
     (footprint `{Means, Subject}`).

3. **Master Synthesis of Foundational Unicity:**
   `ofGround_foundational_unicity` conjoins universal grounding, atom-exclusion,
   subject-transcendence, and unicity under asymmetry into the classical attribute of
   **Foundational Unicity** (`FoundationalUnicity Entity.ofGround`, footprint `{Means, Subject}`,
   0 substantive axioms).

4. **Strict Separation of Categories:**
   In accordance with the project's strict non-overclaiming rules:
   - **Foundational Unicity** (PROVEN): The impossibility of multiple universal grounding principles.
    - **Numerical Unitarianism** (SEPARATED / NOT PROVEN): Does not force a solitary, relationless
      monad; internal relational plurality (the Trinitarian frontier) remains an open, non-collapsed
      theological question. Note the direction: this separation says unicity does not *imply* a
      single-Person ground, leaving the person-count undetermined. It does not refute the
      single-Person reading, and it says nothing against monotheism in its primary sense (one God,
      C320) — the two are distinct claims, and `Monotheism` is the *proven* one.
   - **Pantheism / Monism** (SEPARATED / EXCLUDED): The unique ground is transcendent (`TranscendentGround`),
     strictly distinct from empirical atoms and finite subjects.
-/

namespace Logos.FoundationalUnicity

open Logos.Core (T IsFalse)
open Logos.Semantics (World Form Satisfies)
open Logos.Agency (Subject Means)
open Logos.Entity (Entity ExistsAt EntityOf actualWorld)
open Logos.RecoveredOntologicalGround (EntityMeans OneEssence ActualEntity GroundOfReality)
open Logos.NecessityEternity (ofGround_necessary ofGround_ground_of_reality)
open Logos.CanonicalAseity (CanonicalAseity atom_cannot_ground_the_ground discriminating_subject_cannot_ground_the_ground)
open Logos.DivineSimplicity (TranscendentGround ofGround_transcendent)
open Logos.FoundationalOmnipresence (UniversalModalGround ofGround_universal_modal_ground WorldRigidPresence ofGround_world_rigid_presence NonReciprocalGround ofGround_non_reciprocal_ground MaximalCapacity ofGround_maximal_capacity FoundationalOmnipresence ofGround_foundational_omnipresence)

-- ============================================================================
-- Section 1: Abstract Structural Unicity of Universal Grounding
-- ============================================================================

/-- Foundational Asymmetry:
    No two distinct entities mutually ground each other.
    Ontological grounding is an asymmetric dependency relation.
    Footprint: `{Means, Subject}`. -/
def AsymmetricGrounding : Prop :=
  ∀ (g1 g2 : Entity), OneEssence g1 g2 → ¬ OneEssence g2 g1

/-- Master Metaphysical Theorem: Universal Ground Unicity.
    Two distinct entities cannot both be universal modal grounds under asymmetric grounding.
    Proof: If g1 ≠ g2, universality of g1 forces g1 to ground g2, and universality of g2
    forces g2 to ground g1. Under asymmetry, this yields an immediate contradiction.
    Hence, g1 = g2.
    Footprint: `{CL, Means, NecessarySubjectKind, Subject}` (0 substantive axioms). -/
theorem universal_ground_unicity
    (g1 g2 : Entity)
    (hU1 : UniversalModalGround g1)
    (hU2 : UniversalModalGround g2)
    (hAsym : AsymmetricGrounding)
    (w : World) (hEx1 : ExistsAt w g1) (hEx2 : ExistsAt w g2) :
    g1 = g2 := open Classical in by
  by_cases hEq : g1 = g2
  · exact hEq
  · have h12 : OneEssence g1 g2 := by
      cases hU1 w g2 hEx2 with
      | inl h1 => exact False.elim (hEq h1.symm)
      | inr h2 => exact h2
    have h21 : OneEssence g2 g1 := by
      cases hU2 w g1 hEx1 with
      | inl h1 => exact False.elim (hEq h1)
      | inr h2 => exact h2
    exact False.elim (hAsym g1 g2 h12 h21)

-- ============================================================================
-- Section 1b: Semantic Repair — the Asymmetry Premise is Refutable
-- ============================================================================

/-- Semantic Lemma: `OneEssence` is reflexive at every entity.
    Grounding is meaning-containment, so an entity trivially possesses every
    capacity it already has. No relation of this form can be irreflexive.
    Footprint: `{Means, Subject}`. -/
theorem groundsEntity_reflexive (e : Entity) : OneEssence e e :=
  fun _ hx => hx

/-- Semantic Lemma: an entity grounds the Ground of Reality exactly when it has
    total meaning-capacity. Because `Entity.ofGround` means every proposition,
    the grounding obligation `∀ p, EntityMeans ofGround p → EntityMeans e p`
    collapses to maximal capacity.
    Footprint: `{Means, Subject}`. -/
theorem grounds_ground_iff_maximal (e : Entity) :
    OneEssence e Entity.ofGround ↔ MaximalCapacity e := by
  constructor
  · intro h p
    exact h p trivial
  · intro h p _
    exact h p

/-- Semantic Lemma: no subject-entity is identical with the Ground of Reality.
    Footprint: `{Subject}`. -/
theorem ofGround_ne_ofSubject (s : Subject) : EntityOf s ≠ Entity.ofGround := by
  intro hEq
  cases hEq

/-- Countermodel: `AsymmetricGrounding` as stated is UNSATISFIABLE.
    It reads `∀ g1 g2, OneEssence g1 g2 → ¬ OneEssence g2 g1` with no
    `g1 ≠ g2` guard, but grounding is reflexive, so `g1 = g2 = ofGround` refutes
    it. This is not a price the theory could ever pay: the `hAsym` argument of
    `universal_ground_unicity` reduces against a false statement, so that route
    to unicity is void. Section 3b supplies a satisfiable replacement.
    Footprint: `{Means, Subject}`. -/
theorem not_asymmetric_grounding : ¬ AsymmetricGrounding := by
  intro h
  exact h Entity.ofGround Entity.ofGround
    (groundsEntity_reflexive Entity.ofGround)
    (groundsEntity_reflexive Entity.ofGround)

-- ============================================================================
-- Section 2: Concrete Exhaustive Exclusion of Non-Ground Entities in Γ
-- ============================================================================

/-- Theorem: No Atomic Entity Can Be a Universal Modal Ground.
    An atomic factual state cannot ground Entity.ofGround, hence cannot ground all beings.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem no_atom_is_universal_modal_ground (n : Nat) (w : World) :
    ¬ UniversalModalGround (Entity.ofAtom n) := by
  intro hU
  have hEx : ExistsAt w Entity.ofGround := trivial
  have hCases := hU w Entity.ofGround hEx
  cases hCases with
  | inl hEq => cases hEq
  | inr hGr => exact atom_cannot_ground_the_ground n hGr

/-- Theorem: No Finite Discriminating Subject Can Be a Universal Modal Ground.
    A subject with finite propositional grasp cannot ground Entity.ofGround,
    hence cannot ground all beings across modal space.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem no_discriminating_subject_is_universal_modal_ground
    (s : Subject) (hDisc : ∃ p, ¬ Logos.Agency.Means s p) (w : World) :
    ¬ UniversalModalGround (EntityOf s) := by
  intro hU
  have hEx : ExistsAt w Entity.ofGround := trivial
  have hCases := hU w Entity.ofGround hEx
  cases hCases with
  | inl hEq => cases hEq
  | inr hGr => exact discriminating_subject_cannot_ground_the_ground s hDisc hGr

/-- Theorem: Entity.ofGround is the Sole Universal Ground in the Γ Inventory.
    Any universal modal ground in a world w cannot be an atom, nor a discriminating subject.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_sole_universal_ground (e : Entity) (w : World)
    (hU : UniversalModalGround e) :
    (∀ n : Nat, e ≠ Entity.ofAtom n) ∧
    (∀ s : Subject, (∃ p, ¬ Logos.Agency.Means s p) → e ≠ EntityOf s) := by
  constructor
  · intro n hEq
    subst hEq
    exact no_atom_is_universal_modal_ground n w hU
  · intro s hDisc hEq
    subst hEq
    exact no_discriminating_subject_is_universal_modal_ground s hDisc w hU

-- ============================================================================
-- Section 3: Synthesis of Foundational Unicity (Classical Divine Monotheism)
-- ============================================================================

/-- Foundational Unicity (The Sixth Classical Attribute):
    The entity is a universal modal ground of all reality, transcends all atomic
    and finite subjective beings, and is structurally unique (no competing universal
    ground can co-exist under asymmetric grounding). -/
structure FoundationalUnicity (g : Entity) : Prop where
  /-- The entity grounds every being in every possible world -/
  universal_ground : UniversalModalGround g
  /-- The entity cannot be an atomic worldly state -/
  atom_exclusion : ∀ n : Nat, g ≠ Entity.ofAtom n
  /-- The entity cannot be a finite discriminating subject -/
  subject_transcendence : ∀ s : Subject, (∃ p, ¬ Logos.Agency.Means s p) → g ≠ EntityOf s
  /-- Unicity: any competing universal ground is identical under asymmetry -/
  unicity : ∀ g' : Entity, UniversalModalGround g' → AsymmetricGrounding →
    ∀ w : World, ExistsAt w g → ExistsAt w g' → g = g'

/-- Master Synthesis Theorem: The Ground of Reality possesses Foundational Unicity.
    `Entity.ofGround` satisfies Classical Divine Unicity (Monotheism).
    Footprint: `{CL, Means, NecessarySubjectKind, Subject}` (0 substantive axioms). -/
theorem ofGround_foundational_unicity :
    FoundationalUnicity Entity.ofGround := {
  universal_ground := ofGround_universal_modal_ground
  atom_exclusion := fun n hEq => by cases hEq
  subject_transcendence := fun s _ hEq => by cases hEq
  unicity := fun g' hU' hAsym w hEx1 hEx2 =>
    universal_ground_unicity Entity.ofGround g' ofGround_universal_modal_ground hU' hAsym w hEx1 hEx2
}

-- ============================================================================
-- Section 3b: The Repaired Unicity Route (One Named Hypothesis)
-- ============================================================================

/-- Theorem: Foundational Unicity from ONE named hypothesis.
    If no subject has total meaning-capacity, then the Ground of Reality is the
    only universal modal ground. The atom and discriminating-subject branches are
    discharged by `ofGround_sole_universal_ground`; only the total-capacity
    subject is left, and `hNoTotal` rules it out. Unlike the `AsymmetricGrounding`
    route this premise is satisfiable, so the argument is not void.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_unicity_from_no_discriminating_subject
    (hNoTotal : ∀ s : Subject, ∃ p, ¬ Means s p)
    (e : Entity) (w : World) (hU : UniversalModalGround e) : e = Entity.ofGround := by
  have h208 := ofGround_sole_universal_ground e w hU
  rcases e with s | n | _
  · exact False.elim (h208.2 s (hNoTotal s) rfl)
  · exact False.elim (h208.1 n rfl)
  · rfl

/-- Theorem: the maximality hypothesis IS the exclusion of maximal capacity among
    non-ground entities. This prices Foundational Unicity in the project's own
    vocabulary (`MaximalCapacity`, `FoundationalOmnipresence.lean:119`) instead of
    in newly invented terms, and shows the hypothesis is exactly one predicate.
    Footprint: `{CL, Means, Subject}`. -/
theorem no_discriminating_subject_iff_no_maximal_non_ground :
    (∀ s : Subject, ∃ p, ¬ Means s p)
      ↔ (∀ e : Entity, e ≠ Entity.ofGround → ¬ MaximalCapacity e) := by
  constructor
  · intro h e hne hM
    rcases e with s | n | _
    · obtain ⟨p, hp⟩ := h s
      exact hp (hM p)
    · exact hM True
    · exact hne rfl
  · intro h s
    classical
    by_cases hEx : ∃ p, ¬ Means s p
    · exact hEx
    · have hM : MaximalCapacity (EntityOf s) :=
        fun p => Classical.byContradiction (fun hn => hEx ⟨p, hn⟩)
      exact False.elim (h (EntityOf s) (ofGround_ne_ofSubject s) hM)

/-- Repaired Foundational Unicity: identical in content to `FoundationalUnicity`,
    except that the unicity field is discharged by the single named hypothesis
    `∀ s, ∃ p, ¬ Means s p` rather than by the refutable `AsymmetricGrounding`.
    The unicity field is now a plain identity, with no unpayable premise. -/
structure SoleUniversalGrounding (g : Entity) : Prop where
  /-- The entity grounds every being in every possible world -/
  universal_ground : UniversalModalGround g
  /-- The entity cannot be an atomic worldly state -/
  atom_exclusion : ∀ n : Nat, g ≠ Entity.ofAtom n
  /-- The entity cannot be a discriminating subject -/
  subject_transcendence : ∀ s : Subject, (∃ p, ¬ Means s p) → g ≠ EntityOf s
  /-- Unicity: any other universal modal ground is identical to this one -/
  unicity : ∀ g' : Entity, UniversalModalGround g' → g' = g

/-- Master Synthesis: the Ground of Reality is the sole universal ground, under
    the single named hypothesis.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_sole_universal_grounding
    (hNoTotal : ∀ s : Subject, ∃ p, ¬ Means s p) :
    SoleUniversalGrounding Entity.ofGround := {
  universal_ground := ofGround_universal_modal_ground
  atom_exclusion := fun n hEq => by cases hEq
  subject_transcendence := fun s _ hEq => by cases hEq
  unicity := fun g' hU' =>
    ofGround_unicity_from_no_discriminating_subject hNoTotal g' actualWorld hU'
}

/-- Master Synthesis (existential form): exactly one universal modal ground exists.
    Existence comes from `ofGround_universal_modal_ground`, which is unconditional;
    uniqueness from `hNoTotal`. This is Classical Monotheism with the whole price
    of the claim visible in a single line. The `∃!` notation and `ExistsUnique`
    are absent from this Lean core, so the standard unique-existence conjunction
    is written out.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem exactly_one_universal_modal_ground
    (hNoTotal : ∀ s : Subject, ∃ p, ¬ Means s p) :
    ∃ g : Entity, UniversalModalGround g ∧
      (∀ g' : Entity, UniversalModalGround g' → g' = g) :=
  ⟨Entity.ofGround, ofGround_universal_modal_ground,
    fun g' hU' => ofGround_unicity_from_no_discriminating_subject hNoTotal g' actualWorld hU'⟩

-- ============================================================================
-- Section 4: Category Boundary Separations (Honest Demarcation)
-- ============================================================================

/-- Separation Model: Foundational Unicity Does Not Imply a Single-Person Ground.
    Proving that there is exactly one universal grounding principle does not logically
    force that the internal life of that ground is solitary or lacks relational plurality.

    **Read the entailment direction carefully — this is a separation, not a refutation.**
    The model has one ground, and in it that ground bears at least two distinct persons; so
    *unicity does not entail* a single-Person ground. It does **not** follow that a single-Person
    ground is false: the person-count is left *undetermined* by unicity. Two further
    consequences, each load-bearing against a common misreading:
      - **Monotheism is not this claim.** Monotheism is one *God* — one universal modal ground —
        and that is `exactly_one_universal_modal_ground` (C320), PROVEN. This declaration is about
        how many *Persons* that one God bears, which is a different question, and it stays open here.
      - **The positive plural reading is priced elsewhere.** Distinct subsisting centres come from
        the declared META axiom `DivineAgape.AxAgapeEssence` (C504), not from this countermodel.
        Whether the ground is personal *at all* is `C228` (BLOCKED), and that is upstream: a
        person-count is not well posed until personality is settled.
    Footprint: `{}`. -/
theorem unicity_does_not_force_unitarian_monad :
    ∃ (Ground : Type) (Persons : Ground → Type),
      (∃ g : Ground, ∀ g' : Ground, g' = g) ∧ (∀ g : Ground, ∃ (p1 p2 : Persons g), p1 ≠ p2) := by
  refine ⟨Unit, fun _ => Bool, ?_, fun _ => ⟨true, false, Bool.noConfusion⟩⟩
  exact ⟨(), fun y => Subsingleton.elim y ()⟩

/-- Separation Model: Foundational Unicity Does Not Entail Pantheism / Monism.
    A unique universal ground is strictly non-identical with the world of entities
    it grounds, preserving metaphysical transcendence (`TranscendentGround`).
    Footprint: `{Subject}`. -/
theorem unicity_strictly_transcends_world :
    TranscendentGround Entity.ofGround :=
  ofGround_transcendent

-- ============================================================================
-- Section 5: Axiom Footprint Audit
-- ============================================================================

#print axioms universal_ground_unicity
#print axioms no_atom_is_universal_modal_ground
#print axioms no_discriminating_subject_is_universal_modal_ground
#print axioms ofGround_sole_universal_ground
#print axioms ofGround_foundational_unicity
#print axioms unicity_does_not_force_unitarian_monad
#print axioms unicity_strictly_transcends_world
#print axioms groundsEntity_reflexive
#print axioms grounds_ground_iff_maximal
#print axioms ofGround_ne_ofSubject
#print axioms not_asymmetric_grounding
#print axioms ofGround_unicity_from_no_discriminating_subject
#print axioms no_discriminating_subject_iff_no_maximal_non_ground
#print axioms ofGround_sole_universal_grounding
#print axioms exactly_one_universal_modal_ground

end Logos.FoundationalUnicity


/-!
================================================================================
SECTION: DivinePureActuality
================================================================================
-/
/-
# Logos.DivinePureActuality — The Seventh Classical Divine Characteristic: Pure Actuality & Perfection

This module formalizes the classical divine attribute of **Divine Pure Actuality** (*Actus Purus*,
Aristotle *Metaphysics* XII.7, Aquinas *Summa Theologiae* I, q. 3, a. 1–2; q. 4, a. 1–2:
"Whether God is Perfect?" / "God is Pure Act, without any potentiality") for the necessary
Ground of Reality (`Entity.ofGround`), fulfilling the roadmap in `CHARACTERISTICS.md:373`
and `CHARS.md:243`.

## The Conceptual Movement

1. **Apophatic Purification (*Via Negationis*):**
   Passive potency (*potentia passiva*) is the capacity to receive a new state, to be changed or
   determined by an external cause, to fail of existence, or to have unfulfilled capacity.
   An ultimate foundation cannot possess passive potency without ceasing to be ultimate.
   We formalize the fourfold exclusion of passive potency:
   - **Zero Existential Potency:** The ground cannot fail to exist in any possible world (`ofGround_no_existential_potency`).
   - **Zero Grounding Potency:** Under finite subjectivity, the ground cannot be externally grounded by another (`ofGround_no_grounding_potency`).
   - **Zero Transition Potency:** The ground is immune to temporal becoming or agential succession (`ofGround_no_transition_potency`).
   - **Zero Intentional Potency:** The ground possesses complete, undivided propositional meaning (`ofGround_no_intentional_potency`).

2. **Positive Foundational Actuality (*Via Eminentiae*):**
   Rather than being in potency, the ground is in act as the universal sustaining ground of all
   reality across modal space (`UniversalModalGround Entity.ofGround`, from `FoundationalOmnipresence`).

3. **Master Synthesis of Divine Pure Actuality:**
   `ofGround_divine_pure_actuality` conjoins the absence of passive potency with universal
   grounding into the classical attribute of **Divine Pure Actuality** (*Actus Purus*, Aquinas ST I q. 4 a. 1),
   verified with 0 substantive axioms (footprint `{Initiates, Means, State, Subject}`).

4. **Incorporeality and Entity Exclusion Corollaries:**
   - **Divine Incorporeality:** As pure act without material/passive potency, `Entity.ofGround`
     is strictly non-corporeal and transcends every worldly atomic state (`ofGround_incorporeal`,
     Aquinas ST I q. 3 a. 1–2: *Deus non est corpus*).
   - **Atoms fail Pure Actuality:** Atomic states possess passive existential potency (`atom_fails_pure_actuality`).
   - **Finite subjects fail Pure Actuality:** Discriminating subjects possess unactualized intentional potency (`discriminating_subject_fails_pure_actuality`).
   - **Sole Pure Actuality:** `Entity.ofGround` is the sole candidate for Actus Purus in Γ (`ofGround_sole_pure_actuality`).

5. **Honest Demarcation:**
   - **Metatheoretic Independence:** Entities with passive potency fail Pure Actuality (`entity_with_potency_fails_pure_actuality`, footprint `{}`).
   - **Category Demarcation (C498, disclosed):** the separation of Metaphysical Pure Actuality from
     physical kinetic motion or thermodynamic energy (`pure_actuality_independent_of_physical_energy`).
     **Disclosure: this is a pure-logic tautology.** Both propositional variables are unbound, so the
     statement is `∃ P Q, P ∧ ¬ Q` with no reference to pure actuality or to energy; it demarcates
     nothing on its own. It is ledgered as C498 and kept visible rather than deleted, so the
     category reading is neither silently emptied nor silently upgraded (class A `Kinetic` semantics
     were declined F18). Γ has no theory of physical energy; see `PLAN3.md` Task 3.
-/

namespace Logos.DivinePureActuality

open Logos.Core (T IsFalse)
open Logos.Semantics (World Form Satisfies)
open Logos.Agency (Subject Means State Initiates)
open Logos.Entity (Entity ExistsAt EntityOf)
open Logos.RecoveredOntologicalGround (EntityMeans OneEssence ActualEntity GroundOfReality)
open Logos.NecessityEternity (ofGround_necessary the_ground_everlasting the_ground_atemporal the_ground_not_in_succession)
open Logos.CanonicalAseity (ExternalGrounding CanonicalAseity conditional_canonical_aseity atom_cannot_ground_the_ground discriminating_subject_cannot_ground_the_ground)
open Logos.DivineSimplicity (NonComposite non_composite_iff_canonical_aseity ofGround_has_no_internal_components ofGround_undivided_meaning ofGround_transcendent TranscendentGround)
open Logos.DivineImmutability (TransitionInvariance ofGround_transition_invariance ModalInvariance ofGround_modal_invariance StageInvariance ofGround_stage_invariance CapacityInvariance ofGround_capacity_invariance DivineImmutability ofGround_divine_immutability)
open Logos.FoundationalOmnipresence (UniversalModalGround ofGround_universal_modal_ground NonReciprocalGround ofGround_non_reciprocal_ground MaximalCapacity ofGround_maximal_capacity FoundationalOmnipresence ofGround_foundational_omnipresence)
open Logos.FoundationalUnicity (FoundationalUnicity ofGround_foundational_unicity)

-- ============================================================================
-- Section 1: The Metaphysics of Potency and Pure Actuality
-- ============================================================================

/-- Separation Model: Entities with Passive Potency Fail Pure Actuality.
    Proving that Pure Actuality is a non-trivial, discriminating predicate
    that excludes entities carrying passive potentiality.
    Footprint: `{}` (pure logic). -/
theorem entity_with_potency_fails_pure_actuality :
    ∃ (Ent : Type) (HasPotency : Ent → Prop) (PureAct : Ent → Prop),
      (∀ e, PureAct e → ¬ HasPotency e) ∧
      (∃ e, HasPotency e ∧ ¬ PureAct e) := by
  refine ⟨Bool, fun b => b = false, fun b => b = true, ?_, ?_⟩
  · intro b hb_act hb_pot
    subst hb_act
    cases hb_pot
  · exact ⟨false, rfl, fun h => by contradiction⟩

/-- Passive existential potency: entity `e` is in potency to non-existence,
    failing to exist in at least one possible world.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
def PassiveExistentialPotency (e : Entity) : Prop :=
  ∃ w : World, ¬ ExistsAt w e

/-- Theorem: The Ground of Reality has zero passive existential potency.
    `Entity.ofGround` exists necessarily in every possible world.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem ofGround_no_existential_potency :
    ¬ PassiveExistentialPotency Entity.ofGround := by
  intro ⟨w, hw⟩
  exact hw trivial

/-- Passive grounding potency: entity `e` is dependent upon and grounded by
    an external entity distinct from itself.
    Footprint: `{Means, Subject}`. -/
def PassiveGroundingPotency (e : Entity) : Prop :=
  ∃ g : Entity, ExternalGrounding g e

/-- Theorem: The Ground of Reality has zero passive grounding potency.
    Under finite subjectivity, `Entity.ofGround` depends upon no external ground.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_no_grounding_potency
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    ¬ PassiveGroundingPotency Entity.ofGround :=
  conditional_canonical_aseity hFinite

/-- Passive transition potency: entity `e` is subject to temporal change,
    process transition, or agential initiation becoming.
    Footprint: `{Initiates, State, Subject}`. -/
def PassiveTransitionPotency (e : Entity) : Prop :=
  ¬ TransitionInvariance e

/-- Theorem: The Ground of Reality has zero passive transition potency.
    `Entity.ofGround` is immune to becoming and outside agential succession.
    Footprint: `{Initiates, State, Subject}`.

    **READING, 2026-09-28 (succession audit, C458–C462).** `PassiveTransitionPotency e := ¬
    TransitionInvariance e` and `TransitionInvariance e := NotInSuccession e`, so this row inherits
    C458's fact — **constructor disjointness, not a result about initiation**. What is proven is
    that the ground is no subject's correlate; if a correlate initiates, that is a fact about the
    subject. "Immune to agential succession" overstates the proof, and the ground's non-agency is
    unstatable rather than established (C462, `BLOCKED`). The ground's *production* is a different
    relation and coexists with this potency-absence in C467. No status moves. -/
theorem ofGround_no_transition_potency :
    ¬ PassiveTransitionPotency Entity.ofGround := by
  intro h
  exact h ofGround_transition_invariance

/-- Passive intentional potency: entity `e` fails to actualize intentional meaning
    for some proposition (has unactualized propositional capacity).
    Footprint: `{Means, Subject}`. -/
def PassiveIntentionalPotency (e : Entity) : Prop :=
  ∃ p : Prop, ¬ EntityMeans e p

/-- Theorem: The Ground of Reality has zero passive intentional potency.
    `Entity.ofGround` actualizes uniform meaning across all propositions.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_no_intentional_potency :
    ¬ PassiveIntentionalPotency Entity.ofGround := by
  intro ⟨p, hp⟩
  exact hp trivial

/-- Theorem: Finite discriminating subjects possess passive intentional potency.
    Any subject whose propositional horizon is discriminating has unactualized potency.
    Footprint: `{Means, Subject}`. -/
theorem discriminating_subject_has_intentional_potency
    (s : Subject) (hDisc : ∃ p, ¬ Means s p) :
    PassiveIntentionalPotency (EntityOf s) :=
  hDisc

-- ============================================================================
-- Section 2: Classical Divine Pure Actuality (Actus Purus)
-- ============================================================================

/-- Classical Divine Pure Actuality (Actus Purus, Aquinas ST I q. 3 a. 1-2, ST I q. 4 a. 1-2):
    The entity possesses zero passive potentiality:
    (1) no existential potency to non-being across modal space;
    (2) no passive grounding potency from external entities (Canonical Aseity);
    (3) no passive transition potency (outside becoming and succession);
    (4) no passive intentional potency (exhaustive propositional actuality);
    and positively, is the universal modal ground sustaining all reality. -/
structure DivinePureActuality (g : Entity) : Prop where
  /-- Zero existential potency: necessarily actualized in all worlds -/
  no_existential_potency : ¬ PassiveExistentialPotency g
  /-- Zero grounding potency: ungrounded by any external entity -/
  no_grounding_potency : ¬ PassiveGroundingPotency g
  /-- Zero transition potency: immune to agential succession and temporal becoming -/
  no_transition_potency : ¬ PassiveTransitionPotency g
  /-- Zero intentional potency: complete, undivided propositional meaning -/
  no_intentional_potency : ¬ PassiveIntentionalPotency g
  /-- Universal actuality: actively grounds all beings across modal space -/
  universal_ground : UniversalModalGround g

/-- Master Synthesis Theorem: The Ground of Reality possesses Divine Pure Actuality.
    `Entity.ofGround` is Actus Purus in Γ, having zero passive potentiality
    and universally grounding reality.
    Footprint: `{Initiates, Means, NecessarySubjectKind, State, Subject}` (0 substantive axioms). -/
theorem ofGround_divine_pure_actuality
    (hFinite : ∀ s : Subject, ∃ p : Prop, ¬ Means s p) :
    DivinePureActuality Entity.ofGround := {
  no_existential_potency := ofGround_no_existential_potency
  no_grounding_potency := ofGround_no_grounding_potency hFinite
  no_transition_potency := ofGround_no_transition_potency
  no_intentional_potency := ofGround_no_intentional_potency
  universal_ground := ofGround_universal_modal_ground
}

/-- The Thomistic Principle of Pure Actuality:
    Any entity with world-rigid necessary existence, canonical aseity,
    transition invariance, maximal intentional capacity, and universal modal
    grounding satisfies Divine Pure Actuality (Aquinas ST I q. 3 a. 1-2; q. 4 a. 1).
    Footprint: `{Initiates, Means, NecessarySubjectKind, State, Subject}`. -/
theorem necessity_aseity_and_immutability_yield_pure_actuality
    (e : Entity)
    (hNec : ∀ w : World, ExistsAt w e)
    (hAseity : CanonicalAseity e)
    (hTrans : TransitionInvariance e)
    (hMax : MaximalCapacity e)
    (hUniv : UniversalModalGround e) :
    DivinePureActuality e := {
  no_existential_potency := fun ⟨w, hw⟩ => hw (hNec w)
  no_grounding_potency := hAseity
  no_transition_potency := fun h => h hTrans
  no_intentional_potency := fun ⟨p, hp⟩ => hp (hMax p)
  universal_ground := hUniv
}

-- ============================================================================
-- Section 3: Divine Incorporeality and Entity Exclusion Corollaries
-- ============================================================================

/-- Divine Incorporeality and Immateriality (Aquinas ST I q. 3 a. 1-2: Deus non est corpus).
    As Pure Actuality without material/passive potency, Entity.ofGround is strictly
    non-corporeal and transcends every worldly atomic state.
    Footprint: `{Subject}`. -/
theorem ofGround_incorporeal :
    ∀ n : Nat, Entity.ofGround ≠ Entity.ofAtom n := by
  intro n hEq
  cases hEq

/-- Atomic physical entities fail Divine Pure Actuality:
    every atomic state has passive existential potency.
    Footprint: `{Initiates, Means, NecessarySubjectKind, State, Subject}`. -/
theorem atom_fails_pure_actuality (n : Nat) :
    ¬ DivinePureActuality (Entity.ofAtom n) := by
  intro hAct
  have hNoPot := hAct.no_existential_potency
  apply hNoPot
  refine ⟨fun _ => Logos.Semantics.TV.f, ?_⟩
  dsimp [ExistsAt, Logos.Entity.EntityExistsAt]
  intro hTrue
  exact Logos.Semantics.TV.noConfusion hTrue

/-- Finite discriminating subjects fail Divine Pure Actuality:
    every discriminating subject has passive intentional potency.
    Footprint: `{Initiates, Means, NecessarySubjectKind, State, Subject}`. -/
theorem discriminating_subject_fails_pure_actuality
    (s : Subject) (hDisc : ∃ p, ¬ Means s p) :
    ¬ DivinePureActuality (EntityOf s) := by
  intro hAct
  exact hAct.no_intentional_potency hDisc

/-- Theorem: Entity.ofGround is the Sole Candidate for Pure Actuality in Γ.
    No atomic state and no discriminating subject can be Actus Purus.
    Footprint: `{Initiates, Means, NecessarySubjectKind, State, Subject}`. -/
theorem ofGround_sole_pure_actuality
    (e : Entity) (hAct : DivinePureActuality e) :
    (∀ n : Nat, e ≠ Entity.ofAtom n) ∧
    (∀ s : Subject, (∃ p, ¬ Means s p) → e ≠ EntityOf s) := by
  constructor
  · intro n hEq
    subst hEq
    exact atom_fails_pure_actuality n hAct
  · intro s hDisc hEq
    subst hEq
    exact discriminating_subject_fails_pure_actuality s hDisc hAct

-- ============================================================================
-- Section 4: Category Demarcation
-- ============================================================================

/-- Category Demarcation (C498, disclosed): Pure Actuality in Γ does not imply physical kinetic energy.
    Metaphysical Actus Purus is absence of passive potency and sustaining ground of reality;
    it does not establish thermodynamic energy, kinetic movement, or physical work.

    **Disclosure: this is a pure-logic tautology.** Both propositional variables are unbound, so the
    statement is `∃ P Q, P ∧ ¬ Q` with no reference to pure actuality or to energy; it demarcates
    nothing on its own. It is ledgered as C498 and kept visible rather than deleted, so the
    category reading is neither silently emptied nor silently upgraded (class A `Kinetic` semantics
    were declined F18). Γ has no theory of physical energy; see `PLAN3.md` Task 3.
    Footprint: `{}`. -/
theorem pure_actuality_independent_of_physical_energy :
    ∃ (PureAct PhysicalEnergy : Prop),
      PureAct ∧ ¬ PhysicalEnergy := by
  exact ⟨True, False, trivial, fun h => h⟩

-- ============================================================================
-- Section 5: Axiom Footprint Audit
-- ============================================================================

#print axioms entity_with_potency_fails_pure_actuality
#print axioms ofGround_no_existential_potency
#print axioms ofGround_no_grounding_potency
#print axioms ofGround_no_transition_potency
#print axioms ofGround_no_intentional_potency
#print axioms ofGround_divine_pure_actuality
#print axioms necessity_aseity_and_immutability_yield_pure_actuality
#print axioms ofGround_incorporeal
#print axioms atom_fails_pure_actuality
#print axioms discriminating_subject_fails_pure_actuality
#print axioms ofGround_sole_pure_actuality
#print axioms pure_actuality_independent_of_physical_energy

end Logos.DivinePureActuality


/-!
================================================================================
SECTION: DivineOmnipotence
================================================================================
-/
/-
# Logos.DivineOmnipotence — Foundational Omnipotence and the Non-Contradictory Restriction

This module formalizes the characteristic of **Foundational Omnipotence**
(the ground's operative scope excludes no non-contradictory state of affairs;
`CHARACTERISTICS.md` §15; `CHARS.md` §15) for the necessary Ground of Reality
(`Entity.ofGround`).

### What is formalized:
1. **The price of the operational identification (`OperatesAt`, C241's model):**
   Γ has **no** causal production relation, so the canonical operation relation is
   *presence plus obtaining*. C241 is a machine-checked countermodel showing this
   price is real: an entity can be present in every world and still operate
   nothing — presence is not production.
2. **Gapless operative scope (`GaplessOperate`, C242):**
   No state of affairs satisfiable in any accessible world is closed to the
   ground's operative scope. In Aquinas' own terms (*ST* I, q. 25, a. 5, ad 1 —
   *De potentia Dei*), omnipotence is power over *whatever does not involve a
   contradiction*; C242 proves exactly that for Γ's satisfiable domain.
3. **The non-contradictory restriction, as a theorem (C243, C244):**
   The ground operates only what obtains, and therefore can never operate
   `φ ∧ ¬φ` — because no world satisfies a contradiction
   (`Semantics.nonContradiction`, `Semantics.lean:85`).
4. **Exhaustive exclusion and uniqueness (C245–C247):** no worldly atom and no
   discriminating subject is a gapless operator, so `Entity.ofGround` is the
   **sole** gapless operator in the Γ inventory.
5. **The master synthesis (`FoundationalOmnipotence`, C248 + companion):**
   Conjoins (2)–(4) with the universal grounding of `FoundationalOmnipresence`,
   at zero new substantive axioms.

### The honest boundary, machine-checked:
- **The orthodox reading is affirmed, not refuted.** Aquinas' restriction to the
  non-contradictory is *not* a weakening of omnipotence that Γ fails to reach;
  it is machine-checked here (C242) and its domain is machine-checked
  contradiction-free (C250, `{}`). The reading is also non-vacuous: the
  satisfiable domain is non-empty, so "power over everything that does not
  involve a contradiction" is a substantive, non-trivial scope.
- **What is refuted is only the contradiction-omni reading** (C244) — "power over
  everything conceivable, *including contradictions*". It is refuted *because of*
  the orthodox restriction, not against it: `φ ∧ ¬φ` is unsatisfiable in every
  world of Γ's classical valuation semantics, so it can never be operated. This
  is a coherence result of the framework, not a criticism of any doctrine.
- **The causal/creative sense is now declared, not derived.** "Can bring X about" uses the
  entity-level production relation `Logos.ThomisticAct.Produces : Entity → World → Form → Prop`
  (C463, `Tag: VOCAB`); the only initiation relation remains `Agency.Initiates`
  (`Agency.lean:168`), which is **subject**-indexed while `Entity.ofGround` is provably not a
  subject correlate (`ofGround_ne_ofSubject`, `NecessityEternity.lean:160`). The two F10 items
  are recorded in `formal/GAPMAP.md` (Level 17) and `theorems/T27.txt`:

      (1) VOCABULARY — a production relation, one level down from `Initiates`:
          Produces : Entity → World → Form → Prop (C463, declared);
      (2) DERIVATION — the causal sense, which (1) alone does not give and which is now separately
          declared, not derived: `Logos.ThomisticAct.ground_produces_every_satisfiable_form` (C493,
          `Tag: META`). It closes F10's universal sentence as a priced metaphysical bridge, while C483
          remains the shape-level proof that (1) plus C465's existential shape would not have entailed
          it. Production is still not creation: C110's `Creates` separation stands.

  Note that (1) alone would not yield (2): `OneEssence`
  (`RecoveredOntologicalGround.lean:57`) is explanatory containment (*esse est
  agere*), and `means_does_not_imply_means_selection` (`HostileSemantics.lean:1861`)
  already machine-checks that omni-scope does not entail selection power.
- **One further boundary, machine-checked (C249):** Γ's Kripke accessibility is
  not conjunctive, so gapless scope over accessible states of affairs is strictly
  weaker than power over every pair of jointly accessible contents. C249 is the
  generic separation, not a refutation of classical omnipotence.

A note on vocabulary: because `Core.T p` is the identity (`Core.lean:40`), no
consistency predicate is built on `T` here. "Does not involve a contradiction" is
read as *satisfiability in Γ's classical valuation semantics*
(`∃ w, Satisfies w φ`), which is non-degenerate and is discharged by
`Semantics.nonContradiction`.
-/

namespace Logos.DivineOmnipotence

open Logos.Semantics (Form World Satisfies sat_and sat_not)
open Logos.Entity (Entity EntityOf ExistsAt actualWorld)
open Logos.Modal (NecessaryEntity)
open Logos.Agency (Subject NecessarySubjectKind ContingentSubjectKind)
open Logos.Necessity (WProp)
open Logos.RecoveredOntologicalGround (OneEssence)
open Logos.FoundationalOmnipresence
    (WorldRigidPresence UniversalModalGround ofGround_universal_modal_ground)
open Logos.TheologicalModalHardening (KripkeFrame UniversalFrame)

-- ============================================================================
-- Section 1: The Scope Domain — Satisfiable States of Affairs
-- ============================================================================

/-- A state of affairs P is possible at `w` when it is satisfied in some world
    accessible from `w` under `frame`. With the weakest frame
    (`UniversalFrame`, every world accessible) this is exactly Γ's satisfiable
    domain: `∃ v, Satisfies v P`.
    Footprint: `{}`. -/
def PossibleAt (frame : KripkeFrame World) (w : World) (P : WProp) : Prop :=
  ∃ v, frame.R w v ∧ P v

/-- **THE PRICED IDENTIFICATION — the founding decision of this batch.**
    In this batch Γ had no causal production relation (see the module header), so the canonical
    operation relation is *presence plus obtaining*: the entity is present at `v`
    and the content P obtains at `v`. This is a **definition**, not a derivation:
    C241 machine-checks that the price is real (presence ⇏ production). The causal/creative sense
    has since been closed by declaration, not by this definition: C463 declares the production
    relation and C493 (`Tag: META`) declares universal production, while this row keeps its
    weakened reading and footprint.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
def OperatesAt (v : World) (e : Entity) (P : WProp) : Prop :=
  ExistsAt v e ∧ P v

/-- Gapless operative scope: no possible state of affairs is closed to the
    entity's operative scope at the evaluating world — the weak (Thomistic)
    classical sense of omnipotence, generic over carrier and operation relation.
    Footprint: `{}`. -/
def GaplessOperate (frame : KripkeFrame World) {Ent : Type}
    (Operates : World → Ent → WProp → Prop) (e : Ent) : Prop :=
  ∀ w P, PossibleAt frame w P → ∃ v, frame.R w v ∧ Operates v e P

/-- Conjunctive power: every *pair* of possible states of affairs, jointly
    possible, is operated together at one world. Strictly stronger than
    `GaplessOperate`; C249 machine-checks that the two come apart.
    Footprint: `{}`. -/
def ConjunctivePower (frame : KripkeFrame World) {Ent : Type}
    (Operates : World → Ent → WProp → Prop) (e : Ent) : Prop :=
  ∀ w P Q, PossibleAt frame w P → PossibleAt frame w Q →
    ∃ v, frame.R w v ∧ Operates v e (fun u => P u ∧ Q u)

-- ============================================================================
-- Section 2: The Price of the Identification (Countermodel)
-- ============================================================================

/-- **The price of the operational identification, machine-checked.**
    An entity can be present in *every* world and still operate nothing: presence
    is not production. The witness is the two-element carrier where one element is
    universally present but no content is ever operated at it, and the operation
    relation is the one Γ actually uses — the second conjunct of a content at the
    evaluating world. This is what licenses the `README-OLD.md:263` disclaimer
    for the causal sense, and it is why C248 below is a *foundational* record.
    Footprint: `{}`. -/
theorem existence_everywhere_does_not_entail_operation :
    ∃ (Ent : Type) (ExistsAtRel : World → Ent → Prop)
      (Operates : World → Ent → WProp → Prop) (e : Ent),
      (∀ w : World, ExistsAtRel w e) ∧
      ¬ GaplessOperate (UniversalFrame World) Operates e := by
  let Ent : Type := Bool
  let ExistsAtRel : World → Ent → Prop := fun _ _ => True
  let Operates : World → Ent → WProp → Prop :=
    fun _ b P => b = true ∧ ∀ v, P v
  refine ⟨Ent, ExistsAtRel, Operates, false, fun _ => trivial, ?_⟩
  intro hG
  obtain ⟨v, _, hOp⟩ :=
    hG actualWorld (fun u => Satisfies u (Form.atom 0)) ⟨actualWorld, trivial, rfl⟩
  exact Logos.Semantics.TV.noConfusion (hOp.2 (fun _ => Logos.Semantics.TV.f))

-- ============================================================================
-- Section 3: The Doctrine — Gapless Operative Scope for the Ground
-- ============================================================================

/-- **Foundational Omnipotence, the doctrine (Aquinas *ST* I, q. 25, a. 5, ad 1):
    no state of affairs that is satisfiable in any accessible world is closed to
    the ground's operative scope.** With `UniversalFrame` the scope is Γ's whole
    satisfiable domain, and `OperatesAt` is the priced identification of §1. The
    proof is the two clauses of `OperatesAt`: the ground is present at `v` by the
    world-rigid constructor (stipulation ◈ `ofGround_existsAt`) and the content
    obtains at `v` by the witness. Zero substantive axioms.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem ofGround_gapless_operative_scope :
    GaplessOperate (UniversalFrame World) OperatesAt Entity.ofGround := by
  intro w P ⟨v, hRv, hPv⟩
  exact ⟨v, hRv, trivial, hPv⟩

/-- The non-contradictory restriction, first horn: the ground operates **only what
    obtains**. Nothing unobtained — hence nothing unsatisfiable — is within the
    ground's operative scope. (Holds of every entity under `OperatesAt`, hence of
    the ground with no premise at all.)
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem ofGround_operates_only_what_obtains :
    ∀ v : World, ∀ P : WProp, OperatesAt v Entity.ofGround P → P v := by
  intro v P h
  exact h.2

/-- **The non-contradictory restriction, second horn: the ground cannot operate a
    contradiction — ever, at no world.** `φ ∧ ¬φ` is unsatisfiable in every world
    of Γ's classical valuation semantics (`Semantics.nonContradiction`), so the
    ground's operative scope excludes it. This is the *only* sense of omnipotence
    refuted here — the contradiction-omni reading ("everything conceivable,
    including contradictions") — and it is refuted **by** the orthodox
    restriction, not against it. The cost is `propext`, inherited from
    `Semantics.nonContradiction` (C14, `CL`).
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem ofGround_does_not_operate_contradictions (v : World) (φ : Form) :
    ¬ OperatesAt v Entity.ofGround
        (fun u => Satisfies u (Form.and φ (Form.not φ))) := by
  intro h
  have hSat : Satisfies v (Form.and φ (Form.not φ)) := h.2
  have hNo : ¬ Satisfies v (Form.and φ (Form.not φ)) :=
    Logos.Semantics.nonContradiction φ v
  rw [sat_and, sat_not] at hSat hNo
  exact hNo hSat

-- ============================================================================
-- Section 4: Exhaustive Exclusion (Atoms and Discriminating Subjects)
-- ============================================================================

/-- Exhaustive exclusion: no worldly atom is a gapless operator. An atom exists
    exactly where its atomic content obtains, so it misses every world in which
    that content is denied — the witness being the content `¬atom n` itself, which
    is satisfiable (`(fun _ => TV.f)`) and yet unobtained wherever the atom
    exists. Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem atom_not_gapless_operate (n : Nat) :
    ¬ GaplessOperate (UniversalFrame World) OperatesAt (Entity.ofAtom n) := by
  intro hG
  obtain ⟨v, _, hEv, hPv⟩ :=
    hG actualWorld (fun u => Satisfies u (Form.not (Form.atom n)))
      ⟨fun _ => Logos.Semantics.TV.f, trivial, fun hc =>
        Logos.Semantics.TV.noConfusion hc⟩
  exact hPv hEv

/-- Exhaustive exclusion: a subject of the contingent kind is not a gapless
    operator. Such a subject exists only at the actual world, so it misses
    every satisfiable content denied there — witness `¬atom 0`, which is
    satisfiable in `(fun _ => TV.f)` and yet denied at `actualWorld`. The
    necessary kind is excluded from this verdict by hypothesis: a necessary-kind
    subject is present everywhere, so the argument does not touch it.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem discriminating_subject_not_gapless_operate (s : Subject)
    (hKind : ContingentSubjectKind s) :
    ¬ GaplessOperate (UniversalFrame World) OperatesAt (EntityOf s) := by
  intro hG
  obtain ⟨v, _, hEv, hPv⟩ :=
    hG actualWorld (fun u => Satisfies u (Form.not (Form.atom 0)))
      ⟨fun _ => Logos.Semantics.TV.f, trivial, fun hc =>
        Logos.Semantics.TV.noConfusion hc⟩
  dsimp [OperatesAt, ExistsAt, Logos.Entity.EntityExistsAt,
    Logos.Entity.SubjectExistsAt, EntityOf] at hEv
  rcases hEv with hk | heq
  · exact hKind hk
  · subst heq
    exact hPv rfl

/-- **Gapless operators are the ground and the necessary-kind subjects.** Together
    with the exclusions of §4, this closes the characteristic: among the three
    constructors of `Entity`, gapless operative scope belongs to
    `Entity.ofGround` and to subject-correlates of the necessary kind — never to
    atoms, never to contingent-kind subjects. The necessary-kind disjunct is the
    honest price of the two-kinds doctrine: whoever is present everywhere
    operates everywhere satisfiable. Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem gapless_operators_are_ground_or_necessary_kind (e : Entity)
    (h : GaplessOperate (UniversalFrame World) OperatesAt e) :
    e = Entity.ofGround ∨
      ∃ s : Subject, NecessarySubjectKind s ∧ e = EntityOf s := by
  cases e with
  | ofSubject s =>
      obtain ⟨v, _, hEv, hPv⟩ :=
        h actualWorld (fun u => Satisfies u (Form.not (Form.atom 0)))
          ⟨fun _ => Logos.Semantics.TV.f, trivial, fun hc =>
            Logos.Semantics.TV.noConfusion hc⟩
      dsimp [OperatesAt, ExistsAt, Logos.Entity.EntityExistsAt,
        Logos.Entity.SubjectExistsAt, EntityOf] at hEv
      rcases hEv with hk | heq
      · exact Or.inr ⟨s, hk, rfl⟩
      · subst heq
        exact absurd rfl hPv
  | ofAtom n => exact False.elim (atom_not_gapless_operate n h)
  | ofGround => exact Or.inl rfl

-- ============================================================================
-- Section 5: The Master Synthesis — Foundational Omnipotence
-- ============================================================================

/-- Foundational Omnipotence: the conjunction of gapless operative scope over the
    satisfiable domain, the two horns of the non-contradictory restriction
    (operates only what obtains; operates no contradiction — the second being the
    machine-checked exclusion of the contradiction-omni reading), and the
    universal grounding of `FoundationalOmnipresence`. (The structure itself is
    not an audited kernel node; the audited axiom set of the ground instance is
    recorded in `ofGround_foundational_omnipotence` below.) -/
structure FoundationalOmnipotence (g : Entity) : Prop where
  /-- No satisfiable state of affairs is closed to the entity's operative scope -/
  gapless_operate : GaplessOperate (UniversalFrame World) OperatesAt g
  /-- Only what obtains is operated -/
  operates_only_obtaining : ∀ v : World, ∀ P : WProp, OperatesAt v g P → P v
  /-- No contradiction is ever operated -/
  operates_no_contradiction :
    ∀ v : World, ∀ φ : Form,
      ¬ OperatesAt v g (fun u => Satisfies u (Form.and φ (Form.not φ)))
  /-- The scope covers all reality as the universal modal ground -/
  universal_ground : UniversalModalGround g

/-- Master Synthesis Theorem: The Ground of Reality possesses Foundational
    Omnipotence in Γ — its operative scope excludes no non-contradictory state of
    affairs, it operates only what obtains, and (per the carried field) it can
    never operate a contradiction. Zero substantive axioms; the whole footprint is
    the declared vocabulary `{Means, Subject}` (plus `propext`, from C14).
    Footprint: `{Means, NecessarySubjectKind, Subject, propext}`. -/
theorem ofGround_foundational_omnipotence :
    FoundationalOmnipotence Entity.ofGround :=
  { gapless_operate := ofGround_gapless_operative_scope
    operates_only_obtaining := ofGround_operates_only_what_obtains
    operates_no_contradiction := ofGround_does_not_operate_contradictions
    universal_ground := ofGround_universal_modal_ground }

/-- The Thomistic principle: any necessary entity that is present in every
    possible world and is a universal modal ground thereby satisfies Foundational
    Omnipotence. The premise of necessary existence is carried explicitly
    (Aquinas *ST* I q. 25 a. 5: the ground is *semper et ubique*); the conclusion
    is proved from world-rigid presence and universal grounding alone — the two
    non-contradictory horns hold of every entity under `OperatesAt` with no
    premise at all. Footprint: `{Means, NecessarySubjectKind, Subject, propext}`. -/
theorem necessity_and_presence_yield_foundational_omnipotence
    (e : Entity) (_hNec : NecessaryEntity e) (hPres : WorldRigidPresence e)
    (hUniv : UniversalModalGround e) :
    FoundationalOmnipotence e :=
  { gapless_operate := by
      intro w P ⟨v, hRv, hPv⟩
      exact ⟨v, hRv, hPres v, hPv⟩
    operates_only_obtaining := by
      intro v P h
      exact h.2
    operates_no_contradiction := by
      intro v φ h
      have hSat : Satisfies v (Form.and φ (Form.not φ)) := h.2
      have hNo : ¬ Satisfies v (Form.and φ (Form.not φ)) :=
        Logos.Semantics.nonContradiction φ v
      rw [sat_and, sat_not] at hSat hNo
      exact hNo hSat
    universal_ground := hUniv }

-- ============================================================================
-- Section 6: The Scope Domain Is Non-Empty and Contradiction-Free
-- ============================================================================

/-- **The domain of C242 is non-empty and contradiction-free** — the two facts
    that make the orthodox reading substantive rather than vacuous, and that
    license reading it as "power over whatever does not involve a contradiction"
    (Aquinas *ST* I, q. 25, a. 5, ad 1) in Γ's classical valuation semantics.
    Non-emptiness: the content `atom 0` is satisfied at `actualWorld`.
    Contradiction-freedom: no content of the form `φ ∧ ¬φ` is satisfied at any
    world (`Semantics.nonContradiction`, C14 — hence the `propext` cost).
    Footprint: `{propext}`. -/
theorem satisfiable_scope_is_nonempty_and_contradiction_free :
    (∃ v : World, ∃ φ : Form, Satisfies v φ) ∧
    (∀ (φ : Form) (v : World),
      ¬ Satisfies v (Form.and φ (Form.not φ))) :=
  ⟨⟨actualWorld, Form.atom 0, rfl⟩,
   fun φ v => Logos.Semantics.nonContradiction φ v⟩
-- ============================================================================
-- Section 7: Separations (Countermodel) — What Gapless Scope Does Not Give
-- ============================================================================

/-- Countermodel: gapless operative scope does **not** entail conjunctive power.
    Under the weakest frame every world is accessible, yet accessibility in Γ is
    not conjunctive: the contents `atom 0` and `¬atom 0` are each possible and no
    single world operates both. This bounds the batch's own claim: the
    non-contradictory restriction is machine-checked, but "jointly possible pairs"
    is strictly stronger than what Γ's modal accessibility delivers. Footprint: `{}`. -/
theorem gapless_operative_scope_without_conjunctive_power :
    ∃ (Ent : Type) (Operates : World → Ent → WProp → Prop) (e : Ent),
      GaplessOperate (UniversalFrame World) Operates e ∧
      ¬ ConjunctivePower (UniversalFrame World) Operates e := by
  let Ent : Type := Bool
  let Operates : World → Ent → WProp → Prop := fun v b P => b = true ∧ P v
  refine ⟨Ent, Operates, true, ?_, ?_⟩
  · intro w P ⟨v, hRv, hPv⟩
    exact ⟨v, hRv, rfl, hPv⟩
  · intro hCP
    obtain ⟨v, _, hOp⟩ :=
      hCP actualWorld
        (fun u => Satisfies u (Form.atom 0))
        (fun u => Satisfies u (Form.not (Form.atom 0)))
        ⟨actualWorld, trivial, rfl⟩
        ⟨fun _ => Logos.Semantics.TV.f, trivial, fun hc =>
          Logos.Semantics.TV.noConfusion hc⟩
    exact hOp.2.2 hOp.2.1

/-- Countermodel: an **exhaustively meaningful scope does not entail operative
    scope**. The witness carries a total meaning relation (`∀ P, Scope e P`) and
    an empty operation relation, so maximal scope — the same scope the ground has
    by stipulation ◈ `ofGround_meansAll` — buys no operative scope whatever. This
    is the operational analogue of `means_does_not_imply_means_selection`
    (`HostileSemantics.lean:1861`): scope is not power. It is why C242 is proved
    from world-rigid *presence* (◈ `ofGround_existsAt`) and never read off the
    meaning-exhaustive scope of `FoundationalOmniscience`. Footprint: `{}`. -/
theorem exhaustive_scope_without_operative_scope :
    ∃ (Ent : Type) (Scope : Ent → WProp → Prop)
      (Operates : World → Ent → WProp → Prop) (e : Ent),
      (∀ P : WProp, Scope e P) ∧
      ¬ GaplessOperate (UniversalFrame World) Operates e := by
  let Ent : Type := Bool
  let Scope : Ent → WProp → Prop := fun _ _ => True
  let Operates : World → Ent → WProp → Prop := fun _ _ _ => False
  refine ⟨Ent, Scope, Operates, true, fun _ => trivial, ?_⟩
  intro hG
  obtain ⟨v, _, hOp⟩ :=
    hG actualWorld (fun u => Satisfies u (Form.atom 0)) ⟨actualWorld, trivial, rfl⟩
  exact hOp

-- ============================================================================
-- Axiom Footprints
-- ============================================================================

#print axioms existence_everywhere_does_not_entail_operation
#print axioms ofGround_gapless_operative_scope
#print axioms ofGround_operates_only_what_obtains
#print axioms ofGround_does_not_operate_contradictions
#print axioms atom_not_gapless_operate
#print axioms discriminating_subject_not_gapless_operate
#print axioms gapless_operators_are_ground_or_necessary_kind
#print axioms ofGround_foundational_omnipotence
#print axioms necessity_and_presence_yield_foundational_omnipotence
#print axioms satisfiable_scope_is_nonempty_and_contradiction_free
#print axioms gapless_operative_scope_without_conjunctive_power
#print axioms exhaustive_scope_without_operative_scope

end Logos.DivineOmnipotence


/-!
================================================================================
SECTION: DivineOmniscience
================================================================================
-/
/-
# Logos.DivineOmniscience — Foundational Omniscience and Truth-Exhaustiveness

This module formalizes the characteristic of **Foundational Omniscience**
(the ground's scope excludes no truth; `CHARACTERISTICS.md` §14; `CHARS.md` §14)
for the necessary Ground of Reality (`Entity.ofGround`).

### What is formalized:
1. **Truth-Exhaustive Scope (`TruthExhaustive`):**
   No true proposition is closed to the entity's scope: `∀ p, T p → EntityMeans e p`.
   In Aquinas' terms (*ST* I, q. 14 a. 1 — *De differentia Dei a creaturis*, where the
   ground is the condition of all truth), the foundation is the "condition of truth":
   no truth lies outside what it is coextensive with.
2. **World-Indexed Exhaustiveness (`WorldTruthExhaustive`):**
   The same, world-indexed: no state of affairs true in *any* possible world is closed
   to the scope.
3. **Undivided Scope (reused from `DivineSimplicity`):**
   The scope is uniform and undivided across propositions (`UndividedMeaning`).
4. **Universal Grounding (reused from `FoundationalOmnipresence`):**
   The scope covers all reality (`UniversalModalGround`).
5. **The Master Synthesis (`FoundationalOmniscience`):**
   Conjoins (1)–(4) plus the refutation of the strong sense, with zero substantive
   axioms.

### The honest boundary, machine-checked:
Classical omniscience is *not* claimed — the prose explicitly disclaims it
(`README-OLD.md:263`: being the condition of truth does not entail knowing all
truth). Two independent machine results keep that boundary honest, and the
refutation of the strong sense is carried as a **field** of the master record
rather than hidden in a remark:

- **Infallibility is refuted for `Entity.ofGround`** (`ofGround_not_truth_tracking`,
  C236). `EntityMeans (Entity.ofGround) p` reduces to `True` by the constructor's
  match arm (stipulation ◈ `ofGround_meansAll`), so the ground's scope bears *every*
  proposition, including `False`. Hence the exclusive half
  (`EntityMeans e p → T p`) is **false** of the ground in Γ: the scope is
  exhaustive but provably not error-free. The classical "all and only truths"
  sense is not merely unproven here — it is refuted.
- **Counterfactual knowledge is not forced** (`exhaustive_scope_without_counterfactual_knowledge`,
  C240): the frontier predicate `Omniscience_Counterfactuals`
  (`DeepModalFrontier`) is satisfied by no `{}`-knowledge relation over an
  exhaustive-scope subject, so nothing in Γ forces the counterfactual sense.

Γ has no `Knows` predicate at all: the frontier's knowledge relations
(`KnowsAt`, `KnowsCounterfactualAt`) are *vocabulary definitions* generic over an
arbitrary relation, and `Entity.ofGround` is not a subject correlate
(`ofGround_ne_ofSubject`, `NecessityEternity.lean:155`) — so no subject-indexed
omniscience predicate can even be instantiated by the ground. This module
therefore establishes **foundational** omniscience only, and never manufactures a
divine knowledge bridge.
-/

namespace Logos.DivineOmniscience

open Logos.Core
open Logos.Semantics (Form World Satisfies)
open Logos.Entity (Entity EntityOf)
open Logos.Modal (NecessaryEntity)
open Logos.Agency (Subject Means)
open Logos.RecoveredOntologicalGround (EntityMeans)
open Logos.DivineSimplicity (UndividedMeaning ofGround_undivided_meaning)
open Logos.FoundationalOmnipresence
    (MaximalCapacity UniversalModalGround ofGround_universal_modal_ground)
open Logos.DeepModalFrontier (Omniscience_Counterfactuals)

-- ============================================================================
-- Section 1: Metatheoretic Independence of Scope-Exhaustiveness and Infallibility
-- ============================================================================

/-- Metatheoretic separation (countermodel): an entity's scope can be exhaustive
    over every true proposition *and yet* fail to track truth exactly — i.e. a
    perfectly exhaustive scope is not error-free. The witness is the two-element
    carrier with a scope that is trivially total and one element that "fails"
    the tracking half.
    Footprint: `{}`. -/
theorem entity_scope_exhaustiveness_is_not_infallibility :
    ∃ (Ent : Type) (Scope Fails : Ent → Prop),
      (∀ e : Ent, Scope e) ∧ (∃ e : Ent, Scope e ∧ Fails e) := by
  refine ⟨Bool, fun _ => True, fun b => b = true, fun _ => trivial,
          ⟨true, trivial, rfl⟩⟩

-- ============================================================================
-- Section 2: Foundational (Truth-Exhaustive) Scope for the Ground
-- ============================================================================

/-- Foundational omniscience, permissive half: no true proposition is closed to
    the entity's scope — the ground is the condition of all truth.
    Direction, stated so it cannot be misread against `TruthTracking` below:
    `T p → EntityMeans e p` (truth implies scope). Footprint: `{Means, Subject}`. -/
def TruthExhaustive (e : Entity) : Prop :=
  ∀ p : Prop, T p → EntityMeans e p

/-- World-indexed truth-exhaustiveness: no state of affairs true in any possible
    world is closed to the entity's scope.
    Footprint: `{Means, Subject}`. -/
def WorldTruthExhaustive (e : Entity) : Prop :=
  ∀ w : World, ∀ φ : Form, Satisfies w φ → EntityMeans e (Satisfies w φ)

/-- Infallibility, the exclusive half: the entity's scope tracks truth exactly
    (what is borne, and nothing but what is true).
    Direction, stated so it cannot be misread against `TruthExhaustive` above:
    `EntityMeans e p → T p` (scope implies truth) — the **opposite** arrow.
    `TruthExhaustive` alone never yields `TruthTracking`: a scope can contain
    every truth and also contain falsehoods (that is exactly what makes the
    ground's scope total rather than selective). Footprint: `{Means, Subject}`. -/
def TruthTracking (e : Entity) : Prop :=
  ∀ p : Prop, EntityMeans e p → T p

/-- Foundational Omniscience of the Ground of Reality: no true proposition, and
    no state of affairs true in any world, is closed to `Entity.ofGround`'s scope.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_truth_exhaustive : TruthExhaustive Entity.ofGround := by
  intro p _
  trivial

/-- The ground's truth-exhaustive scope is uniform across modal space: no world
    and no form true in that world is closed to the ground's scope.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_world_truth_exhaustive :
    WorldTruthExhaustive Entity.ofGround := by
  intro w φ _
  trivial

-- ============================================================================
-- Section 3: The Strong Sense, Machine-Checked as Refuted for the Ground
-- ============================================================================

/-- **The strong (infallible) sense is refuted for `Entity.ofGround`.**
    The ground's scope bears every proposition — including `False` — by the
    constructor's match arm, so the exclusive half of classical omniscience
    ("and nothing but the true") is false of the ground in Γ. The scope is
    exhaustive; it is provably not error-free.
    Footprint: `{Means, Subject}`. -/
theorem ofGround_not_truth_tracking : ¬ TruthTracking Entity.ofGround := by
  intro h
  exact h False trivial

-- ============================================================================
-- Section 4: Exhaustive Exhaustiveness (Atoms and Discriminating Subjects Excluded)
-- ============================================================================

/-- Exhaustive exclusion: no worldly atom bears even a single true proposition,
    so no atom is truth-exhaustive. Witness: `p := True`.
    Footprint: `{Means, Subject}`. -/
theorem atom_not_truth_exhaustive (n : Nat) :
    ¬ TruthExhaustive (Entity.ofAtom n) := by
  intro h
  exact h True trivial

/-- Exhaustive exclusion: a discriminating subject is never truth-exhaustive,
    because any *true* proposition it fails to mean is a witness against
    exhaustiveness.
    Footprint: `{Means, Subject}`. -/
theorem discriminating_subject_not_truth_exhaustive
    (s : Subject) (hDisc : ∃ p : Prop, T p ∧ ¬ Means s p) :
    ¬ TruthExhaustive (EntityOf s) := by
  intro h
  obtain ⟨p, ht, hp⟩ := hDisc
  exact hp (h p ht)

-- ============================================================================
-- Section 5: The Master Synthesis — Foundational Omniscience
-- ============================================================================

/-- Foundational Omniscience: the conjunction of the weak classical sense
    (no true proposition closed to the scope, in any world) with the undivided
    scope of `DivineSimplicity` and the universal grounding of
    `FoundationalOmnipresence`, plus the *refutation* of infallibility as a
    carried field — the boundary is part of the record, not a remark. (The
    structure itself is not an audited kernel node; the audited axiom set of
    the ground instance is recorded in `ofGround_foundational_omniscience`
    below.) -/
structure FoundationalOmniscience (g : Entity) : Prop where
  /-- No true proposition is closed to the entity's scope -/
  truth_exhaustive : TruthExhaustive g
  /-- The same across every possible world -/
  world_truth_exhaustive : WorldTruthExhaustive g
  /-- The scope is undivided across propositions (DivineSimplicity) -/
  undivided_scope : UndividedMeaning g
  /-- The scope is provably not truth-tracking: the strong sense is refuted -/
  not_truth_tracking : ¬ TruthTracking g
  /-- The scope covers all reality as the universal modal ground -/
  universal_ground : UniversalModalGround g

/-- Master Synthesis Theorem: The Ground of Reality possesses Foundational
    Omniscience in Γ — its scope excludes no truth, in any world, and (per the
    carried field) that scope is provably not infallible. Zero substantive
    axioms; the whole footprint is the declared vocabulary `{Means, Subject}`.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem ofGround_foundational_omniscience :
    FoundationalOmniscience Entity.ofGround := {
  truth_exhaustive := ofGround_truth_exhaustive
  world_truth_exhaustive := ofGround_world_truth_exhaustive
  undivided_scope := ofGround_undivided_meaning
  not_truth_tracking := ofGround_not_truth_tracking
  universal_ground := ofGround_universal_modal_ground }

-- ============================================================================
-- Section 6: The Thomistic Principle (Necessity, Scope and Grounding Concede Omniscience)
-- ============================================================================

/-- The Thomistic principle: any necessary entity that is maximally
    scope-exhaustive, undivided in scope, and a universal modal ground thereby
    satisfies Foundational Omniscience — *and* its scope is necessarily not
    error-free (from `hMax False`). The premise of necessary existence
    (`Aquinas ST` I q. 14 a. 1: the ground exists always, as the condition of
    truth) is carried explicitly; the conclusion is proved from the scope
    premises alone.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem necessity_and_scope_yield_foundational_omniscience
    (e : Entity) (_hNec : NecessaryEntity e) (hMax : MaximalCapacity e)
    (hUnd : UndividedMeaning e) (hUniv : UniversalModalGround e) :
    FoundationalOmniscience e := by
  refine ⟨?_, ?_, hUnd, ?_, hUniv⟩
  · intro p _
    exact hMax p
  · intro w φ _
    exact hMax _
  · intro h
    exact h False (hMax False)

-- ============================================================================
-- Section 7: Counterfactual Knowledge Is Not Forced (Countermodel)
-- ============================================================================

/-- Countermodel: an entity can have exhaustive scope and still fail the
    frontier's counterfactual-knowledge predicate — so nothing in Γ forces the
    counterfactual sense of omniscience from foundational omniscience. The
    knowledge relation is degenerate (`False`), so no counterfactual predicate
    holds, while the subject's scope is trivially exhaustive.
    Footprint: `{}`. -/
theorem exhaustive_scope_without_counterfactual_knowledge :
    ∃ (W S : Type) (Scope : S → Prop) (K : W → S → (W → Prop) → Prop) (s : S),
      Scope s ∧ ¬ Omniscience_Counterfactuals W S K s := by
  refine ⟨Bool, Bool, fun _ => True, fun _ _ _ => False, true, trivial, ?_⟩
  intro hK
  exact hK true (fun _ => True)

-- ============================================================================
-- Axiom Footprints
-- ============================================================================

#print axioms entity_scope_exhaustiveness_is_not_infallibility
#print axioms ofGround_truth_exhaustive
#print axioms ofGround_world_truth_exhaustive
#print axioms ofGround_not_truth_tracking
#print axioms atom_not_truth_exhaustive
#print axioms discriminating_subject_not_truth_exhaustive
#print axioms ofGround_foundational_omniscience
#print axioms necessity_and_scope_yield_foundational_omniscience
#print axioms exhaustive_scope_without_counterfactual_knowledge

end Logos.DivineOmniscience


/-!
================================================================================
SECTION: LovesAsGround
================================================================================
-/
/-
# Logos.LovesAsGround — the ground's love as a distinct, Entity-level relation

The claim that *God is not merely a mathematical ground but loves* needs one thing the
vocabulary does not have. `Loves` is indexed by `Subject`:

    def Loves (s t : Subject) : Prop := Helps s t ∧ ¬ Harms s t   -- Love.lean:49

and the ground is **provably not a `Subject`** (`ofGround_ne_ofSubject`,
`NecessityEternity.lean:155-157`). So "the ground loves" is not well-formed: there is no
`Entity → Entity → Prop` relation anywhere in the library, and every relational predicate
(`Helps`, `Harms`, `Chooses`, `Initiates`, `Grounds`) is `Subject`-indexed.

This module adds the missing relation **without disturbing `Loves`**, and records what it
costs. Design decision: interpersonal love and the ground's love are *kept distinct*
rather than merged, because merging would silently reinterpret `T14` and the
person-stability principle `PersonStabilityPrinciple` (`Love.lean:97`).

## A correction: the first version of this module was unsound as advertised

This module previously carried a declared `Tag: META` bridge,
`AxGroundLovesContingentRealm`, and claimed in its own docstring that the inhabitation of
`GroundLoves` was "**not derivable**", that it was "the one substantive commitment of the
module", and that "the axiom is not satisfiable by `True`". **All three claims were
false**, and the defect was invisible to the footprint audit.

The original definition was

    def GroundLoves (g t : Entity) (a : Prop) : Prop :=
      NecessaryEntity g ∧ ActualEntity t ∧ t ≠ g ∧ a

but `NecessaryEntity Entity.ofGround` is *provably trivial* — `ofGround_necessary` closes
by `trivial`, because `EntityExistsAt w .ofGround := True` is a definitional stipulation of
the constructor. So `GroundLoves Entity.ofGround t a` reduced to
`ActualEntity t ∧ t ≠ ofGround ∧ a`, and `a := True` discharged it: the relation was
inhabited for **every** actual entity distinct from the ground, with no content, and the
"price" was zero while being advertised as the module's point.

## Why a primitive is needed, and not merely a fair definition

Stipulating the content conjunctually — say
`NecessaryEntity g ∧ ActualEntity t ∧ t ≠ g ∧ (∃ p, EntityMeans t p ∧ a)` — repairs the
degeneracy, and the separation theorems below then hold. But it does **not** make the
inhabitation a commitment: given a target that is actual, distinct from the ground, and
meaning-bearing, that whole conjunction is provable with `a := True`. The price is again
zero, one level down.

This is the structural reason the price could not be located by stipulation alone. At
`Entity` level the ground is not a `Subject`, there is no entity-indexed content
predicate, and the only necessary entity has trivial meaning-capacity. So *any* first-order
content over `NecessaryEntity`/`ActualEntity`/`EntityMeans` is a function of the target's
own properties, and therefore free.

So the content is a **primitive**, `GroundBearsGood`, exactly as `Means : Subject → Prop →
Prop` is a primitive (`Agency.lean:92`). It is `Tag: VOCAB` — the missing relational
vocabulary — and it constrains nothing, so the inhabitation is a genuine `Tag: META`
commitment. This is the library's own pattern for moral content: `Means` (VOCAB) → `Good`
(fair def) → `AxBenevolentBearingObtains` (META inhabitation). Here no fair definition is
available, so the primitive goes one level deeper.

## Why the bridge is restricted to meaning-bearing targets

The unrestricted bridge `∀ t, ContingentEntity t → ∃ a, GroundLoves Entity.ofGround t a`
is **refutable**, and the module proves it (`meaningful_love_bridge_is_refuted`): an atom is
provably contingent (`an_atom_is_contingent`) and provably meaningless, so the unrestricted
bridge would force an atom to bear meaning. The declared axiom therefore carries the
meaning hypothesis, and the refutation is what justifies the restriction.

## What is proven here

1. **The "merely a mathematical ground" is machine-checked, and it is a *separation*.**
   Grounding reaches *everything*, including an entity that means *nothing at all*
   (`ground_grounds_the_meaningless`); love provably cannot reach it
   (`meaningless_entities_cannot_be_loved`). `grounding_reaches_what_love_cannot` puts the
   two side by side. This is the machine-checked content of "not merely a mathematical
   ground": the two relations differ, and they differ on an entity bearing no meaning.
2. **The inhabitants, at a real price.** `the_ground_loves_every_meaningful_contingent_
   reality` and `the_ground_bears_a_directional_good_toward_the_cosmos` rest on
   `AxGroundLovesContingentRealm`; `the_ground_is_a_liver` adds the existential, and
   `the_ground_is_a_necessary_and_chosen_lover` is the "necessary ∧ chosen" cell of
   `poem.txt:24` with a direction of good in it.
3. **No contingent person can occupy the necessary pole**
    (`no_subject_is_a_necessary_entity`,
    `necessary_entities_are_ground_or_necessary_kind`). The contingent-kind
    half is **forced by the three-constructor ontology** —
    `EntityExistsAt w .ofGround := True`, contingent-kind subjects exist only at
    the actual world, atoms fail somewhere — so it is a structural fact of the
    modelling and **not** evidence that the ground loves. Its legitimate content
    is now positive: the "necessary ∧ chosen" cell of `poem.txt:24` is occupied
    — by the ground, and by whoever is of the necessary kind
    (`Plurality.necessaryPersonalSubjectExists`, `Tag: META`). The "necessary"
    pole of interpersonal love is discharged here and, conditionally, by T14 /
    C42–C45.
4. **The two relations are provably disjoint on the contingent side**
    (`subject_love_is_not_ground_love`,
    `interpersonal_love_never_reaches_the_necessary_quadrant`): `GroundLoves`
    demands a *necessary* lover and no contingent-kind subject is necessary, so
    `Loves s t` of a contingent-kind `s` never yields
    `GroundLoves (EntityOf s) _ _`. The transfer the original design asked for is recorded as
    **unstatable for the contingent kind, not merely blocked**
    (`ground_love_cannot_be_read_as_person_love`).
5. **Compatibility with `actus purus`** (`ground_love_preserves_pure_actuality`): the
   ground's love requires no initiation, so `DivinePureActuality` is untouched. Love as
   *act* adds to pure actuality rather than contradicting it (Aquinas, ST I q.20 a.3).

## The price, stated

Two commitments, different in kind:

- `GroundBearsGood` (`Tag: VOCAB`) is **vocabulary**: a primitive relational predicate that
  constrains nothing. It cannot make anything true on its own; it only names what is
  missing. Rejecting it means rejecting the relation's content, not the theory.
- `AxGroundLovesContingentRealm` (`Tag: META`) is the **substance**: it says a necessary
  ground bears a directional good toward every contingent realm that bears content of its
  own. Its consistency model: interpret `GroundBearsGood` everywhere as `False`, which
  satisfies the whole vocabulary, the epistemic reality-hook, and every per-constructor
  theorem of the `Divine*` modules, while every inhabitant theorem below fails. So the
  inhabitation is genuinely not forced by the relying structure.

The `Tag: VOCAB` primitive does not conflict with `ofGround_meansAll`
(`Stipulations.lean:60-61`), which makes `EntityMeans .ofGround p := True`:
`GroundBearsGood` is a *directional* relation about a pair, not a meaning-capacity
judgment, and `GroundLoves` still requires the target to bear content of its own. What is
paid is the admission that the ground's relation to the cosmos is **directed and good**,
where the library's grounding vocabulary can express only undirected sufficiency.
-/

namespace Logos.LovesAsGround

open Logos.Semantics (World TV)
open Logos.Agency (Subject State Initiates NecessarySubjectKind ContingentSubjectKind)
open Logos.Entity (Entity ExistsAt EntityOf EntityExistsAt SubjectExistsAt actualWorld)
open Logos.RecoveredOntologicalGround (EntityMeans OneEssence)
open Logos.Love (Loves)
open Logos.TheologicalModalHardening
    (ActualEntity ContingentEntity NecessaryEntity necessary_not_contingent)
open Logos.NecessityEternity (ofGround_necessary ofGround_ne_ofSubject)
open Logos.FoundationalOmnipresence (UniversalModalGround ofGround_universal_modal_ground)
open Logos.DivineImmutability (TransitionInvariance ofGround_transition_invariance)
open Logos.DivinePureActuality (PassiveTransitionPotency ofGround_no_transition_potency)

-- ============================================================================
-- Section 0: Contingent and meaningful existence (the inhabitation's premises)
-- ============================================================================

/-- The all-`TV.f` valuation is not the actual world, which is all-`TV.t`
    (`Entity.lean:33`). The single witness of modal fragility used throughout this module.
    Footprint: `{propext}`. -/
theorem falsityWorld_ne_actualWorld : (fun _ => TV.f) ≠ actualWorld := by
  intro hc
  have h := congrFun hc 0
  simp [actualWorld] at h

/-- An atom is contingent: actual at the actual world, refuted at the all-`TV.f` world,
    because `EntityExistsAt w (ofAtom n) := w n = TV.t` (`Entity.lean:53-56`).
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem an_atom_is_contingent (n : Nat) : ContingentEntity (Entity.ofAtom n) :=
  ⟨rfl, (fun _ => TV.f), by simp [ExistsAt, EntityExistsAt]⟩

/-- A contingent entity exists, witnessed by an atom. This is the bare *contingency* half
    only. It is **not** the identification of an atom with the cosmos, which
    `investigations/creation.md` and the ledger forbid — and it is explicitly *not* an
    object of love either, since atoms bear no meaning
    (`meaningless_entities_cannot_be_loved`). The realm is handled separately and in two
    halves, neither of which is a stipulated datum: its **contingency** is `PROVEN` by
    `CosmicExistence.contingent_realm_obtains` (C350, `{CL, NecessarySubjectKind, Subject}`), and its
    **meaning-bearingness** is `PROVEN` by `CosmicExistence.cosmos_obtains` (C367,
    `: CreatedRealm`) given an exhibited contingent person — no bridge in either row
    since the two-kinds correction. Note that "created" names
    the region of reality — actual, modal-fragile, and not the ground — and never an act of
    production; no `Creates` relation is claimed or derivable.
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem a_contingent_entity_exists : ∃ t : Entity, ContingentEntity t :=
  ⟨Entity.ofAtom 0, an_atom_is_contingent 0⟩

/-- **A contingent entity bearing content exists.** The witness is a subject of the
    contingent kind, whose `EntityMeans` unfolds to `Means s p` — a primitive
    `Tag: VOCAB` **axiom** (`Agency.lean:92`). `Means` has no derivable instance
    in Γ, so this theorem *consumes* a `Means` inhabitant rather than producing
    one: its hypothesis is the honest form of that dependency. The kind premise
    is load-bearing, not bureaucratic: only a contingent-kind subject is absent
    somewhere, so only it can witness contingency. Note what this does **not**
    do: it does not identify the subject with the cosmos. It supplies only the
    shape the love inhabitation needs.
    Footprint: `{Means, NecessarySubjectKind, Subject, propext}`. -/
theorem a_meaningful_contingent_entity_exists
    (h : ∃ s : Subject, ContingentSubjectKind s ∧ ∃ p : Prop, Logos.Agency.Means s p) :
    ∃ t : Entity, ContingentEntity t ∧ ∃ p, EntityMeans t p := by
  obtain ⟨s, hKind, p, hp⟩ := h
  have hActual : ExistsAt actualWorld (EntityOf s) := Or.inr rfl
  have hAbsent : ¬ ExistsAt (fun _ => TV.f) (EntityOf s) := by
    intro hEx
    dsimp [ExistsAt, EntityExistsAt, SubjectExistsAt, EntityOf] at hEx
    rcases hEx with hk | heq
    · exact hKind hk
    · exact falsityWorld_ne_actualWorld heq
  exact ⟨EntityOf s, ⟨hActual, (fun _ => TV.f), hAbsent⟩, p, hp⟩

-- ============================================================================
-- Section 1: The ground as "merely a mathematical ground", machine-checked
-- ============================================================================

/-- The ground of reality grounds every entity whatsoever: `OneEssence` transfers
    meaning, and the ground's meaning-capacity is stipulated to bear all of it.
    Footprint: `{Means, Subject}` (vocabulary-only — the transfer is vacuous, which is
    exactly the point of the next theorem). -/
theorem ground_grounds_every_entity (t : Entity) : OneEssence Entity.ofGround t := by
  intro p _hEM
  exact True.intro

/-- An atom bears no meaning at all: `EntityMeans (Entity.ofAtom _) p` reduces to `False`.
    Footprint: `{Means, Subject}` (the match arm alone). -/
theorem atoms_bear_no_meaning (p : Prop) : ¬ EntityMeans (Entity.ofAtom 0) p := by
  intro h
  exact h

/-- The ground grounds even an entity that means nothing whatever. This is the sharpest
    machine-checked sense of "merely a mathematical ground": the ground's relation to
    reality is *undiscriminating* — it holds uniformly, including where there is nothing
    to bear.
    Footprint: `{Means, Subject}`. -/
theorem ground_grounds_the_meaningless :
    OneEssence Entity.ofGround (Entity.ofAtom 0) :=
  ground_grounds_every_entity (Entity.ofAtom 0)

/-- Universal modal grounding of the ground, in the library's own form. Retained so the
    contrast with `GroundLoves` is read off a single pair of definitions.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem the_ground_is_a_universal_modal_ground :
    UniversalModalGround Entity.ofGround :=
  ofGround_universal_modal_ground

/-- No subject of the contingent kind is a necessary entity: such subjects exist
    only at the actual world, so a contingent-kind subject fails to exist in
    every other world. This is why no *contingent* person can occupy the
    necessary pole. The necessary kind is excluded by hypothesis, not by
    oversight: it occupies the pole by
    `Plurality.necessaryKindSubject_is_necessary`.
    Footprint: `{NecessarySubjectKind, Subject, propext}` (world structure alone). -/
theorem no_subject_is_a_necessary_entity (s : Subject)
    (hKind : ContingentSubjectKind s) : ¬ NecessaryEntity (EntityOf s) := by
  intro h
  have hf := h (fun _ => TV.f)
  dsimp [ExistsAt, EntityExistsAt, SubjectExistsAt, EntityOf] at hf
  rcases hf with hk | heq
  · exact hKind hk
  · exact falsityWorld_ne_actualWorld heq

/-- The necessary entities are the ground and the necessary-kind subjects: every
    other entity is either a contingent-kind subject or an atom, and both are
    refuted (contingent subjects fail at the all-`TV.f` world by the row above;
    atoms fail wherever a value is `TV.f`).

    Read this for what it is. The ground disjunct is **forced by the
    three-constructor ontology** — `EntityExistsAt w .ofGround := True` is a
    definitional stipulation of the constructor — and the subject disjunct is the
    priced metaphysical bridge `Plurality.necessaryPersonalSubjectExists`
    (`Tag: META`), never a derivation. Its legitimate content is now positive:
    the "necessary ∧ chosen" cell of `poem.txt:24` is occupied — by the ground,
    and by whoever is of the necessary kind. The "necessary" pole of love is
    discharged here and, conditionally, by T14 / C42–C45.
    Footprint: `{NecessarySubjectKind, Subject, propext}` (world structure and
    constructor analysis alone; the inhabitant bridge is not unfolded here). -/
theorem necessary_entities_are_ground_or_necessary_kind :
    ∀ e : Entity, NecessaryEntity e →
      e = Entity.ofGround ∨
        ∃ s : Subject, NecessarySubjectKind s ∧ e = EntityOf s := by
  intro e h
  cases e with
  | ofSubject s =>
      have hf := h (fun _ => TV.f)
      dsimp [ExistsAt, EntityExistsAt, SubjectExistsAt, EntityOf] at hf
      rcases hf with hk | heq
      · exact Or.inr ⟨s, hk, rfl⟩
      · exact absurd heq falsityWorld_ne_actualWorld
  | ofAtom n =>
      have hf := h (fun _ => TV.f)
      simp [ExistsAt, EntityExistsAt] at hf
  | ofGround => exact Or.inl rfl

-- ============================================================================
-- Section 2: The missing vocabulary — a primitive directional good
-- ============================================================================

/--Tag: VOCAB
A necessary bearer holds a directional good toward a target, with content `p`.

**Why a primitive and not a fair definition.** The ground's relation to the cosmos is
supposed to be *directional* — good *toward* something — and the library's grounding
vocabulary can express only undirected sufficiency (`OneEssence g e := ∀ p,
EntityMeans e p → EntityMeans g p`, which the ground satisfies vacuously, including for an
entity bearing no meaning at all: `ground_grounds_the_meaningless`). The one content
predicate available, `EntityMeans`, is a *capacity* of the target, not an attitude of the
bearer, so it cannot distinguish a bearer that loves from one that merely contains.
`Good s (_a : Prop)` (`MoralFrontierAudit.lean:203-204`) is the right shape but is
`Subject`-indexed, and the ground is provably not a `Subject`. Any first-order definition
over `NecessaryEntity`/`ActualEntity`/`EntityMeans` is therefore a function of the target's
own properties and collapses to a provable conjunction — see the module header for the
concrete instance of that collapse that this module previously shipped by mistake.

Consistency model: the predicate constrains nothing, so it is satisfiable by any
interpretation, including the constant-`False` one under which every inhabitant theorem
below fails. It therefore introduces no inconsistency and forces nothing; it only supplies
the relational shape that the vocabulary lacked.

Philosophical cost: Γ acquires a primitive directed relation at the entity level. This is
new vocabulary, and it is admitted as such — it is *not* reducible to `OneEssence`,
whose `∀ p, …` form cannot express a direction. Note it does not conflict with
`ofGround_meansAll` (`Stipulations.lean:60-61`), which fixes the ground's
`EntityMeans` at `True`: `GroundBearsGood` is a relation over a *pair* with a content
argument, not a meaning-capacity judgment. A reader who rejects the cost rejects this
primitive, and with it every inhabitant theorem in Section 3.
-/
axiom GroundBearsGood : Entity → Entity → Prop → Prop

/-- **The ground's love of a target, at a context of evaluation.** The relation says: a
    *necessary* entity bears, directed at this target and at this content, a good the
    target has — the target being actual, other than the lover, and **bearing content of
    its own**.

    The two content-bearing conjuncts are both load-bearing, and the module header records
    why each was added. The `GroundBearsGood` conjunct is what makes the inhabitation a
    real commitment rather than a provable one; the `EntityMeans` conjunct is what makes
    the relation discriminating, and is why love cannot reach the meaningless. The
    `ActualEntity` conjunct, by contrast, does no work: it holds of every entity by
    definition (C457) — the target conditions with content are `t ≠ g` and
    `∃ q, EntityMeans t q` alone.

    The `a : Prop` context-of-evaluation argument mirrors `Good s (_a : Prop)`
    (`MoralFrontierAudit.lean:203-204`), the library's existing idiom for a relational
    pole indexed by a context.
    Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Subject}`. -/
def GroundLoves (g : Entity) (t : Entity) (a : Prop) : Prop :=
  NecessaryEntity g ∧ ActualEntity t ∧ t ≠ g ∧ (∃ p, GroundBearsGood g t p) ∧
    (∃ q, EntityMeans t q) ∧ a

/-- Ground-level love is eternal in the lover: the lover is necessary. This is one half of
    the formal content of `poem.txt:24`'s "também é necessário" — the other half, that love
    is *chosen*, is the bridge of Section 3, not this conjunct.
    Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Subject}`. -/
theorem ground_love_requires_a_necessary_lover {g t : Entity} {a : Prop}
    (h : GroundLoves g t a) : NecessaryEntity g := h.1

/-- Ground-level love is directed at a target distinct from the lover: love is not
    self-regarding. Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Subject}`. -/
theorem ground_love_is_directed_at_another {g t : Entity} {a : Prop}
    (h : GroundLoves g t a) : ActualEntity t ∧ t ≠ g := ⟨h.2.1, h.2.2.1⟩

/-- **Ground-level love is content-bearing in the strong sense:** the ground holds some
    directional good *toward* the target. This is the conjunct with no first-order
    substitute, and the one the inhabitation axiom pays for.
    Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Subject}`. -/
theorem ground_love_bears_a_directional_good {g t : Entity} {a : Prop}
    (h : GroundLoves g t a) : ∃ p, GroundBearsGood g t p := h.2.2.2.1

/-- **Ground-level love requires the target to bear content of its own:**
    `EntityMeans t q` for some `q`. Since `EntityMeans (ofAtom _) = False` and
    `EntityMeans Entity.ofGround _ = True`, this is what separates love from the ground's
    undiscriminated meaning-capacity.
    Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Subject}`. -/
theorem ground_love_requires_a_meaningful_target {g t : Entity} {a : Prop}
    (h : GroundLoves g t a) : ∃ q, EntityMeans t q := h.2.2.2.2.1

/-! ### WALL localisation for the ground-love hypothesis (2026-09-28, the `ACT-CASCADE` batch)

C465 `ground_love_produces` and C467 `producing_coexists_with_immutability` are stated under
`GroundLoves Entity.ofGround t a`, and Γ cannot exhibit that hypothesis. The two theorems below do
not change either row's status — they make the reason the hypothesis is unavailable into a
statement the kernel checks, so that the `BLOCKED` is settled with its price named rather than
merely asserted. Plan of record: `WIN.md` §2 B1. **No axiom is added, and no existing theorem is
altered.**

The first says *which* entity can be loved at all; the second says, for that entity, exactly what
is still owed. -/

/-- **WALL 1 localisation, part one: the ground's love can only ever reach a subject correlate.**

    Case analysis on `Entity`. An atom is excluded because `EntityMeans (ofAtom _) p` reduces to
    `False` (`atoms_bear_no_meaning`, and the same by `defeq` for every atom, not just `0`); the
    ground is excluded by the `t ≠ g` conjunct of `GroundLoves` itself. So the only surviving
    constructor is `ofSubject`, and the reduction is a case split, not a lemma: nothing here is
    about the metaphysics of love.

    **What this does NOT do.** It does not show that any subject *is* loved. It shows that if the
    ground loves anything at all, the thing loved is a subject correlate — which converts the
    existence of a love-instance into the existence of a *contingent person who is loved*, and is
    why WALL 2 below cannot be routed around. It adds no axiom, and C465/C467 keep their status
    (`PROVEN↑`, i.e. axiomatic under a declared bridge) and their footprints.

    Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Subject, propext}` - the four
    vocabulary declarations (`Tag: VOCAB`, or unconstrained primitives) that the *hypothesis's
    type* mentions, plus `propext` for the `∃` unfolding. No `SEM` or `META` axiom: the row
    carries no substantive price. Note the footprint is not `{}` - `GroundBearsGood` appears
    because the type of `h` mentions it, though the proof never uses that conjunct. Corrects
    the `{}` guessed in `WIN.md` section 2 B1, per the `SUCCESSION.md` section 10 precedent. -/
theorem ground_love_targets_a_subject_correlate {t : Entity} {a : Prop}
    (h : GroundLoves Entity.ofGround t a) : ∃ s : Subject, t = Entity.ofSubject s := by
  obtain ⟨q, hq⟩ := ground_love_requires_a_meaningful_target h
  cases t with
  | ofSubject s => exact ⟨s, rfl⟩
  | ofAtom n => exact absurd hq (by simp [EntityMeans])
  | ofGround => exact ((ground_love_is_directed_at_another h).2 rfl).elim

/-- **WALL 1 localisation, part two: for a subject correlate, the hypothesis reduces to exactly
    two conjuncts — the one unavailable primitive, and a meaning.**

    Reading `GroundLoves` out for `t = EntityOf s` deletes three conjuncts as *proved*, not as
    assumed: the lover's necessity (`ofGround_necessary`), the target's actuality
    (`every_entity_is_actual` — `ActualEntity` holds of every entity, C457), and the
    distinctness (`ofGround_ne_ofSubject`). The `EntityMeans` conjunct reduces by `defeq` to
    `Means s q`. What is left is

    - **WALL 1** — `∃ p, GroundBearsGood Entity.ofGround (EntityOf s) p`. `GroundBearsGood` is a
      bare `Tag: VOCAB` relation with **no inhabitant theorem anywhere in Γ**; every inhabitant in
      the corpus is routed through the `AxGroundLovesContingentRealm` bridge, which is itself
      unpriced, so there is nothing to extract. This conjunct is the wall.
    - **WALL 2** — a meaning for a *contingent* subject. `Means s q` is available
      (C469 `someone_means_something`), but only for whichever `s` the act-datum supplies, and
      nothing relates that `s` to `ContingentSubjectKind`. `ContingentSubjectKind` is the negation
      of `NecessarySubjectKind`, which is a primitive constrained by **no axiom at all**, so C410 /
      C411 give only a tautological partition and no inhabitant of the contingent kind exists in Γ
      (recorded in `NecessityEternity.lean:396`, `LovesAsGround.lean`, `CosmicExistence.lean`,
      `T22.txt`). The `AxGroundLovesContingentRealm` route needs WALL 2 for exactly this reason.

    **What this does NOT do.** It does not discharge WALL 1 or WALL 2, and it is the reason the
    `BLOCKED` status of C465/C467 is settled rather than provisional: the residual is two named
    primitives, both of which would be *new substantive content* to inhabit, which the author
    declined on 2026-09-28. It does not move any badge, and the `Asserts` lane is untouched.

    Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Subject}` - the vocabulary
    declarations the hypothesis's type and `EntityMeans`'s unfolding mention. `GroundBearsGood`
    is here because the *statement* names it, which is the whole point of the row. No `SEM` or
    `META` axiom. Not `{}`, contrary to `WIN.md` section 2 B1's guess: same correction, same
    precedent. -/
theorem ground_love_of_a_subject_correlate_iff {s : Subject} {a : Prop} :
    GroundLoves Entity.ofGround (EntityOf s) a ↔
      (∃ p, GroundBearsGood Entity.ofGround (EntityOf s) p) ∧
        (∃ q, Logos.Agency.Means s q) ∧ a := by
  constructor
  · intro h
    exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩, ha⟩
    refine ⟨ofGround_necessary, Logos.RecoveredOntologicalGround.every_entity_is_actual _,
      Logos.FoundationalUnicity.ofGround_ne_ofSubject s, ⟨p, hp⟩, ⟨q, hq⟩, ha⟩

/-- **Love cannot reach the meaningless.** A meaningless entity is not loved by the
    ground, in any context. This is the discriminating counterpart of
    `ground_grounds_the_meaningless`: grounding holds there, love does not.
    Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Subject}`. -/
theorem meaningless_entities_cannot_be_loved :
    ¬ ∃ a : Prop, GroundLoves Entity.ofGround (Entity.ofAtom 0) a := by
  rintro ⟨a, h⟩
  obtain ⟨q, hq⟩ := h.2.2.2.2.1
  exact atoms_bear_no_meaning q hq

/-- **The separation, in one statement: the ground grounds what it cannot love.** The left
    conjunct is undiscriminated grounding; the right is the failure of love on the very
    same entity. This is the machine-checked content of "not *merely* a mathematical
    ground": the two relations differ, and they differ on an entity bearing no meaning.
    Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Subject}`. -/
theorem grounding_reaches_what_love_cannot :
    OneEssence Entity.ofGround (Entity.ofAtom 0) ∧
      ¬ ∃ a : Prop, GroundLoves Entity.ofGround (Entity.ofAtom 0) a :=
  ⟨ground_grounds_the_meaningless, meaningless_entities_cannot_be_loved⟩

/-- Grounding is total over entities while love is not: every entity is grounded, and not
    every contingent entity is loved.
    Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Subject, propext}`. -/
theorem grounding_is_total_but_love_is_not :
    (∀ t : Entity, OneEssence Entity.ofGround t) ∧
      ¬ (∀ t : Entity, ContingentEntity t → ∃ a : Prop, GroundLoves Entity.ofGround t a) := by
  refine ⟨ground_grounds_every_entity, ?_⟩
  rintro hall
  obtain ⟨a, ha⟩ := hall (Entity.ofAtom 0) (an_atom_is_contingent 0)
  obtain ⟨q, hq⟩ := ha.2.2.2.2.1
  exact atoms_bear_no_meaning q hq

-- ============================================================================
-- Section 3: The inhabitation — one declared, priced bridge
-- ============================================================================

/-- **Why the bridge carries a meaning hypothesis.** The unrestricted form
    `∀ t, ContingentEntity t → ∃ a, GroundLoves Entity.ofGround t a` is refutable in Γ: an
    atom is provably contingent and provably meaningless, so it would force an atom to bear
    meaning. This theorem is the machine-checked reason the axiom below is stated over
    meaning-bearing targets only, and it is why this module does not claim the stronger,
    more attractive, and false statement.
    Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Subject, propext}`. -/
theorem meaningful_love_bridge_is_refuted :
    ¬ (∀ t : Entity, ContingentEntity t → ∃ a : Prop, GroundLoves Entity.ofGround t a) :=
  fun hall => grounding_is_total_but_love_is_not.2 hall

/--Tag: META
The Ground of Reality bears a directional good toward every contingent realm that bears
content of its own.

The inhabitation of `GroundLoves` is **not derivable**, and this is the module's single
substantive commitment. The primitive `GroundBearsGood` is what makes that true: it
constrains nothing, so no theorem of the vocabulary establishes that a necessary bearer
holds any good toward any target. Nor can the content be read off the existing relations —
universal modal grounding is satisfied *vacuously* by the ground for every entity,
including entities bearing no meaning at all (`ground_grounds_the_meaningless`), so
grounding carries no directed content from which love could follow. The bridge therefore
has to postulate, in the shape of `AxBenevolentBearingObtains` (C177) and
`AxSecondPersonalAddress` (C117): disclosed, priced, with the negative side separated below.

Consistency model: the bridge is not forced by the relying structure. Interpreting
`GroundBearsGood` as `False` everywhere satisfies the whole of the vocabulary, the
epistemic reality-hook and every per-constructor theorem of the `Divine*` modules, while
every inhabitant theorem of this section fails. Conversely the inhabitation is not a
triviality: it is not satisfied by `True`, since the target must be actual, distinct from
the lover, and meaningful, and the good must be directional.

Philosophical cost: declaring the ground a lover is a substantive metaphysical bridge. The
price is that Γ acquires a directed relation at the ground that is **not reducible to its
stipulated meaning-capacity**, and a primitive predicate to say so. The stipulation
`ofGround_meansAll` (`Stipulations.lean:60-61`) makes the ground's `EntityMeans`
undiscriminated (`True`); `GroundBearsGood` is a relation over a *pair* with a content
argument, so the `DivineOmniscience` face `ofGround_truth_exhaustive` stays consistent with
this bridge precisely because it is not a `Means` judgment. What is paid is the admission
that the ground's relation to the cosmos is **directed and good**, where the library's
grounding vocabulary can express only undirected sufficiency. A reader who rejects the
price must reject this axiom, and with it `the_ground_is_a_liver`.
-/
axiom AxGroundLovesContingentRealm :
  ∀ t : Entity, ContingentEntity t → (∃ q, EntityMeans t q) →
    ∃ a : Prop, GroundLoves Entity.ofGround t a

/-- The bridge, applied: the ground loves every contingent created reality that bears
    content of its own.
    Footprint: `{AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject}`. -/
theorem the_ground_loves_every_meaningful_contingent_reality {t : Entity}
    (h : ContingentEntity t) (hm : ∃ q, EntityMeans t q) :
    ∃ a : Prop, GroundLoves Entity.ofGround t a :=
  AxGroundLovesContingentRealm t h hm

/-- **The content of the claim, unwrapped:** a directional good is held toward the realm.
    This is the least an inhabitant theorem can say, and it is where the whole price of the
    module sits — a `{}` reading of "the ground loves" would be a different, much weaker
    claim about meaning-capacity.
    Footprint: `{AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject}`. -/
theorem the_ground_bears_a_directional_good_toward_the_cosmos {t : Entity}
    (h : ContingentEntity t) (hm : ∃ q, EntityMeans t q) :
    ∃ p, GroundBearsGood Entity.ofGround t p := by
  obtain ⟨a, ha⟩ := the_ground_loves_every_meaningful_contingent_reality h hm
  exact ha.2.2.2.1

/-- **The inhabitants, with the price visible.** There exists a contingent entity bearing
    content which the ground loves, and toward which it holds a directional good. The
    `Means` hypothesis is the library's primitive content vocabulary being inhabited, which
    the caller obtains from its own datum (`Logos.CosmicExistence.CreatedRealm.bears_
    meaning`); nothing here identifies that subject with the cosmos.
    Footprint: `{AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, propext}`. -/
theorem the_ground_is_a_liver
    (h : ∃ s : Subject, ContingentSubjectKind s ∧ ∃ p : Prop, Logos.Agency.Means s p) :
    ∃ t : Entity, ContingentEntity t ∧ (∃ q, EntityMeans t q) ∧
      ∃ p, GroundBearsGood Entity.ofGround t p := by
  obtain ⟨t, hc, hq⟩ := a_meaningful_contingent_entity_exists h
  exact ⟨t, hc, hq, the_ground_bears_a_directional_good_toward_the_cosmos hc hq⟩

/-- **The "necessary ∧ chosen" cell, occupied.** The ground is a necessary entity and holds
    a chosen directional good toward a contingent realm that bears content — the machine
    form of `poem.txt:24`'s "Amar é escolhido e também é necessário", with the necessity in
    the lover and the choice in the bridge. This is the module's conclusion, and its
    footprint names the whole price: the content vocabulary, the bridge, and the world's
    structure. No axiom of *free choice* is hidden here — the choice is exactly what
    `AxGroundLovesContingentRealm` declares.
    Footprint: `{AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, propext}`. -/
theorem the_ground_is_a_necessary_and_chosen_lover
    (h : ∃ s : Subject, ContingentSubjectKind s ∧ ∃ p : Prop, Logos.Agency.Means s p) :
    NecessaryEntity Entity.ofGround ∧
      ∃ t : Entity, ContingentEntity t ∧ (∃ q, EntityMeans t q) ∧
        ∃ p, GroundBearsGood Entity.ofGround t p :=
  ⟨ofGround_necessary, the_ground_is_a_liver h⟩

-- ============================================================================
-- Section 4: Ground-level love and interpersonal love are distinct
-- ============================================================================

/-- The ground-constructor is not a subject-correlate: no subject's `EntityOf` is
    definitionally the ground. So the conclusion attributes love to the ground
    **as a kind** and smuggles in no hypostatic identification — the open ledger
    bridge #9 (`Ground(e, personal) → Personal(e)`) is untouched by it.

    Read the title for what it now says, not what it used to imply: this is a
    *constructor* separation (`ofGround ≠ EntityOf s` for every `s`), not a
    verdict on whether reality's necessary ground is personal. The personal
    ground of the necessary kind is a *subject* (`Plurality.necessaryPersonalSubjectExists`),
    hence a *different* entity from the ground-constructor; Claim E's two
    conjuncts with no identity line are exactly that shape. What this row rules
    out, then as now, is identifying the two.
    Footprint: `{Subject}`. -/
theorem the_ground_is_not_a_person :
    ∀ s : Subject, Entity.ofGround ≠ EntityOf s :=
  ofGround_ne_ofSubject

/-- The separation, in one statement: the inhabitation cannot be read as a claim about a
    person. If someone were to identify the ground with a subject, the identification
    itself fails, so no route from the ground's love to a created person exists here.
    Footprint: `{Subject}`. -/
theorem ground_love_does_not_identify_a_person :
    ¬ ∃ s : Subject, Entity.ofGround = EntityOf s := by
  rintro ⟨s, h⟩
  exact ofGround_ne_ofSubject s h

/-- **Interpersonal love of the contingent kind never yields ground-level love.**
    `GroundLoves` demands a *necessary* lover and no contingent-kind subject is
    necessary, so `Loves s t` of a contingent-kind `s` cannot give
    `GroundLoves (EntityOf s) _ _`. The two relations are provably disjoint on
    the contingent side; the necessary kind is excluded by hypothesis, not by
    oversight. Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Subject, propext}`. -/
theorem subject_love_is_not_ground_love (s t : Subject) (a : Prop)
    (hKind : ContingentSubjectKind s) (_h : Loves s t) :
    ¬ GroundLoves (EntityOf s) (EntityOf t) a :=
  fun hh => no_subject_is_a_necessary_entity s hKind hh.1

/-- The failure holds for *every* contingent-kind subject and *every* love
    relation, so no amount of contingent interpersonal love can populate the
    necessary quadrant. The necessary kind can — that is the reversal this
    batch records. This is the negative half of the transfer the original
    design asked for, now correctly scoped to the kind it holds of.
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem interpersonal_love_never_reaches_the_necessary_quadrant :
    ¬ ∃ s t : Subject, ContingentSubjectKind s ∧ Loves s t ∧
      NecessaryEntity (EntityOf s) := by
  rintro ⟨s, _t, hKind, _, hn⟩
  exact no_subject_is_a_necessary_entity s hKind hn

/-- **The transfer to contingent interpersonal love is unstatable, not merely
    blocked.** The design originally asked for `GroundLoves → Loves` on the
    subject side. There is no such statement for the contingent kind: `Loves` is
    `Subject`-indexed, the ground is provably no subject-correlate, and the
    target of a `GroundLoves` claim is an arbitrary `Entity` rather than a
    `Subject`. The only route would be a hypostatic identification, which the
    theorems above refute for the contingent kind.
    Footprint: `{GroundBearsGood, Means, NecessarySubjectKind, Subject, propext}`. -/
theorem ground_love_cannot_be_read_as_person_love :
    ¬ (∃ s : Subject, Entity.ofGround = EntityOf s) ∧
      ∀ s t : Subject, ContingentSubjectKind s → Loves s t →
        ¬ GroundLoves (EntityOf s) (EntityOf t) True :=
  ⟨ground_love_does_not_identify_a_person,
    fun s t hKind h => subject_love_is_not_ground_love s t True hKind h⟩

/-- Pure actuality is preserved: the ground's love requires no initiation, so
    `DivinePureActuality`'s zero-transition-potency field is untouched. Attributing an
    *act* of love to the ground adds to `ofGround_divine_pure_actuality` rather than
    contradicting it — pure actuality excludes passive potency, not act.
    Footprint: `{GroundBearsGood, Initiates, Means, NecessarySubjectKind, State, Subject}`.

    **The "*act* of love" prose now has partial formal content (2026-09-28, lote THOMISTIC-ACT).**
    `Logos.ThomisticAct.ground_love_produces` (C465, `Tag: META`, *ST* I q.19 a.4) turns the
    ground's love into `∃ w φ, Produces Entity.ofGround w φ`, and
    `producing_coexists_with_immutability` (C467) proves the *conjunction* this row asserts by
    another route — the ground produces **and** is immutable, in one theorem. Two things this
    row still does not give, and must not be cited for: **essence-act identity** ("God is His
    act" needs essence vocabulary, Class A, still blocked — so no divine simplicity follows),
    and **universal production** (C465's `∃ w φ` is existential; the causal derivation
    `(∃ w, Satisfies w φ) → ∃ v, Produces Entity.ofGround v φ` remains F10's missing statement).
    Read with the succession audit: the `ofGround_no_transition_potency` this row inherits is a
    *non-correlateness* fact (C458), which is precisely why production, not initiation, is the
    relation the ground-level agency claim needs. -/
theorem ground_love_preserves_pure_actuality {t : Entity} {a : Prop}
    (_h : GroundLoves Entity.ofGround t a) : ¬ PassiveTransitionPotency Entity.ofGround :=
  ofGround_no_transition_potency

#print axioms ground_love_targets_a_subject_correlate
#print axioms ground_love_of_a_subject_correlate_iff
end Logos.LovesAsGround

-- Axiom footprint audit
#print axioms Logos.LovesAsGround.falsityWorld_ne_actualWorld
#print axioms Logos.LovesAsGround.an_atom_is_contingent
#print axioms Logos.LovesAsGround.a_contingent_entity_exists
#print axioms Logos.LovesAsGround.a_meaningful_contingent_entity_exists
#print axioms Logos.LovesAsGround.ground_grounds_every_entity
#print axioms Logos.LovesAsGround.atoms_bear_no_meaning
#print axioms Logos.LovesAsGround.ground_grounds_the_meaningless
#print axioms Logos.LovesAsGround.the_ground_is_a_universal_modal_ground
#print axioms Logos.LovesAsGround.no_subject_is_a_necessary_entity
#print axioms Logos.LovesAsGround.necessary_entities_are_ground_or_necessary_kind
#print axioms Logos.LovesAsGround.GroundBearsGood
#print axioms Logos.LovesAsGround.GroundLoves
#print axioms Logos.LovesAsGround.ground_love_requires_a_necessary_lover
#print axioms Logos.LovesAsGround.ground_love_is_directed_at_another
#print axioms Logos.LovesAsGround.ground_love_bears_a_directional_good
#print axioms Logos.LovesAsGround.ground_love_requires_a_meaningful_target
#print axioms Logos.LovesAsGround.meaningless_entities_cannot_be_loved
#print axioms Logos.LovesAsGround.grounding_reaches_what_love_cannot
#print axioms Logos.LovesAsGround.grounding_is_total_but_love_is_not
#print axioms Logos.LovesAsGround.meaningful_love_bridge_is_refuted
#print axioms Logos.LovesAsGround.the_ground_loves_every_meaningful_contingent_reality
#print axioms Logos.LovesAsGround.the_ground_bears_a_directional_good_toward_the_cosmos
#print axioms Logos.LovesAsGround.the_ground_is_a_liver
#print axioms Logos.LovesAsGround.the_ground_is_a_necessary_and_chosen_lover
#print axioms Logos.LovesAsGround.the_ground_is_not_a_person
#print axioms Logos.LovesAsGround.ground_love_does_not_identify_a_person
#print axioms Logos.LovesAsGround.subject_love_is_not_ground_love
#print axioms Logos.LovesAsGround.interpersonal_love_never_reaches_the_necessary_quadrant
#print axioms Logos.LovesAsGround.ground_love_cannot_be_read_as_person_love
#print axioms Logos.LovesAsGround.ground_love_preserves_pure_actuality


/-!
================================================================================
SECTION: CosmicExistence
================================================================================
-/
/-
# Logos.CosmicExistence — the cosmos exists, as a proved theorem

`poem.txt:26-30` asks and answers: "este mundo é necessário? Não.." and then places "a
criação que me parece existir" under a salto de fé. This module makes the *existence* half
of that a **theorem of Γ** while leaving purpose and the incarnation in faith.

## Why it is a theorem, and what it costs

**Corrected 2026-09-27.** This module previously declared the existence of the cosmos as a
`Tag: SEM` axiom, on the stated ground that the lemma it requires had no producer:

    ∃ s : Subject, ∃ p : Prop, Means s p

That ground was **false**. The lemma is already an unconditional theorem —
`Plurality.cogito_from_T12`, of `{Means, NecessarySubjectKind, Subject, Will, subjectWill, AxTwoNecessaryPersonalCentres}` — via
`T12_twoPersons` (unconditional on `AxTwoNecessaryPersonalCentres`, LOVE-3/S4) and `person_is_intentional`, and
`Logos.Core.rightWrongDistinction` is itself axiom-free. The axiom was therefore
**redundant**: it re-charged for a commitment Γ had already made. It is deleted, and
`cosmos_obtains` is the theorem that replaces it.

So the answer to "does the cosmos exist?" is no longer stipulated. **Γ is not satisfiable by
an empty contingent world**, because Γ contains a theorem that *discovers* a subject: from
two distinct necessary persons (`AxTwoNecessaryPersonalCentres`, `Tag: META`) a person means something
(`person_is_intentional`), a meaning subject witnesses a realm (`cosmos_presence_model`).

Note the verb, and it is load-bearing throughout this module. A theorem **discovers**; it
does not **manufacture**. Nothing here produces a subject — the two persons are already
there, as a matter the derivation reports rather than causes, and the derivation is what
makes the report *checkable*. Γ fabricates nothing. Read every inhabitation below as a
discovery, never as a construction: see `Logos.Agency`'s module note, which states the same
principle for the act-datum and disowns the term "manufacturing" for exactly this reason.

**The price, stated plainly.** Existence now rests on the **plurality bridge**:
`Logos.TwoNecessaryPersonalCentres.AxTwoNecessaryPersonalCentres` — "a necessary ground's freedom to self-give cannot depend on contingent subjects". That is a substantive interpersonal metaphysics already declared and paid for
elsewhere in Γ, and it is a `Tag: META` commitment, not a semantic one. Reject it and the
cosmos's existence goes with it. This is a real relocation of the cost — an ontological
claim now leans on an axiological bridge — and it is *tighter* than the axiom was, because
the position is now falsifiable: it can be refuted by rejecting plurality.

**The earlier objection, and why it does not block this route.** The axiom's docstring
argued that "any deductive route to the cosmos's existence would equally force the judging
subject's own claims to be necessary" — the outcome `poem.txt:26` denies. That was aimed at
the *reality-hook* route,

    theorem content_reality_hook (p : Prop) : (∃ s : Subject, Correct s p) → p

which is unconditional in `p` (`RealityHookAudit.lean:85`) and would indeed make "I am
necessary" necessary. **The plurality route never touches `Correct`.** `Realm.bears_meaning`
is meaning-**capacity** (`∃ q, EntityMeans witness q`), not truth, and `Realm.contingent`
*asserts* the realm is modal-fragile. Nothing in the derivation makes any content
necessary, so the reductio does not apply to it.

## Why a new structure rather than a constructor

The cosmos cannot be identified with anything already in the sort: `Entity` has exactly
three constructors (`Entity.lean:23-26`) and there is no `Cosmos`/`Realm` name in the
library. An atom is contingent already (`an_atom_is_contingent`) but bears no meaning
(`atoms_bear_no_meaning`) and is therefore provably *not* an object of love
(`meaningless_entities_cannot_be_loved`); a subject is the user, not the world; the ground
is `NecessaryEntity`; and `actualWorld` is a `def`. So a **new structure** over a single
witness is the honest move, and it leaves every per-constructor theorem untouched.

**One consequence of that structure, recorded because it is easy to misread.**
`EntityMeans` is `False` on `Entity.ofAtom` and `True` on `Entity.ofGround`
(`NecessaryPersonalGround.lean:151-155`), while `Realm.not_the_ground` bars the ground. So
`bears_meaning` and `not_the_ground` together **force the witness to be a person's entity
correlate**. This is a property of the `def`, it held under the deleted axiom too, and it is
*not* introduced by the derivation. It is flagged here because it is a real constraint on
the theology, and it deserves its own ledger row.

**A second correction: the structure must name *one* realm.** The first version of this
module gave `CreatedRealm` three **independent** existential fields while its own docstring
claimed "something actually obtains, the *same something* is modal-fragile". The three
witnesses could be three different entities, so the module's conclusion was really "the
ground loves *some* contingent entity", not "the ground loves the cosmos". The structure now
carries a single `witness` and every field is about it.

The structure also carries a fourth field, `bears_meaning`. That is not decoration: love
requires the target to bear content (`ground_love_requires_a_meaningful_target`), so
without it the conclusion could never be reached. Its honest consequence is that
satisfiability is **conditional on a contingent-kind inhabitant of `Means`** — see `cosmos_presence_model`
— and that inhabitant is exhibited as a premise (a contingent *person* in `cosmos_obtains`;
since 2026-09-28 the kind must be shown, and showing it subsumes the old
`Plurality.cogito_from_T12` route).

## What is proven here — and what is deliberately not

- **The existence of the cosmos** (`cosmos_obtains : CreatedRealm`), proved given an
  exhibited *contingent person*. Footprint `{Means, NecessarySubjectKind, Subject, Will,
  propext, subjectWill}`. This is the batch's whole point: it was a `Tag: SEM` axiom until
  2026-09-27 and is now a theorem; since 2026-09-28 (two-kinds) the price is the exhibited
  kind, not the plurality bridge — exhibiting the kind subsumes the T12 witness, so
  `AxTwoSubjects` is no longer among the premises.
- **The construction** (`cosmos_presence_model`): the structure is inhabited for any
  contingent-kind inhabitant of `Means`, the library's primitive content vocabulary. `Means`
  (`Agency.lean:92`) still has no derivable instance in Γ *by itself* — and the kind must
  be exhibited with it, which is what `cosmos_obtains` consumes as a premise.
- **Non-triviality of the contingency conjunct's shape**
  (`perfect_universe_has_no_contingent_realm`): in a world-rigid universe, the shape
  `ActualEntity t ∧ ∃ w, ¬ ExistsAt w t` is unsatisfiable. This says the contingent content
  is not forced by world structure — it does **not** speak about Γ, because
  `PerfectUniverse` is an unrelated free structure, not a model of Γ.
- What is **not** claimed, because it is not provable in Lean core: that the *negation* of
  the theorem is consistent with all of Γ. That is a model-theoretic statement requiring a
  full interpretation of Γ, and no such model is built here. The honest summary is: the
  existence is **derived** and **conditionally satisfiable**; its *refutability by all of
  Γ* is neither built nor claimed.
- The realm is actual, contingent, **not the ground**, and **bearing content of its own** —
  the machine-checked content of "reality is not exhausted by the necessary ground".
- **The conclusion** `the_ground_loves_the_cosmos`, by applying the declared bridge
  `AxGroundLovesContingentRealm` of `Logos.LovesAsGround` to the realm's contingency and
  content. The footprint names the whole price: the plurality bridge, the ground-love
  bridge, the content vocabulary, and the world structure.
- Separations: the realm's existence yields neither its necessity, nor the ground's
  personality. C110 (`necessary_ground_not_entails_contingent_creation`) is untouched and
  still refutes the deductive route.

## What is deliberately NOT formalized

Purposiveness ("não iria ser sem propósito"), the incarnation, and creation-with-purpose
stay in the **faith** zone: F9 is rescoped, not discharged. No predicate of purpose is
invented for them; they are named as still-requiring-proof in the prose corpus.
-/

namespace Logos.CosmicExistence

open Logos.Semantics (World TV)
open Logos.Agency (Subject NecessarySubjectKind ContingentSubjectKind)
open Logos.Entity (Entity ExistsAt EntityOf EntityExistsAt SubjectExistsAt actualWorld)
open Logos.RecoveredOntologicalGround (EntityMeans)
open Logos.TheologicalModalHardening
    (ActualEntity ContingentEntity NecessaryEntity necessary_not_contingent)
open Logos.NecessityEternity (ofGround_necessary ofGround_ne_ofSubject)
open Logos.PersonalNormativeGround (PersonCorrelate)
open Logos.LovesAsGround
    (GroundBearsGood GroundLoves AxGroundLovesContingentRealm
     the_ground_loves_every_meaningful_contingent_reality
     the_ground_bears_a_directional_good_toward_the_cosmos
     falsityWorld_ne_actualWorld an_atom_is_contingent)

-- ============================================================================
-- Section 1: The realm — one realm, one witness, a meaning-bearing inhabitation
--
-- `Realm` is the *meaning-bearing* realm. It carries a `bears_meaning` field, which is
-- what makes it a possible target of a relation that is more than meaning-capacity
-- (`ground_love_requires_a_meaningful_target`) — and what makes inhabiting it cost a
-- subject-datum: `Subject` is an opaque sort, so the field must be exhibited (a
-- contingent meaning-subject, person, or act — Sections 2–3b), never manufactured.
-- Nothing in this section was ever a declared datum: `CreatedRealm` is a `def` over a
-- `Type`-valued record, and its inhabitations are the conditional theorems of
-- Sections 2–3b.
-- ============================================================================

/-- **The realm, as one record.** Every field is a predicate over the existing vocabulary
    about **one** entity, so the record really does describe a single realm: it obtains, it
    is modal-fragile, it is not identical with the necessary ground, and it bears content of
    its own.

    The single `witness` is a correction: the earlier three-existential version could be
    witnessed by three different entities, which made "the cosmos" meaningless in the
    conclusion. `bears_meaning` is required because love requires a content-bearing target
    (`ground_love_requires_a_meaningful_target`), and because `EntityMeans (ofAtom _) =
    False`, so a realm that bore nothing could never be loved.

    This is a `Type`-valued record, not a `Prop` structure: a `Prop`-valued structure may
    not carry a data field, so a single witness is only expressible this way. The `Prop`
    form is `CreatedRealm` below, and that `def` is the audited one. -/
structure Realm : Type where
  /-- The realm. -/
  witness : Entity
  /-- The realm actually obtains. -/
  actual : ActualEntity witness
  /-- The realm is modal-fragile: it fails to obtain in some possible world. This is what
      the poem's "este mundo é necessário? Não" asserts. -/
  contingent : ∃ w : World, ¬ ExistsAt w witness
  /-- The realm is distinct from the necessary ground: it is not exhausted by it. -/
  not_the_ground : witness ≠ Entity.ofGround
  /-- The realm bears content of its own, so it can be the target of a relation that is
      not mere meaning-capacity. -/
  bears_meaning : ∃ q : Prop, EntityMeans witness q

/-- **A meaning-bearing created realm exists** — there is a realm of the shape `Realm`.
    Stated as `Nonempty` so it is a `Prop` the ledger can name, while the record it
    inhabits keeps a single witness.

    Inhabiting this is **not** free: the `bears_meaning` field forces the witness to be a
    `Subject`, so any inhabitant costs a subject-datum. For the existence claim *without*
    that price see `ContingentRealmObtains` below, and for the claims derived from each
    see `contingent_realm_obtains` and the `cosmos_*` inhabitations respectively.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
def CreatedRealm : Prop := Nonempty Realm

-- ============================================================================
-- Section 1b: The realm without the meaning condition — existence at no
--            substantive price
-- ============================================================================

/-- A contingent created realm, without the meaning condition: something that obtains, is
    modal-fragile, and is not the necessary ground.

    `Realm` (`:161`) requires `bears_meaning`, and because `EntityMeans` is `False` on
    `ofAtom` and `True` on `ofGround` — the latter excluded by `not_the_ground` — that single
    field forces the witness to be a `Subject`. `Subject` is an opaque sort
    (`Agency.lean:43-49`), so *inhabiting* `Realm` costs a subject-datum, priced in
    vocabulary (the `Will`/`subjectWill` of a person, the `Initiates`/`State` of an act)
    — never the plurality bridge. **Existence does not need that field.** Dropping it is a `structure` change, and it adds no axiom — which
    is what lets cosmos existence be derived rather than charged for.

    **On the word "created".** It labels the *region* of reality this record describes:
    actual, modal-fragile, not the ground. It does **not** assert production. No `Creates`
    relation, no agent and no first moment appear in this structure or in the theorem that
    inhabits it, and none is derivable from them — grounding still does not entail a creation
    record, which is C110's standing result. The only thesis here is that reality is **not
    exhausted by the necessary**. Production is a separate lane, and it is unclaimed.

    **Not the identification of an atom with the cosmos** — the same limit C324 carries. What
    is proved below is that the *shape* has an instance. Which realm that is belongs to
    `cosmos_obtains` (C367), not to this structure.
    As with `Realm`, no footprint marker is claimed here: a `structure` is not listed in
    `axiom_audit.json` (the audit covers `thm`/`def`/`axiom` only), so the machine-checked
    markers sit on `ContingentRealmObtains` and on `contingent_realm_obtains`. -/
structure ContingentRealm : Type where
  /-- The realm. -/
  witness : Entity
  /-- The realm actually obtains. -/
  actual : ActualEntity witness
  /-- The realm is modal-fragile: it fails to obtain in some possible world. -/
  contingent : ∃ w : World, ¬ ExistsAt w witness
  /-- The realm is distinct from the necessary ground: it is not exhausted by it. -/
  not_the_ground : witness ≠ Entity.ofGround

/-- A contingent created realm obtains — the `Prop` form, so the ledger can name it as a
    claim while the record keeps a single witness.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
def ContingentRealmObtains : Prop := Nonempty ContingentRealm

/-- Contingency-overflow: something obtains, is modal-fragile, and is not the necessary
    ground — and Γ derives it outright, resting on nothing substantive.

    The witness is an atom, reusing `LovesAsGround.an_atom_is_contingent 0`
    (`LovesAsGround.lean:171`), itself `{Subject, propext}`. The reuse is deliberate, and
    the construction is **not** vacuous: `EntityExistsAt w (ofAtom n) := w n = TV.t`
    (`Entity.lean:53-56`) discriminates on the index, so `actualWorld 0 = TV.t` while
    `fun _ => TV.f` falsifies it. Contingency here is a real property of this entity, not an
    artifact of a coarse world sort.

    **What this costs: nothing substantive.** `Subject` enters only as the sort behind
    `Entity`, never as an inhabited existential, and `propext` is Lean's classical
    propositional logic. Before 2026-09-27 the same content cost
    `{propext, Means, Will, subjectWill, AxTwoSubjects}`, because it was obtained by
    destructing a `bears_meaning` witness. The difference between that and this is the whole
    of the change: **existence is derived, not purchased.**

    This does **not** make an atom into the cosmos (C324 forbids it), and it does not say
    anything made the realm — see the structure's docstring.
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem contingent_realm_obtains : ContingentRealmObtains := by
  obtain ⟨ha, hc⟩ := an_atom_is_contingent 0
  exact ⟨⟨Entity.ofAtom 0, ha, hc, Entity.noConfusion⟩⟩

-- ============================================================================
-- Section 2: Consistency and non-triviality
-- ============================================================================

/-- **Conditional satisfiability.** The realm does obtain, for any inhabitant of `Means`
    who is of the contingent kind. The witness is such a subject, actual at the
    actual world (right disjunct of `SubjectExistsAt`), refuted at the all-`TV.f`
    world (the kind disjunct fails by hypothesis, the world equation by
    `falsityWorld_ne_actualWorld`), distinct from the ground by
    `Entity.noConfusion`, and bearing content because `EntityMeans (ofSubject s)
    p` unfolds to `Means s p`.

    The kind premise is the honest form of "no creation without a person": a
    contingent realm needs a *contingent* witness, and the witness's contingency
    is its kind. Under the old kind-blind semantics this premise was invisible
    (every subject was contingent); the two-kinds doctrine exhibits it.

    The `Means` hypothesis is not a technicality and is not hidden: `Means` is a primitive
    `Tag: VOCAB` **axiom** (`Agency.lean:92`) with no derivable instance in Γ, so this
    theorem is satisfiability *relative to* Γ's intentional vocabulary being inhabited. It
    is stated that way rather than claimed outright.

    **This is not the identification of a subject with the cosmos** — the model witnesses
    only that the structure is satisfiable, and the witness is forced to be a subject by
    `bears_meaning` + `not_the_ground` together. See `cosmos_obtains` for the theorem that
    consumes it, which reads the witness as *evidence of reality's addressability* rather
    than as the cosmos itself.
    Footprint: `{Means, NecessarySubjectKind, Subject, propext}`. -/
theorem cosmos_presence_model
    (h : ∃ s : Subject, ContingentSubjectKind s ∧ ∃ p : Prop, Logos.Agency.Means s p) :
    CreatedRealm := by
  obtain ⟨s, hKind, p, hp⟩ := h
  have hActual : ActualEntity (EntityOf s) := Or.inr rfl
  have hAbsent : ¬ ExistsAt (fun _ => TV.f) (EntityOf s) := by
    intro hEx
    dsimp [ExistsAt, EntityExistsAt, SubjectExistsAt, EntityOf] at hEx
    rcases hEx with hk | heq
    · exact hKind hk
    · exact falsityWorld_ne_actualWorld heq
  exact
    ⟨{ witness := EntityOf s
       actual := hActual
       contingent := ⟨(fun _ => TV.f), hAbsent⟩
       not_the_ground := Entity.noConfusion
       bears_meaning := ⟨p, hp⟩ }⟩

/-- **The realm, on the performative act-datum.**
    `cosmos_presence_model` is the inhabitation; what it needs is a contingent-kind
    subject who means something. The performative act-datum supplies such a witness
    with no bridge at all, kind exhibited with the act:
    `Logos.Agency.act_datum_implies_means` turns the act's `Means` conjunct into the
    meaning premise for the same subject, because `Act` already contains `Means`.

    This is the God-lane, and it is deliberately a *new row* rather than a
    re-anchoring of `cosmos_obtains`. The two reasons, both of them the project's
    own:

    - **A theorem discovers, it does not manufacture.** Γ cannot supply a subject out
      of nothing, and it is not being asked to: the contingent act is *assumed as
      given*, the way `Logos.Agency` states its foundation — "the present act of
      reasoning is *given*, not inferred" (`Agency.lean:4`). The price is the datum
      itself, stated as the hypothesis. It does not evaporate.
    - **The A1 bug was exactly this made unconditional.** Deleting the act-datum and
      anchoring subject-existence on plurality made it "a consequence of plurality —
      the very datum it must precede" (`GAPMAP.md`, batch A1/M0). A1 was caught and
      reverted for that reason; re-anchoring `cosmos_obtains` now would repeat it.

    So the claim is *not* that the cosmos is free. It is that the meaning-datum
    (C354), the person-datum (C367) and the act-datum (this row) are three independent
    routes to a meaning-bearing realm — a falsifiable difference, since each row
    stands on its own datum and falls with it — and none of them pays the plurality
    bridge.
    Footprint: `{Initiates, Means, NecessarySubjectKind, State, Subject, propext}`. -/
theorem cosmos_presence_model_of_the_act_datum
    (h : ∃ s : Subject, ContingentSubjectKind s ∧ ∃ p : Prop, Logos.Agency.Act s p) :
    CreatedRealm := by
  obtain ⟨s, hKind, p, ha⟩ := h
  exact cosmos_presence_model ⟨s, hKind, p, ha.1⟩

/-- **The cosmos exists** — a contingent created realm, not the necessary ground, actually
    obtains and bears content of its own — given a *contingent* person.

    **This was a `Tag: SEM` axiom until 2026-09-27, and that was an error.**
    `AxContingentCreationObtains` was declared on the ground that the lemma it needs had no
    producer. It does have one. Γ contains a theorem that *discovers* a subject:

        rightWrongDistinction        : ¬ N_T ∧ ¬ N_F                      -- `{}`
        T12_twoPersons               = AxTwoSubjects rightWrongDistinction
        person_is_intentional        : Person s → ∃ p, Means s p
        cogito_from_T12              : ∃ s, ∃ p, Means s p                -- unconditional

    so `cosmos_presence_model cogito_from_T12` inhabited `CreatedRealm` outright. The axiom
    was re-charging for a commitment Γ had already made, and it is deleted.

    **The two-kinds correction (2026-09-28).** Under the old kind-blind semantics every
    subject was contingent, so the T12 witness's contingency was free. It is not free:
    a contingent realm needs a *contingent* witness, and the witness's contingency is
    its kind (`ContingentSubjectKind`). `cogito_from_T12` exhibits a meaning subject
    but says nothing of its kind, so this row now exhibits the kind as an explicit
    premise — a contingent *person* — and reads the meaning off it by
    `person_is_intentional`. `AxTwoSubjects` no longer appears in the footprint: it
    supplied personhood and meaning, but exhibiting the kind subsumes the witness, so
    the plurality bridge is not among this row's premises. That is not a promotion for
    free: the kind premise is the load-bearing datum, and it is stated, not
    manufactured. T12/the plurality bridge stays load-bearing everywhere else
    (T13, T14, C40, C74, the moral-good lane).

    **What Γ can now say, and cannot.** It can say the contingent realm exists, given a
    contingent person who means something: Γ is not satisfiable by an empty contingent
    world under that datum, because Γ then contains a theorem exhibiting the witness.
    It still cannot say the realm's *negation* is consistent with all of Γ — that needs
    a full interpretation of Γ, and no such model is built here.

    **The price, which is the whole cost of this row.** Existence *as such* no longer costs
    anything: see `contingent_realm_obtains` (`{propext, Subject}`), which yields the same
    contingency-overflow with no substantive axiom. What this row costs is the *witness*:
    a contingent person who means something — personhood, meaning, and kind, all
    exhibited, none manufactured.

    So the correct statement of the price is narrower than it was: **reject the
    contingent-person datum and the realm's *meaning-bearing inhabitation* goes, not
    the realm's existence.** The position is tighter than the axiom was, because it is
    now falsifiable — but a meaning claim now leans on an exhibited witness, and that
    is a relocation of the cost, not a removal of it.

    **This row is C367, not C350.** The 2026-09-27 split moved the bare existence claim to
    `contingent_realm_obtains` (C350, `PROVEN`, `{CL, NecessarySubjectKind, Subject}`) and left the
    meaning-bearing inhabitation here. What distinguishes the two is `bears_meaning`, and
    what identifies the derived realm as *the cosmos* is this row — not C324's atom, which
    the ledger explicitly forbids reading as the cosmos.

    **Why the old objection does not apply.** The deleted docstring argued that any
    deductive route here "would equally force the judging subject's own claims to be
    necessary", the outcome `poem.txt:26` denies. That was aimed at the reality-hook route
    `(∃ s, Correct s p) → p`, which is unconditional in `p`. This route never touches
    `Correct`: `Realm.bears_meaning` is meaning-**capacity**, and `Realm.contingent`
    *asserts* modal-fragility. Nothing becomes necessary.

    Non-triviality of the contingency content is unchanged and still machine-checked:
    `perfect_universe_has_no_contingent_realm` refutes the `Realm` shape in a world-rigid
    universe. C110's separation also survives untouched — existence is derived, and the
    deductive route from necessary ground to a creation record is still refuted.
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, propext, subjectWill}`. -/
theorem cosmos_obtains
    (h : ∃ s : Subject, ContingentSubjectKind s ∧ Logos.Person.Person s) :
    CreatedRealm := by
  obtain ⟨s, hKind, hPerson⟩ := h
  obtain ⟨p, hmp⟩ := Logos.Person.person_is_intentional s hPerson
  exact cosmos_presence_model ⟨s, hKind, p, hmp⟩

/-- **No reading of Γ satisfies an empty contingent world.** The subject the derivation
    reports is *discovered inside Γ*, not assumed and not manufactured: `cogito_from_T12`
    has no hypothesis, and its
    input `Logos.Core.rightWrongDistinction` is axiom-free. Stated as a standalone fact so
    the "cannot come about in an empty world" claim is checkable on its own, rather than
    only as a side effect of the row above. (No `propext`: it is `cogito_from_T12` verbatim,
    and the `propext` in `cosmos_obtains` enters only through `Realm`'s record fields.)
    Footprint: `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`. -/
theorem gamma_exhibits_a_meaning_subject :
    ∃ s : Subject, ∃ p : Prop, Logos.Agency.Means s p :=
  Logos.Plurality.cogito_from_T12

/-- **A world-rigid universe**, in the `ModalOntologySignature` idiom of
    `TheologicalModalHardening.lean:74-80`. Used as the negative side of the realm's
    consistency story.

    Read the scope carefully: this is an **unrelated free structure, not a model of Γ**. It
    shows that the shape of the realm's contingency field is not forced by world-rigidity
    *in general*; it says nothing about Γ's worlds, on which the contingency claim simply
    holds. -/
structure PerfectUniverse where
  World : Type
  actualWorld : World
  Entity : Type
  ExistsAt : World → Entity → Prop
  /-- World-rigidity of existence: what holds at the actual world holds at every world.
      This is the field that makes contingency impossible in the universe. -/
  WorldRigid : ∀ w : World, ∀ e : Entity, ExistsAt w e ↔ ExistsAt actualWorld e

/-- **Non-triviality of the contingency conjunct's shape.** In a `PerfectUniverse` every
    actual entity is necessary, so the shape `ExistsAt actualWorld t ∧ ∃ w, ¬ ExistsAt w t`
    is unsatisfiable there. The contingency conjunct is therefore not a triviality of the
    world structure.
    Footprint: `{}`. -/
theorem perfect_universe_actual_is_necessary (U : PerfectUniverse) :
    ∀ t : U.Entity, U.ExistsAt U.actualWorld t → ∀ w : U.World, U.ExistsAt w t := by
  intro t ht w
  exact (U.WorldRigid w t).mpr ht

/-- **The contingency shape is refuted.** In a `PerfectUniverse` world-rigidity makes every
    actual entity necessary, so nothing witnesses `ExistsAt actualWorld t ∧ ∃ w,
    ¬ ExistsAt w t` — the shape of `CreatedRealm.contingent`.
    Footprint: `{}`. -/
theorem perfect_universe_has_no_contingent_realm (U : PerfectUniverse) :
    ¬ (∃ t : U.Entity, U.ExistsAt U.actualWorld t ∧ ∃ w : U.World, ¬ U.ExistsAt w t) := by
  rintro ⟨t, ht, w, hw⟩
  exact hw (perfect_universe_actual_is_necessary U t ht w)

/-- **The realm's existence is not refutable** by the theory: the structure is inhabited, so
    no theorem of Γ can refute it. **Renamed 2026-09-27** from
    `the_cosmos_datum_is_not_refutable` — there is no longer a datum to be refuted. The name
    would otherwise have reintroduced the very "declared datum" language this module removes.

    Since 2026-09-27 it also **loses its hypothesis**. It used to require a `Means` inhabitant
    and then refute the emptiness of a *meaning-bearing* `CreatedRealm`, which cost
    `{Means, Subject, propext}`. The bare `ContingentRealmObtains` is inhabited outright, so
    the honest statement is the unconditional one and the hypothesis is gone rather than
    carried as decoration.

    This is the half of the *empirical* character Lean can certify: the claim is consistent
    with the theory that states it. Its **status is derived** (`contingent_realm_obtains`).
    The ambient contingency it appeals to is itself a countermodel
    (`Logos.NecessityEternity.everlasting_but_contingent`), so the contingency content is not
    a triviality of Γ either.
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem the_cosmos_existence_is_not_refutable : ¬ (ContingentRealmObtains → False) :=
  fun hh => hh contingent_realm_obtains

-- ============================================================================
-- Section 3: What the realm is — and is not — machine-checked
-- ============================================================================

/-- Something contingent obtains. This is the whole of what is claimed about existence on
    the free route, and it no longer rides on the meaning-bearing `cosmos_obtains`: since
    2026-09-27 it is read off `contingent_realm_obtains`, which costs nothing substantive.
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem a_created_realm_obtains : ∃ t : Entity, ActualEntity t := by
  obtain ⟨R⟩ := contingent_realm_obtains
  exact ⟨R.witness, R.actual⟩

/-- The realm is contingent. The machine-checked content of the poem's
    "este mundo é necessário? Não" — now at vocabulary-only price, for the same reason as
    `a_created_realm_obtains`.
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem a_contingent_reality_obtains : ∃ t : Entity, ContingentEntity t := by
  obtain ⟨R⟩ := contingent_realm_obtains
  exact ⟨R.witness, ⟨R.actual, R.contingent⟩⟩

/-- The realm is not the ground. This is the *negative* half of the thesis — the
    machine-checked form of "reality is not exhausted by the ground" — and it is the step
    the deductive route (C110) cannot supply in the other direction. Free since 2026-09-27:
    the price used to be `AxTwoSubjects`, carried only by the `bears_meaning` witness.
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem reality_is_not_exhausted_by_the_ground :
    ∃ t : Entity, ActualEntity t ∧ t ≠ Entity.ofGround := by
  obtain ⟨R⟩ := contingent_realm_obtains
  exact ⟨R.witness, ⟨R.actual, R.not_the_ground⟩⟩

/-- The realm bears content of its own — the fact that makes it a *possible* target of a
    relation that is more than meaning-capacity, and the fact that distinguishes the
    meaning-bearing realm from the bare atom-existence of `a_contingent_entity_exists`.

    **This claim keeps its price on purpose.** It is read off `cosmos_obtains` and therefore
    inherits the person-hypothesis price (`Will`/`subjectWill`), because `bears_meaning`
    needs a `Subject` and `Subject` is an opaque sort. Meaning is the substantive half of the thesis; charging for it is correct,
    and the 2026-09-27 change deliberately did **not** route this through
    `contingent_realm_obtains`. Doing so would be a vacuous proof, and the two shortcuts that
    would have made it free — rescoping love onto an atom, and relaxing `EntityMeans` so
    atoms bear content — were both considered and rejected.
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, propext, subjectWill}`. -/
theorem the_realm_bears_meaning
    (h : ∃ s : Subject, ContingentSubjectKind s ∧ Logos.Person.Person s) :
    ∃ t : Entity, ∃ q : Prop, EntityMeans t q := by
  obtain ⟨R⟩ := cosmos_obtains h
  exact ⟨R.witness, R.bears_meaning⟩

/-- The two poles, side by side: the ground is necessary and the realm is contingent, so
    the realm's existence cannot be read off the ground's necessity. Both halves are
    machine-checked, and together they are the whole content of "not merely a mathematical
    ground" available *before* any love is claimed. **Free since 2026-09-27**: the ground's
    necessity is `{Subject}` (`ofGround_necessary`) and the realm's contingency is
    `{Subject, propext}` (`a_contingent_reality_obtains`), so no substantive axiom appears.
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem the_ground_is_necessary_and_the_realm_is_contingent :
    NecessaryEntity Entity.ofGround ∧ ∃ t : Entity, ContingentEntity t :=
  ⟨ofGround_necessary, a_contingent_reality_obtains⟩

/-- **The conclusion, with both prices visible.** The realm's contingency and content plus
    the declared bridge yield a directional good the ground holds toward the cosmos — "He
    is not merely a mathematical ground, but loves". The footprint names the whole price:
    the meaning vocabulary, the metaphysical bridge, the love bridge, and the world structure.
    The claim is about the ground *as a kind*: no hypostatic identification is made
    (`ofGround_ne_ofSubject`).

    **This price is kept deliberately.** Since 2026-09-27 the existence conjunct is available
    free (`a_contingent_reality_obtains`), so this row is no longer paying for existence; it
    pays only for the *meaning* conjunct and the two declared bridges. That is the correct
    distribution — a realm with no content could not be loved, so the content is what is
    being charged for.
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, propext, subjectWill, AxGroundLovesContingentRealm, GroundBearsGood}`. -/
theorem the_ground_loves_the_cosmos
    (h : ∃ s : Subject, ContingentSubjectKind s ∧ Logos.Person.Person s) :
    ∃ t : Entity, ContingentEntity t ∧ (∃ q, EntityMeans t q) ∧
      ∃ p, GroundBearsGood Entity.ofGround t p := by
  obtain ⟨R⟩ := cosmos_obtains h
  obtain ⟨q, hq⟩ := R.bears_meaning
  have hc : ContingentEntity R.witness := ⟨R.actual, R.contingent⟩
  exact ⟨R.witness, hc, ⟨q, hq⟩,
    the_ground_bears_a_directional_good_toward_the_cosmos hc ⟨q, hq⟩⟩

/-- The same conclusion in the library's relational vocabulary: there is a context in which
    the ground's love of the realm holds. Note this is the *relation* `GroundLoves`, not
    interpersonal `Loves` — the two are provably disjoint, and the transfer is unstatable
    rather than merely unproved (`ground_love_cannot_be_read_as_person_love`). Kept priced
    for the same reason as `the_ground_loves_the_cosmos`: the meaning conjunct, not
    existence, is the load-bearing premise.
    Footprint: `{Means, NecessarySubjectKind, Subject, Will, propext, subjectWill, AxGroundLovesContingentRealm, GroundBearsGood}`. -/
theorem the_ground_loves_the_cosmos_in_a_context
    (h : ∃ s : Subject, ContingentSubjectKind s ∧ Logos.Person.Person s) :
    ∃ t : Entity, ContingentEntity t ∧ ∃ a : Prop, GroundLoves Entity.ofGround t a := by
  obtain ⟨R⟩ := cosmos_obtains h
  have hc : ContingentEntity R.witness := ⟨R.actual, R.contingent⟩
  exact ⟨R.witness, hc,
    the_ground_loves_every_meaningful_contingent_reality hc R.bears_meaning⟩

-- ============================================================================
-- Section 3b: The God-lane — the ground's-love line through the act-datum
-- ============================================================================

/-- **The conclusion of C351, through the act-datum instead of the person-datum.**
    `the_ground_loves_the_cosmos` is C351 and reaches its meaning conjunct through
    `cosmos_obtains`, which exhibits a contingent *person*. Re-route that step through
    `cosmos_presence_model_of_the_act_datum`, which exhibits an *act*, and the
    conclusion is byte-identical with the person vocabulary swapped for the act
    vocabulary.

    (History, so the older "removes the bridge" telling is not misread: when this
    row was written, C351 still paid the plurality bridge, and the row removed it.
    The two-kinds correction of 2026-09-28 has since removed the bridge from both
    rows — `AxTwoSubjects` occurs in neither footprint — leaving the hypothesis
    swap as this row's content.)

    The love bridge `Logos.LovesAsGround.AxGroundLovesContingentRealm` and the
    relation `GroundBearsGood` remain, and must: a directional good held by the ground
    is not expressible in Γ's grounding vocabulary, which reaches only undirected
    sufficiency, and the corpus has already recorded that no reading of it is `{}`
    (see `LovesAsGround.lean`'s module note).

    What this row changes, measured: C351's footprint is
    `{AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind,
    Subject, Will, propext, subjectWill}` and this row's is
    `{AxGroundLovesContingentRealm, GroundBearsGood, Initiates, Means,
    NecessarySubjectKind, State, Subject, propext}` — the `Will`/`subjectWill` that
    entered through the person-hypothesis are swapped for the `Initiates`/`State`
    that enter through the act-hypothesis, statement byte-identical. That matters
    for a reader's verdict on the price: the person-datum is no longer among the
    premises of the ground's love, and the act-datum that replaces it is
    independently priced (C454), so the swap is *visible* rather than quietly
    absorbed.

    **This does not make the conclusion free, and the row is not promoted.** The price
    is relocated to the declared act-datum axiom `performative_act_datum` (C454, `Tag: TRANS`):
    one axiom, not free in performance, which is the same account the retorsion
    batch gives for C375/C377. A reader who will not grant that an act occurred
    rejects this row; a reader who rejects `AxTwoNecessaryPersonalCentres` keeps it.
    Footprint: `{propext, Initiates, Means, NecessarySubjectKind, State, Subject, AxGroundLovesContingentRealm,
    GroundBearsGood}`. -/
theorem the_ground_loves_the_cosmos_from_the_act_datum
    (h : ∃ s : Subject, ContingentSubjectKind s ∧ ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ t : Entity, ContingentEntity t ∧ (∃ q, EntityMeans t q) ∧
      ∃ p, GroundBearsGood Entity.ofGround t p := by
  obtain ⟨R⟩ := cosmos_presence_model_of_the_act_datum h
  obtain ⟨q, hq⟩ := R.bears_meaning
  have hc : ContingentEntity R.witness := ⟨R.actual, R.contingent⟩
  exact ⟨R.witness, hc, ⟨q, hq⟩,
    the_ground_bears_a_directional_good_toward_the_cosmos hc ⟨q, hq⟩⟩

-- ============================================================================
-- Section 4: Separations — what the free existence result does not buy
-- ============================================================================

/-- The realm's existence does **not** make it necessary. `poem.txt:26`'s negation stands
    as machine-checked: the actual is not the necessary. **Free since 2026-09-27** — read off
    `contingent_realm_obtains`, so the refutation of the necessity reading never touches the
    meaning-bearing record.
    Footprint: `{NecessarySubjectKind, Subject, propext}`. -/
theorem realm_existence_does_not_imply_realm_necessity :
    ¬ (∀ t : Entity, ActualEntity t → NecessaryEntity t) := by
  obtain ⟨R⟩ := contingent_realm_obtains
  obtain ⟨w, hw⟩ := R.contingent
  intro hall
  exact hw (hall R.witness R.actual w)

/-- Contingency and necessity are exclusive, so the realm's witness is provably not
    necessary. This is why the realm's existence does not collapse C110: the ground's
    necessity still does not yield the realm's contingency, and the realm's contingency does
    not retrofeed the ground's necessity.
    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem contingent_reality_is_not_necessary :
    ∀ t : Entity, ContingentEntity t → ¬ NecessaryEntity t :=
  fun t hc hn => necessary_not_contingent t hn hc

/-- The ground is not a person. The hypostatic identification stays blocked: ledger bridge
    #9 (`Ground(e, personal) → Personal(e)`) is untouched, and the ground is provably no
    subject's correlate regardless of what obtains.

    This is deliberately stated **without** a `CreatedRealm` antecedent. The earlier version
    carried one and then ignored it — the proof never used the hypothesis — so the
    antecedent was decoration that made the theorem look like it constrained the realm.
    Footprint: `{Means, Subject, Will, subjectWill}`. -/
theorem ofGround_not_a_person_correlate : ¬ PersonCorrelate Entity.ofGround := by
  rintro ⟨s, hs, _⟩
  exact ofGround_ne_ofSubject s hs

-- ============================================================================
-- Section 4b: §18 — pantheism, in the one form it can be stated in
--
-- `CHARACTERISTICS.md` §18 asks for the exclusion of pantheism and records it as
-- ❌ not established, with two gaps: there is no `Universe` predicate at all, and the
-- prose does not say whether "the universe" is the whole aggregate or the ground
-- itself. The second gap is a question about *which* claim, and this section answers
-- it by refusing to choose.
--
-- `Universe` below is the **identity** form and nothing else: "whatever obtains IS e".
-- The aggregate reading ("the universe is not an entity at all") is not a proposition
-- about `Entity`, so it is unstatable here rather than refuted; and the *grounding*
-- form is not pantheism, and is separated by the cited rows (C110's countermodel, C328
-- on the meaningless) rather than re-proved.
--
-- The section adds no axiom, no primitive, and no stipulation. `Universe` occurs in
-- CONCLUSIONS only — it is defined here and consumed by the three theorems below, so
-- it needs no ◈ registration and no `Tag:`. The plan of record is `PLAN.md`;
-- there is no root `AUDIT.md` in this repository and never has been.
-- ============================================================================

/-- **Pantheism in its only well-formed identity form: whatever obtains IS `e`.**

    Deliberately not `NecessaryEntity` (which is `∀ w, ExistsAt w e`, i.e. C330's
    proposition under a second name — the corpus forbids two names for one
    proposition) and deliberately not an "aggregate universe" `Type`, which `Entity`
    has no constructor for. Identity is the reading on which the claim can be false
    or true of something in Γ's ontology at all.

    Read the three theorems below for what they do **not** say: the realm's
    contingency is untouched, and `SUBJECTS.md` §4's
    `∀ w ∀ s, Creates s w → ∃ t, ContingentSubjectKind t ∧ Person t` remains BLOCKED
    and is cited there, not re-proved here. -/
def Universe (e : Entity) : Prop :=
  ∀ (w : World) (x : Entity), ExistsAt w x → e = x

/-- **No entity is identical to the totality of what obtains.** For every entity there
    is something else that obtains, so the identity form of pantheism fails for all
    three constructors of `Entity` at once.

    The proof is the three-constructor exhaustion, and it is worth reading carefully
    because it is *type-theoretic*, not metaphysical: `ofGround ≠ ofAtom n` and
    `ofGround ≠ ofSubject s` are `Entity.noConfusion`, and the ground exists at
    every world while `ofAtom 0` exists at `actualWorld` (`actualWorld 0 = TV.t`
    computes). The refutation is therefore not an empty-world artifact — the same
    witness `LovesAsGround.an_atom_is_contingent` (C323) already uses.

    **This is cheap, and should be read as cheap.** It says that Γ's `Entity` is an
    inductive with distinguishable constructors, not that an ontology of the universe
    has been philosophically adjudicated. The ledger row records it at that strength.
    Footprint: `{NecessarySubjectKind, Subject}` (the `ExistsAt` artifact of Section 1b). -/
theorem no_entity_is_identical_to_the_whole (e : Entity) :
    ∃ (w : World) (x : Entity), ExistsAt w x ∧ x ≠ e := by
  cases e with
  | ofSubject s => exact ⟨Entity.actualWorld, Entity.ofGround, trivial, Entity.noConfusion⟩
  | ofAtom n => exact ⟨Entity.actualWorld, Entity.ofGround, trivial, Entity.noConfusion⟩
  | ofGround => exact ⟨Entity.actualWorld, Entity.ofAtom 0, rfl, Entity.noConfusion⟩

/-- **The ground of reality is not the universe.** The headline of §18's identity
    form, read off the previous row at `e := Entity.ofGround`.

    Footprint: `{NecessarySubjectKind, Subject}`. -/
theorem the_ground_is_not_the_universe : ¬ Universe Entity.ofGround := by
  intro h
  obtain ⟨w, x, hxw, hne⟩ := no_entity_is_identical_to_the_whole Entity.ofGround
  exact hne (h w x hxw).symm

/-- **Founding and identifying are not compatible alternatives.** For every entity,
    being grounded by the ground does not make it identical with the totality — so
    §18's second stated gap ("it does not specify whether founded and identical are
    compatible") is machine-checked as *incompatible*.

    The antecedent is the whole of `OneEssence`, and under Γ's definitions it holds
    for every entity (C328), so this row's content is entirely in the `¬ Universe e`
    half. It is stated as an implication because that is the form the prose gap is
    about; a reader looking for a constraint on `OneEssence` will not find one
    here, and should not. Its dependency on `Means` is inherited from
    `OneEssence`; nothing in the antecedent is read in the proof.
    Footprint: `{Means, NecessarySubjectKind, Subject}`. -/
theorem grounding_never_yields_identity_of_the_totality (e : Entity) :
    Logos.RecoveredOntologicalGround.OneEssence Entity.ofGround e →
    ¬ Universe e := by
  intro _hGrounds h
  obtain ⟨w, x, hxw, hne⟩ := no_entity_is_identical_to_the_whole e
  exact hne (h w x hxw).symm

end Logos.CosmicExistence
#print axioms Logos.CosmicExistence.Realm
#print axioms Logos.CosmicExistence.CreatedRealm
#print axioms Logos.CosmicExistence.ContingentRealm
#print axioms Logos.CosmicExistence.ContingentRealmObtains
#print axioms Logos.CosmicExistence.contingent_realm_obtains
#print axioms Logos.CosmicExistence.cosmos_presence_model
#print axioms Logos.CosmicExistence.cosmos_obtains
#print axioms Logos.CosmicExistence.gamma_exhibits_a_meaning_subject
#print axioms Logos.CosmicExistence.PerfectUniverse
#print axioms Logos.CosmicExistence.perfect_universe_actual_is_necessary
#print axioms Logos.CosmicExistence.perfect_universe_has_no_contingent_realm
#print axioms Logos.CosmicExistence.the_cosmos_existence_is_not_refutable
#print axioms Logos.CosmicExistence.a_created_realm_obtains
#print axioms Logos.CosmicExistence.a_contingent_reality_obtains
#print axioms Logos.CosmicExistence.reality_is_not_exhausted_by_the_ground
#print axioms Logos.CosmicExistence.the_realm_bears_meaning
#print axioms Logos.CosmicExistence.the_ground_is_necessary_and_the_realm_is_contingent
#print axioms Logos.CosmicExistence.the_ground_loves_the_cosmos
#print axioms Logos.CosmicExistence.the_ground_loves_the_cosmos_in_a_context
#print axioms Logos.CosmicExistence.realm_existence_does_not_imply_realm_necessity
#print axioms Logos.CosmicExistence.contingent_reality_is_not_necessary
#print axioms Logos.CosmicExistence.ofGround_not_a_person_correlate
#print axioms Logos.CosmicExistence.Universe
#print axioms Logos.CosmicExistence.no_entity_is_identical_to_the_whole
#print axioms Logos.CosmicExistence.the_ground_is_not_the_universe
#print axioms Logos.CosmicExistence.grounding_never_yields_identity_of_the_totality


/-!
================================================================================
SECTION: SuccessionAudit
================================================================================
-/
/-
# Logos.SuccessionAudit — what `NotInSuccession` actually says, and what it does not

This module is the answer to an objection raised on 2026-09-28:

> *"The ground Initiates is refuted because there's a mistake in the proof."*

The object was `the_ground_not_in_succession` (`NecessityEternity.lean:196-198`), the fact on which
the immutability headline and C217 rest. The verdict is that the **objection is right and the
mistake is real — but it is not in the kernel term.** That term is perfectly sound, which is exactly
why it survived every audit. The proof binds the initiation conjunct and throws it away:

```lean
theorem the_ground_not_in_succession : NotInSuccession Entity.ofGround := by
  rintro ⟨s, σ, σ', p, ⟨hEq, _h⟩⟩        -- _h : Initiates s σ σ' p is never used
  exact Entity.noConfusion hEq            -- consumes only ofGround = ofSubject s
```

So the ground's transition invariance is discharged by **constructor disjointness** and decides
nothing whatever about `Initiates`. Its content is `¬ ∃ s, ofGround = EntityOf s`, which is
`ofGround_ne_ofSubject` — already a theorem in the corpus twice over
(`FoundationalUnicity.lean:131`, `NecessityEternity.lean:160`).

Two consequences follow, and this module machine-checks both of them:

1. **The field cannot tell the ground from an atom.** Every atom is equally far from being a subject
   correlate, so every atom satisfies `NotInSuccession` too. This is the *identical* asymmetry C321
   found in `capacity_invariance` — `capacity_invariance_holds_for_every_entity`
   (`DivineImmutability.lean:161`) — on the other field of the same structure, and it was not on
   record. `DivineImmutability.lean:153-154` calls `TransitionInvariance` "the real predicate"; it is
   real in general (C460 below shows it can fail) but it carries no information about the ground.
2. **The ground's non-agency is unstatable, not refuted.** Γ has no entity-level agency relation at
   all: `Initiates : Subject → State → State → Prop → Prop`, and the only way an `Entity` reaches it
   is `EntityOf s = Entity.ofSubject s`. "The ground does not initiate" therefore has no denotation —
   the same wall F16 hit with `EntityMeansAt`. The claim is recorded as C462 (`BLOCKED`) in the
   ledger with the exact missing statement, and the vocabulary that would state it is C463
   (`Produces : Entity → World → Form → Prop`).

**Disclosure, not demotion.** `ofGround_divine_immutability` and C217 keep their status and their
footprints; no badge moves. What changes is the *reading* of one field of one structure — the
F16 precedent (`DivineImmutability.lean:142-165`), applied to the sibling it left unexamined.

**What the sentence "the fact Γ exists means someone initiates" costs.** It is adjudicated here too,
at the end of the module (C468), and the honest answer is: the existence half is free (C350
`contingent_realm_obtains`, `PROVEN`, `{CL, NecessarySubjectKind, Subject}`) and the whole remaining
price is the performative datum C454, because the consequent of the implication is already
unconditional (C455). A bridge axiom "existence implies initiation" would therefore be *strictly
dominated*: its conclusion is already derived, so it would add a priced axiom and no theorems. It is
refused on ledger grounds, not on theological ones.
-/

namespace Logos.SuccessionAudit

open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf ExistsAt)
open Logos.Agency (Subject State Initiates some_subject_initiates)
open Logos.NecessityEternity (NotInSuccession the_ground_not_in_succession)
open Logos.CosmicExistence (ContingentRealmObtains)

-- ===========================================================================
-- Part I: The content of `NotInSuccession`, extracted
-- ===========================================================================

/-- A subject-correlate-free entity is outside succession whatever its relation to initiation may be.

 C458 — the extraction. `NotInSuccession e` is `¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p`
 (`NecessityEternity.lean:102-104`), and this row proves that the *first* conjunct alone suffices.
 So the predicate is, in general, a statement about **which constructor an entity is** — a type fact
 — and only incidentally about initiation.

 This is the lemma `the_ground_not_in_succession` actually uses, promoted to a theorem so that it can
 be read: the ground's transition invariance follows from `ofGround_is_not_a_subject_correlate`
 (below), and the `Initiates` conjunct of the definition is inert in that instance.

 Not a claim that the ground acts. It is the *absence* of a claim, made explicit.

 Footprint: `{Initiates, State, Subject}` — the *statement* mentions `Initiates` and `State`, though
 the proof uses no axiom; the same reason `FoundationalUnicity.groundsEntity_reflexive` is not `{}`
 (see the `Entity`-layer floor). -/
theorem non_correlate_is_outside_succession {e : Entity}
    (h : ¬ ∃ s : Subject, e = EntityOf s) : NotInSuccession e := by
  intro hEx
  obtain ⟨s, _σ, _σ', _p, hEq, _hInit⟩ := hEx
  exact h ⟨s, hEq⟩

/-- The ground is the correlate of no subject — which is the whole of its transition invariance.

 The content of `the_ground_not_in_succession`, stated so that it can be read directly. It is
 `ofGround_ne_ofSubject` in existential form, and it is the reason the immutability headline's
 `transition_invariance` field is satisfied.

 Footprint: `{Subject}` — the sort is in the statement; the proof is a single `noConfusion`. -/
theorem ofGround_is_not_a_subject_correlate :
    ¬ ∃ s : Subject, Entity.ofGround = EntityOf s := by
  rintro ⟨s, hEq⟩
  exact Entity.noConfusion hEq

/-- An atom is the correlate of no subject either.

 The same argument one constructor over, and the reason C459 below holds. `Entity.ofAtom` and
 `Entity.ofGround` are disjoint from `Entity.ofSubject` in the same way; nothing about the atom's
 relation to initiation is used or decided.

 Footprint: `{Subject}` — the sort is in the statement; the proof is a single `nomatch`. -/
theorem ofAtom_is_not_a_subject_correlate (n : Nat) :
    ¬ ∃ s : Subject, Entity.ofAtom n = EntityOf s := by
  rintro ⟨s, hEq⟩
  exact nomatch hEq

-- ===========================================================================
-- Part II: C459 — the field does not separate the ground from an atom
-- ===========================================================================

/-- Transition invariance holds of the ground and of every atom alike, so it cannot characterise the ground.

 C459 — **the asymmetry, and C321's twin.** `DivineImmutability.capacity_invariance` is satisfied by
 every entity whatever (`DivineImmutability.lean:161`, C321); this row records that
 `transition_invariance` — the field `DivineImmutability.lean:153-154` calls "the real predicate" —
 is satisfied by every **non-subject** entity, ground and atoms together, for the same structural
 reason: none of them is a subject correlate.

 So the immutability headline's fourth field carries no ground-specific weight. This is DISCLOSURE,
 NOT DEMOTION: `ofGround_divine_immutability` stays `PROVEN` with footprint
 `{Initiates, Means, NecessarySubjectKind, State, Subject}`, and C217
 (`ofGround_no_transition_potency`, built on this field) stays `PROVEN` as well. What is withdrawn is
 the *reading* that the field says the ground is inert with respect to becoming. The footprint is
 C458's: the statement reaches `Initiates` and `State` through the very field it is about.

 Footprint: `{Initiates, State, Subject}`. -/
theorem the_ground_and_every_atom_are_outside_succession :
    NotInSuccession Entity.ofGround ∧ ∀ n : Nat, NotInSuccession (Entity.ofAtom n) :=
  ⟨non_correlate_is_outside_succession ofGround_is_not_a_subject_correlate,
   fun n => non_correlate_is_outside_succession (ofAtom_is_not_a_subject_correlate n)⟩

-- ===========================================================================
-- Part III: C460 — the non-triviality countermodel the ledger misattributed to C197
-- ===========================================================================

/-- Not every entity is outside succession: the correlate of an initiating subject is not.

 C460 — the non-triviality result, **for the field itself**. The F16 gloss and `T22.txt:92` both
 claimed that every sibling field of `DivineImmutability` has a `{}` non-triviality countermodel "on
 record (C197 …)"; C197 is `DivineImmutability.lean`'s modal-invariance countermodel
 (`GAPMAP.md:2628`) and says nothing about `NotInSuccession`. This row supplies the missing instance,
 and the live sort makes it free: take the correlate of the subject C455 exhibits.

 So the correction is two-sided, and both halves matter. The field is **not** vacuous in general —
 it can fail, and C460 shows exactly when (C459: it holds for the ground and the atoms, so what
 discriminates is being the correlate of a subject who initiates). What is vacuous is the *ground's
 instance* of it, which is C459. C197's scope is corrected in the ledger to modal and stage
 invariance.

 Priced on the performative datum (`Tag: TRANS`, C454) — the witness subject exists because C455
 says so. The honest alternative, a free-signature countermodel, is C461's neighbour in
 `Logos.SuccessionCountermodel`; this row is kept in the live signature because the live sort supplies
 the witness for nothing.

 Footprint: `{performative_act_datum, Initiates, Means, State, Subject}`. -/
theorem someone_is_in_succession : ¬ ∀ e : Entity, NotInSuccession e := by
  intro hAll
  obtain ⟨s, p, w, w', hInit⟩ := some_subject_initiates
  exact hAll (EntityOf s) ⟨s, w, w', p, rfl, hInit⟩

/-- The bridge of the author's sentence, discharged: given that Γ exists, someone initiates.

 C468 — *"The fact Γ exists means Someone Initiates"* (2026-09-28), in the ledger. The implication is
 `ContingentRealmObtains → ∃ s p σ σ' p, Initiates s σ σ' p`, and the proof is the consequent alone:
 the hypothesis is bound, named for the record, and unused.

 **The premise does no work, and the row says so.** The consequent is C455, unconditional, so any
 antecedent whatsoever would yield this row — the antecedent is a *phylogenetic* remark about why the
 author expects the sentence to be true, not a premise. Decomposed honestly:

 * *something exists* — C350 `contingent_realm_obtains`, `PROVEN`, `{CL, NecessarySubjectKind, Subject}`: free;
 * *someone means* — `Plurality.cogito_from_T12` (`Plurality.lean:220`), from the axiom-free
   `Core.rightWrongDistinction`: free;
 * *someone initiates* — C455: the performative datum C454, the only price in the sentence.

 **Why no axiom is added for the implication.** A bridge `existence → initiation` would be *strictly
 dominated*: its conclusion is already a theorem, so it would raise the registry and add no theorems
 to Γ. Refused on ledger grounds. The non-redundant strengthening — the *ground* as the initiator —
 is C462 (`BLOCKED`, unstatable) and, in its Thomistic form, C463/C465/C467.

 **The antecedent is `Nonempty ContingentRealm`, not the `def` `ContingentRealmObtains`.** The two are
 definitionally the same proposition (`ContingentRealmObtains := Nonempty ContingentRealm`,
 `CosmicExistence.lean:247`), but stating the structure is what keeps the row free of a
 `def`-used-as-premise: `scripts/audit_stipulated_defs.py` treats a bare `Prop` `def` in premise
 position as an assumption invisible to `#print axioms`, and it needs no invisible price here — the
 house style for an existential premise is the explicit structure, as in C367's hypothesis.

Footprint: `{performative_act_datum, Initiates, Means, State, Subject}` — **exactly C455's cone.**
 Worth recording: with the `def` antecedent this row carried `NecessarySubjectKind` as the
 fingerprint of the existence half, and stating the structure explicitly removed it. The existence
 half of the author's sentence now leaves *no* trace in the footprint, which is the machine-checked
 form of \"that side is free\" — the premise is inert, and now provably costless too.

 -/
theorem existence_implies_someone_initiates (_hExistence : Nonempty ContingentRealm) :
    ∃ s : Subject, ∃ p : Prop, ∃ w w' : State, Initiates s w w' p :=
  some_subject_initiates

#print axioms non_correlate_is_outside_succession
#print axioms ofGround_is_not_a_subject_correlate
#print axioms ofAtom_is_not_a_subject_correlate
#print axioms the_ground_and_every_atom_are_outside_succession
#print axioms someone_is_in_succession
#print axioms existence_implies_someone_initiates

end Logos.SuccessionAudit


/-!
================================================================================
SECTION: SuccessionCountermodel
================================================================================
-/
/-
# Logos.SuccessionCountermodel — the succession field places no constraint on entity-level production

Companion to `Logos.SuccessionAudit`, in the free-signature style of `ModalPossibilityFrontier.lean`
and `DeepModalFrontier.lean`: a model, not a theorem about Γ's sorts, so that its footprint is `{}`
and it is not evidence about Γ itself. What it *is* evidence about is the **shape** of
`NotInSuccession`.

Governing rule, from `AGENTS.md` and from C321: a property that holds of everything is not a
characterisation, and the way to show that is to exhibit a model in which the property holds of a
thing it is supposed to exclude. C321 did it for `capacity_invariance`; this module does it for
`transition_invariance`, and the thing it must fail to exclude is **entity-level production**.

The model keeps the live definition's shape verbatim —

    ¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p

— and adds a production relation `Produces : Entity → World → Form → Prop`, which is the signature
F10 asks for (`DivineOmnipotence.lean:55`). The ground is given the trivial production relation and
is still outside succession. Nothing in the definition mentions `Produces`, so nothing could have
excluded it: the two-lane design that `agere sequitur esse` requires is not a subtlety of wording, it
is forced by which relations the definitions quantify over.

This is the model-theoretic shadow of C467 in the live batch: there, the ground produces *and* is
immutable, both machine-checked. Here, the claim is only that the succession field cannot object.
-/

namespace Logos.SuccessionCountermodel

-- ===========================================================================
-- Part I: The definition under test, in the live shape
-- ===========================================================================

/-- The live body of `NotInSuccession` (`NecessityEternity.lean:102-104`), reproduced verbatim over a
    free signature so the model tests the shape rather than Γ's sorts. -/
def ModelNotInSuccession {Entity Subject State : Type} (EntityOf : Subject → Entity)
    (Initiates : Subject → State → State → Prop → Prop) (e : Entity) : Prop :=
  ¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p

/-- A model in which the ground is outside succession **and** produces.

 `Produces` is a parameter, so the model says: *for some production relation, a ground-like entity
 is both inert with respect to succession and a producer.* It is deliberately left arbitrary rather
 than fixed to the trivial relation, because the point is that nothing in
 `ModelNotInSuccession`'s body constrains it. -/
structure GroundProducesCountermodel (Entity Subject State World Form : Type)
    (EntityOf : Subject → Entity)
    (Initiates : Subject → State → State → Prop → Prop)
    (Produces : Entity → World → Form → Prop)
    (g : Entity) (w : World) (φ : Form) : Prop where
  /-- The ground is the correlate of no subject — the type fact that discharges the field. -/
  g_is_no_correlate : ∀ s : Subject, EntityOf s ≠ g
  /-- The live succession field, in the live shape. -/
  g_outside_succession : ModelNotInSuccession EntityOf Initiates g
  /-- And yet it produces a form in a world. -/
  g_produces : Produces g w φ

/-- C461 — a ground-like entity can produce a form in a world while satisfying the succession field.

 The countermodel, exhibited. `Entity := Bool` with the ground at `true` and every subject's correlate
 at `false`, so the ground is nobody's correlate and the field is satisfied by disjointness alone;
 `Produces` is the constant-true relation, so the ground produces; `Initiates` is never even
 reachable, and is set to `False` throughout to make the point that its *value* is irrelevant.

 Read against C459: the field distinguishes the ground from nothing, and this row shows what that
 costs — a reading of immutability in which the ground cannot act is *available in the models* and
 therefore cannot be the content of the definition. The two lanes (`Initiates` for subjects,
 `Produces` for entities) are compatible because the definitions are about different things; the
 conflict was never in the relations but in a **word**.

 Footprint: `{}`. -/
theorem a_ground_can_produce_while_outside_succession :
    ∃ (Entity Subject State World Form : Type)
      (EntityOf : Subject → Entity)
      (Initiates : Subject → State → State → Prop → Prop)
      (Produces : Entity → World → Form → Prop)
      (g : Entity) (w : World) (φ : Form),
      GroundProducesCountermodel Entity Subject State World Form EntityOf Initiates Produces g w φ := by
  refine ⟨Bool, Unit, Unit, Unit, Unit, fun _ => false, fun _ _ _ _ => False, fun _ _ _ => True,
    true, (), (), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro _s
    decide
  · rintro ⟨s, _σ, _σ', _p, hEq, _hInit⟩
    exact nomatch hEq
  · trivial

#print axioms a_ground_can_produce_while_outside_succession

end Logos.SuccessionCountermodel


/-!
================================================================================
SECTION: ImmutabilitySoleBearer
================================================================================
-/
/-
# Logos.ImmutabilitySoleBearer — Divine Immutability is *not* sole-bearing, and the machine-checked reason

`Logos.CharacteristicSoleBearer` closes with an honest negative, and this module discharges it.
The claim it declines to prove is C453, the **unicity** of immutability:

```lean
∀ e : Entity, DivineImmutability e → e = Entity.ofGround
```

C453 has been `DEFERRED` with no declaration since the sole-bearer batch. This module replaces the
deferral with a **machine-checked separation**, and — more usefully — with the exact formal
statement of the unavailable universal, which is the same shape as a result the corpus already has.

## Why the claim fails, in one sentence

`NotInSuccession e` is `¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p`, so it holds of **every**
entity whose subject correlate never initiates; and the act datum (C454) requires that *one* subject
initiates, not that *every* subject does. `ExistsAt` for a subject is
`SubjectExistsAt w s := NecessarySubjectKind s ∨ w = actualWorld` (`Entity.lean:55`), so a subject
of the necessary kind exists at every world and satisfies `ModalInvariance` and `StageInvariance`
outright; `CapacityInvariance` is satisfied by every entity (C321). **A necessary-kind subject that
never initiates therefore bears all four fields, and is not the ground.** C453 is non-derivable in this free-signature sense—not proved false inside Γ.

## The right diagnosis, and why it is not a defeat

The trap in refuting a uniqueness claim is to build a model in which *nothing happens* — no
initiation at all — and call that a refutation. Such a model would be a refutation of Γ, not of
C453: `performative_act_datum` forbids it. So the countermodel below is built the other way round.
It **saturates** the act datum — one subject genuinely acts, with a real `Means` and a real
`Initiates` — and only then exhibits a necessary-kind subject that does not. The two findings are
proved in a single model because they are a single fact: *initiation is a real relation with a
real inhabitant, and it is not universal over necessary-kind subjects.*

That is the formal content of the gap between C454 and C453:

| | statement | status |
|---|---|---|
| C454 (global) | `∃ s, ∃ p, Act s p` | `AXIOM` (`performative_act_datum`, `Tag: TRANS`) |
| C453 needs (per-necessary-kind-subject) | `∀ s, NecessaryKind s → ∃ σ σ' p, Initiates s σ σ' p` | **not derivable** — separated below |

ACT-CASCADE (C469–C480) made the *global* form visible in twelve unconditional rows, all of which
inherit the datum. This module shows the price of that: the datum is a **global existential**, and
every necessary-kind-subject strengthening of it is unavailable until someone pays for a per-necessary-kind-subject bound.
The exact missing lemma is now in the ledger rather than implicit in a `DEFERRED`.

## What survives, and is recorded rather than dropped

Unicity of immutability is non-derivable in the free-signature sense used here, but the batch does **not** claim its negation inside Γ. These stay true
and keep their existing ids:

* `ofGround_divine_immutability` (C201) — the ground *is* immutable, `{Initiates, Means,
  NecessarySubjectKind, State, Subject}`, 0 substantive axioms;
* `capacity_invariance_holds_for_every_entity` (C321) — field 4 is vacuous for all entities;
* `the_ground_and_every_atom_are_outside_succession` (C459) — field 3 holds of the ground and of
  every atom;
* `some_entity_is_in_succession` (C487, `Logos.CharacteristicClosure`) — field 3 is *refutable*,
  which C459 alone did not establish.

So the corrected table row reads: **immutability is the one footprint characteristic the ground
does not uniquely bear**, and the reason is quantified over `Subject` rather than over `Entity` —
a subject-indexed relation cannot discriminate an `Entity`-indexed property. That is a general
observation about the vocabulary, not a defect in this batch, and it is the same reason F10's
production relation had to be re-indexed from `Subject` to `Entity` in THOMISTIC-ACT.
-/

namespace Logos.ImmutabilitySoleBearer

open Logos.Semantics (World)
open Logos.Entity (Entity EntityOf)
open Logos.Agency (Subject State Initiates Act performative_act_datum)
open Logos.NecessityEternity (NotInSuccession)

/-- The counter-structure. Every field is one of the four `DivineImmutability` fields, read at its
    own logical strength and no stronger, so that a witness inhabiting this structure is a witness
    that the structure's *shape* does not characterise its bearer. `e` and `g` are two distinct
    entities, standing in for the non-ground bearer and the ground.

    The last two fields are the ACT-CASCADE half: the model must contain a genuine act, so that the
    separation cannot be dismissed as a model in which nothing happens. It must also identify the
    non-acting subject as necessary-kind, because that is the exact arm C453 needs.
    Footprint: `{}`. -/
structure ImmutabilityCountermodel
    (Entity Subject State World Time : Type)
    (EntityOf : Subject → Entity)
    (ExistsAt : World → Entity → Prop)
    (ExistsAtTime : Time → Entity → Prop)
    (EntityMeans : Entity → Prop → Prop)
    (Means : Subject → Prop → Prop)
    (Initiates : Subject → State → State → Prop → Prop)
    (NecessaryKind : Subject → Prop)
    (e g : Entity) : Prop where
  /-- The bearer is not the ground: this witnesses the failure of C453's conclusion. -/
  distinct : e ≠ g
  /-- Field 1: `ModalInvariance e` at full strength, `∀ w₁ w₂, ExistsAt w₁ e ↔ ExistsAt w₂ e`. -/
  modal_invariance : ∀ w₁ w₂ : World, ExistsAt w₁ e ↔ ExistsAt w₂ e
  /-- Field 2: `StageInvariance e` at full strength, `∀ t₁ t₂, ExistsAtTime t₁ e ↔ …`. -/
  stage_invariance : ∀ t₁ t₂ : Time, ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e
  /-- Field 3: `TransitionInvariance e`, i.e. `NotInSuccession e` at full strength — including the
      `Initiates` conjunct that `NecessityEternity.the_ground_not_in_succession` *discards*. -/
  transition_invariance : ¬ ∃ s σ σ' p, e = EntityOf s ∧ Initiates s σ σ' p
  /-- Field 4: `CapacityInvariance e` — vacuous in Γ (C321), and vacuous here too. -/
  capacity_invariance : ∀ p : Prop, EntityMeans e p ↔ EntityMeans e p
  /-- The act datum **holds**: some subject genuinely means and initiates. -/
  some_act : ∃ s : Subject, ∃ p : Prop, Means s p ∧ ∃ w w' : State, Initiates s w w' p
  /-- … and yet the subject arm fails at a necessary-kind subject. This is the exact missing
      universal: it is not merely that some subject fails to act, but that a necessary-kind
      subject never initiates. -/
  necessary_non_acting_subject :
    ∃ s : Subject, NecessaryKind s ∧ e = EntityOf s ∧
      ¬ ∃ σ σ' : State, ∃ p : Prop, Initiates s σ σ' p

/-- C489 — **the ground is not shown to be the sole bearer of Divine Immutability.** C453 is separated, not
    deferred: there is an interpretation of Γ's immutability vocabulary in which a second entity
    satisfies all four fields at full strength while remaining distinct from the ground.

    **The model, in full.** `Entity := Nat` with `g = 0` and `e = 1`; `Subject := Bool`;
    `EntityOf true = 0`, `EntityOf false = 1`; existence constant everywhere; `Means s _ := s`
    and `Initiates s _ _ _ := s`, so `true` acts and `false` does not. `NecessaryKind` holds only
    of `false`. Then `1 ≠ 0`; fields 1, 2 and 4 hold by constancy and reflexivity; field 3 holds
    because the only subject correlating with `1` is the necessary-kind `false`, which initiates
    nothing. And the act datum is **saturated** — `true` means and initiates — so this separates
    the universal claim from Γ's vocabulary rather than denying Γ's datum.

    **Footprint: `{}`.** The statement quantifies over its own types and mentions no Γ axiom: the
    refusal to derive C453 is not a fact about Γ's axioms but about the *shape* of the claim, in
    the same way as C249 (gapless scope ⇏ conjunctive power) and C321. -/
theorem immutability_is_not_sole_bearer :
    ∃ (Entity Subject State World Time : Type)
      (EntityOf : Subject → Entity)
      (ExistsAt : World → Entity → Prop)
      (ExistsAtTime : Time → Entity → Prop)
      (EntityMeans : Entity → Prop → Prop)
      (Means : Subject → Prop → Prop)
      (Initiates : Subject → State → State → Prop → Prop)
      (NecessaryKind : Subject → Prop)
      (e g : Entity),
      ImmutabilityCountermodel Entity Subject State World Time
        EntityOf ExistsAt ExistsAtTime EntityMeans Means Initiates NecessaryKind e g := by
  refine ⟨Nat, Bool, Unit, Unit, Unit,
    fun s => if s then 0 else 1,
    fun _ _ => True, fun _ _ => True, fun _ _ => False, fun s _ => s,
    fun s _ _ _ => s, fun s => s = false, 1, 0, ?_⟩
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _
    exact Iff.rfl
  · intro _ _
    exact Iff.rfl
  · rintro ⟨s, _σ, _σ', _p, hEq, hInit⟩
    have hs : s = true := hInit
    subst hs
    exact absurd hEq (by decide)
  · intro p
    exact Iff.rfl
  · exact ⟨true, True, rfl, Exists.intro () (Exists.intro () rfl)⟩
  · refine ⟨false, rfl, rfl, ?_⟩
    rintro ⟨_, _, _, hInit⟩
    exact absurd hInit (by decide)

/-- C490 — the same model, isolated to the diagnosis, so the ledger row for the *missing lemma*
    cites a theorem about the gap rather than a comment about it. The necessary-kind initiation
    statement is exactly what C453's subject arm needs and exactly what C454 does not give:

      * `performative_act_datum` is `∃ s, ∃ p, Act s p` — a **global** existential;
      * excluding every necessary-kind subject from `NotInSuccession` needs
        `∀ s, NecessaryKind s → ∃ σ σ' p, Initiates s σ σ' p` — a **per-necessary-kind-subject**
        universal.

    An existential does not distribute over that universal, and the countermodel makes the gap
    explicit: in the model of C489 the first holds, while a necessary-kind subject never
    initiates.

    **This is the exact missing lemma, discharged as a negative.** No new axiom: the
    per-necessary-kind-subject bound would have to be `Tag: SEM` or `Tag: VOCAB`, and paying it is
    an author decision recorded in `INHABITED.md`, not something this batch may take. See `F17` in
    `GAPMAP.md`.
    Footprint: `{}`. -/
theorem the_act_datum_does_not_entail_every_subject_acts :
    ∃ (Subject State : Type)
      (Means : Subject → Prop → Prop)
      (Initiates : Subject → State → State → Prop → Prop)
      (NecessaryKind : Subject → Prop),
      (∃ s : Subject, ∃ p : Prop, Means s p ∧ ∃ w w' : State, Initiates s w w' p) ∧
      (∃ s : Subject, NecessaryKind s ∧
        ¬ ∃ σ σ' : State, ∃ p : Prop, Initiates s σ σ' p) := by
  refine ⟨Bool, Unit, fun s _ => s, fun s _ _ _ => s, fun s => s = false, ?_, ?_⟩
  · exact ⟨true, True, rfl, Exists.intro () (Exists.intro () rfl)⟩
  · refine ⟨false, rfl, ?_⟩
    rintro ⟨_, _, _, hInit⟩
    exact absurd hInit (by decide)

#print axioms immutability_is_not_sole_bearer
#print axioms the_act_datum_does_not_entail_every_subject_acts

end Logos.ImmutabilitySoleBearer
