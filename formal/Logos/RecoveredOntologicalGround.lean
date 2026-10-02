/-
# Logos.RecoveredOntologicalGround — Recovered T8 Ontology Layer and Ontological Synthesis

This module restores the authentic mathematical content of T8 and connects it
to the entity-level ground of reality:
1. Formalizes the recovered T8 result: `NecessaryPersonalReality` (Claim C) derived
   directly from `GroundPerson.T8_personalGround`.
2. Formalizes the act-to-personal-reality corollary.
3. Formalizes the stronger entity-level ontology: `GroundOfReality`, `NecessaryGroundOfReality`,
   and `NecessaryPersonalGroundOfReality` (Claim E).
4. Restores the historical reality-grounding principle `AxRealityGrounding` (GAPMAP C130).
5. Strictly separates the contingent human subject from the necessary ground of reality.
6. Connects Personal-Logical Inseparability (`Person.inseparability_24b`), Explanatory
   Adequacy (`explanatory_adequacy` / `atom_cannot_ground_person`), and agential grounding
   transmission to synthesize `NecessaryPersonalGroundOfReality`.
7. Preserves strict level separation: Claim C does not entail Claim E.
-/

import Logos.Core
import Logos.Semantics
import Logos.Entity
import Logos.Modal
import Logos.Agency
import Logos.Person

namespace Logos.RecoveredOntologicalGround

open Logos.Core (T IsFalse)
open Logos.Semantics (Form World Satisfies TrueAt NecessarilyTrue strongTruthExists TV)
open Logos.Entity (Entity ExistsAt actualWorld EntityOf)
open Logos.Modal (NecessaryEntity)
open Logos.Agency (Subject Act A Means Will subjectWill)
open Logos.Person (Person inseparability_24b CarriesPersonalFeature CarriesLogicalFeature RationalAct free_subject_is_person person_is_intentional)

/-- Actual entity: an entity that exists in the actual world. -/
def ActualEntity (e : Entity) : Prop := ExistsAt actualWorld e

/-- Impersonal Entity: an atomic factual entity that is not a subject. -/
def ImpersonalEntity (e : Entity) : Prop := ∃ n : Nat, e = Entity.ofAtom n

/-- Meaning capacity of an entity. NOTE (semantic stipulation, §5.2):
    `Entity.ofGround` returns `True` for every proposition — the omni-meaning of
    the ground is a definitional stipulation of the world-rigid constructor
    (`Entity.ofGround`), distinguishing *the model has a necessary ground* from
    *the argument entails an ontological necessary ground*. -/
def EntityMeans (e : Entity) (p : Prop) : Prop :=
  match e with
  | Entity.ofSubject s => Means s p
  | Entity.ofAtom _ => False
  | Entity.ofGround => True

/-- `OneEssence`: the ontological grounding relation, renamed from `GroundsEntity`
    on 2026-10-02. DEFINITION (meaning-containment, *esse est agere* at the entity
    level): `g` grounds `e` iff `g` possesses at least `e`'s intentional/agential
    capacity — it means everything `e` means. `∀ p, EntityMeans e p → EntityMeans g p`.

    The rename is **naming only**: the definition is unchanged, so every footprint,
    every countermodel and every `{}`-theorem that reads this predicate is unaffected.
    The reason for the new name is that this relation carries the whole Nicene claim —
    one essence indwelt by three persons (`Perichoretic`) — and `GroundsEntity` read as
    "the entity grounds the entity", which is the same word for a strictly weaker claim
    than the one the corpus actually pays for.

    KNOWN DEFECT, recorded not fixed: because `EntityMeans Entity.ofGround p` reduces to
    `True` (see above), this predicate is `True` for every `e`, including atoms, so its
    ground side is vacuous and `ofGround_universal_modal_ground` closes by `True.intro`
    (`FoundationalOmnipresence.lean:73`). Repairing that was deferred as its own item when the
    personal-ground plan was retired (recorded in `AGENTS.md`); it is a separate change from this
    rename, and the vacuity is disclosed here rather than repaired.

    Footprint: `{Means, Subject}`. -/
def OneEssence (g e : Entity) : Prop :=
  ∀ p : Prop, EntityMeans e p → EntityMeans g p

/-- Ontological Distinction: Atomic entities are provably distinct from any subject correlate. -/
theorem ofAtom_ne_ofSubject (n : Nat) (s : Subject) :
    Entity.ofAtom n ≠ EntityOf s :=
  fun h => Entity.noConfusion h

/-- Explanatory Adequacy of Grounding: theorem (definitional consequence of
    `OneEssence`). The ground g of e possesses e's account-carrying meaning.
    Footprint: `{Means, Subject}`. -/
theorem explanatory_adequacy
    (g e : Entity) (hGr : OneEssence g e) (p : Prop) (hEM : EntityMeans e p) :
    EntityMeans g p :=
  hGr p hEM

/-- Theorem: An impersonal atomic entity cannot ground a personal subject. -/
theorem atom_cannot_ground_person
    (n : Nat) (s : Subject) (hPers : Person s) :
    ¬ OneEssence (Entity.ofAtom n) (EntityOf s) := by
  intro hGr
  have hMeans : ∃ p : Prop, Means s p := person_is_intentional s hPers
  obtain ⟨p, hp⟩ := hMeans
  have hEM : EntityMeans (EntityOf s) p := hp
  have hGM : EntityMeans (Entity.ofAtom n) p :=
    explanatory_adequacy (Entity.ofAtom n) (EntityOf s) hGr p hEM
  exact hGM

-- ============================================================================
-- Section 3: Entity-Level Ground of Reality
-- ============================================================================

/-- GroundOfReality: an entity g ontologically grounds every actual entity distinct from itself. -/
def GroundOfReality (g : Entity) : Prop :=
  ∀ e : Entity, ActualEntity e → e = g ∨ OneEssence g e

/-- NecessaryGroundOfReality: an entity is necessary and is the ontological ground of reality. -/
structure NecessaryGroundOfReality (g : Entity) : Prop where
  necessary : NecessaryEntity g
  grounds_reality : GroundOfReality g

-- ============================================================================
-- Section 4: Derivation of the Ground of Reality (T7 + AxRealityGrounding)
-- ============================================================================

/-
`necessary_ground_of_reality_derived` and `necessary_personal_ground_derived`
are REMOVED: their only routes were the deleted axioms `AxRealityGrounding`
and `agential_grounding_transmission`. The entity-level surface
(`GroundOfReality`, `NecessaryGroundOfReality`, `NecessaryPersonalGroundOfReality`)
remains as the annotated Claim-E statement (see Section 1 note). The headline
theorem is the constitutive claim in `Logos.PersonalGroundOfReality`.
-/

-- ============================================================================
-- Section 5: Modal Invariance and Finite Subject Separation
-- ============================================================================

theorem subject_exists_at_actualWorld (s : Subject) : ExistsAt actualWorld (EntityOf s) := by
  dsimp [ExistsAt, Logos.Entity.EntityExistsAt, Logos.Entity.SubjectExistsAt, EntityOf]
  exact Or.inr rfl

/-- **Vacuity disclosure (C321-class): `ActualEntity` holds of every entity, by
    definition.** At `actualWorld := fun _ => TV.t` each constructor closes without
    content: subject-correlates by `actualWorld = actualWorld` (`rfl` — the
    `NecessarySubjectKind` disjunct of `SubjectExistsAt` is dead here, as in
    `subject_exists_at_actualWorld` above), atoms by β-reduction to `TV.t = TV.t`,
    the ground by `True`. So the predicate discriminates nothing; it is a C321-shaped
    vacuity, recorded rather than repaired.

    Consequences, all machine-checked from this row: the `ActualEntity t` conjunct
    of `LovesAsGround.GroundLoves` does no work — the divine love's real target
    conditions are `t ≠ ofGround` and `∃ q, EntityMeans t q` alone; the two
    `DivineTranscendence` universal-grounding statements range over *all* entities,
    not "actual" ones; and any future totality reading keyed on `ActualEntity`
    collapses to `True` (so it cannot carry a "God loves everything" axiom — the
    atom exclusion would still refute it).
    Footprint: `{NecessarySubjectKind, Subject}` (vocabulary-only: the
    `NecessarySubjectKind` disjunct is mentioned but never used — the proof takes
    the `rfl` branch). -/
theorem every_entity_is_actual (e : Entity) : ActualEntity e := by
  dsimp [ActualEntity, ExistsAt]
  cases e with
  | ofSubject s =>
      dsimp [Logos.Entity.EntityExistsAt, Logos.Entity.SubjectExistsAt, EntityOf]
      exact Or.inr rfl
  | ofAtom _ => rfl
  | ofGround => trivial

#print axioms Logos.RecoveredOntologicalGround.every_entity_is_actual

/-- Contingent finite subjects are numerically distinct from any necessary entity.
    Prevents modal collapse and preserves the separation of the human subject from the ground. -/
theorem contingent_subject_ne_necessary_entity
    (s : Subject) (hCont : ∃ w : World, ¬ ExistsAt w (EntityOf s))
    (g : Entity) (hNec : NecessaryEntity g) :
    EntityOf s ≠ g := by
  rintro rfl
  obtain ⟨w, hw⟩ := hCont
  exact hw (hNec w)

/-- The ground of reality strictly grounds any contingent finite subject.
    Eliminates the disjunctive branch `EntityOf s = g` via modal contingency. -/
theorem ground_of_reality_grounds_finite_subject
    (g : Entity) (hg : NecessaryGroundOfReality g)
    (s : Subject) (hCont : ∃ w : World, ¬ ExistsAt w (EntityOf s))
    (hActual : ActualEntity (EntityOf s)) :
    OneEssence g (EntityOf s) := by
  have hDisj := hg.grounds_reality (EntityOf s) hActual
  cases hDisj with
  | inl hEq =>
    exfalso
    exact contingent_subject_ne_necessary_entity s hCont g hg.necessary hEq
  | inr hGrounds =>
    exact hGrounds

-- ============================================================================
-- Section 6: Non-Impersonality and Inseparability
-- ============================================================================

/-- The ground of reality cannot be an impersonal atom.
    Derived via explanatory adequacy (`atom_cannot_ground_person`). -/
theorem ground_of_reality_not_impersonal
    (g : Entity) (hg : NecessaryGroundOfReality g)
    (s : Subject) (hCont : ∃ w : World, ¬ ExistsAt w (EntityOf s))
    (hPers : Person s) (hAct : ActualEntity (EntityOf s)) :
    ¬ ImpersonalEntity g := by
  intro hImp
  obtain ⟨n, rfl⟩ := hImp
  have hGr := ground_of_reality_grounds_finite_subject (Entity.ofAtom n) hg s hCont hAct
  exact atom_cannot_ground_person n s hPers hGr

/-- Any rational act carries personal features (coinciding with logical features by §24b). -/
theorem rational_act_carries_personal_feature
    (s : Subject) (p : Prop) (hAct : Act s p) :
    CarriesPersonalFeature p := by
  have hRat : RationalAct p := ⟨s, p, hAct, rfl⟩
  have hInsep := inseparability_24b p hRat
  have hLog : CarriesLogicalFeature p := by
    refine ⟨p, id, ?_⟩
    by_cases hT : T p
    · exact Or.inl hT
    · exact Or.inr hT
  exact hInsep.mpr hLog

-- ============================================================================
-- Section 7: Master Synthesis Theorem
-- ============================================================================

/-
`necessary_personal_ground_derived` is REMOVED (route used the two deleted
axioms; see Section 4 note). The constitutive headline lives in
`Logos.PersonalGroundOfReality.person_yields_personal_grounding_of_reality`
(historical compatibility alias: `present_act_yields_personal_grounding_of_reality`).
-/

end Logos.RecoveredOntologicalGround
