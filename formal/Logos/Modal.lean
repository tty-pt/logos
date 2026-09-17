/-
# Logos.Modal — necessity, contingency, and T7 (base.txt §22→T7)

T7 in the prose runs: necessary truth τ ⇒ τ is grounded in no *contingent*
entity ⇒ some non-contingent reality grounds τ ⇒ ∃r □Exists(r).

The informal step `∀w∃r … ⇒ ∃r∀w …` is now a THEOREM for atoms
(batch A2-swap-theorem, 2026-09-17): `ExistsAt` is world-vacuous by
definition (esse est agere), so the witness from any one world works for
all worlds definitionally — no swap axiom is needed. The compound
excluded-middle instance stays unforced (structural `TrueAt` carries no
existential ground for compounds; M4 spike) and is recorded BLOCKED with
its exact missing lemma (GAPMAP.md C19).

Sub-question Q7.2 (ANSWERED, see DESIGN.md): for atoms the swap needs no
weaker premise — it is definitional; the compound instance is a different,
unforced claim, not a footprint-preserving replacement.
-/

import Logos.Core
import Logos.Semantics
import Logos.Truthmaker
import Logos.Agency
import Logos.Initiation

namespace Logos.Modal

open Logos.Semantics (Form World)
open Logos.Truthmaker (Entity EntityOf Ground ExistsAt TrueAt NecessarilyTrue)
open Logos.Agency (Subject Means)
open Logos.Initiation (InitiatingPerson origin_is_initiating_person posited_not_initiating_person)

/-- The present world (SEM, definitional): the performed actuality of the
    reasoning act needs only *some* fixed world in T7 (`Ground e τ` is invoked
    at it and nothing depends on which world it is). Modeled as the
    always-true valuation (precedent: `Necessity.someWorld`). No longer an
    axiom: `def actualWorld` shrinks the C18–C20 footprints. -/
def actualWorld : World := fun _ => Logos.Semantics.TV.t

/-- An entity is necessary iff it exists in every world. -/
def NecessaryEntity (e : Entity) : Prop := ∀ w : World, ExistsAt w e

/-- An entity is contingent iff it is not necessary. -/
def Contingent (e : Entity) : Prop := ¬ NecessaryEntity e

/-- A non-subject atomic entity is not identical to any subject under EntityOf. -/
theorem not_subject_ofAtom (n : Nat) : ¬ ∃ s : Subject, EntityOf s = Entity.ofAtom n := by
  rintro ⟨s, h⟩
  nomatch h

/-- Atomic worldly entities are contingent: they fail to exist in a world where atoms evaluate false. -/
theorem contingent_atom (n : Nat) : Contingent (Entity.ofAtom n) := by
  intro hnec
  have hw : ExistsAt (fun _ => Logos.Semantics.TV.f) (Entity.ofAtom n) :=
    hnec (fun _ => Logos.Semantics.TV.f)
  nomatch hw

/-- A contingent entity exists in the ontology: atomic worldly entities are contingent. -/
theorem contingent_entity_exists : ∃ e : Entity, Contingent e :=
  ⟨Entity.ofAtom 0, contingent_atom 0⟩

/-- Model witness: a contingent non-subject entity is representable. -/
theorem contingent_non_subject_exists :
    ∃ e : Entity, Contingent e ∧ ¬ ∃ s : Subject, EntityOf s = e :=
  ⟨Entity.ofAtom 0, contingent_atom 0, not_subject_ofAtom 0⟩

/-- Subjects are necessary entities under the ontology: their existence does not depend on world valuations. -/
theorem subject_is_necessary (s : Subject) : NecessaryEntity (EntityOf s) := by
  intro _w
  trivial

/--The Primordial Origin is a necessary entity.

 The originating subject exists across all possible worlds. -/
theorem origin_is_necessary : NecessaryEntity (EntityOf (Sum.inl ())) := by
  apply subject_is_necessary

/--An entity is a transcendental subject entity.

 `IsSubjectEntity e`: `e` is the entity-correlate of an acting subject. -/
def IsSubjectEntity (e : Entity) : Prop := ∃ s : Subject, e = Entity.ofSubject s

/--An entity is an empirical atomic entity.

 `IsAtomEntity e`: `e` is an empirical atomic state of affairs. -/
def IsAtomEntity (e : Entity) : Prop := ∃ n : Nat, e = Entity.ofAtom n

/--The empty world: all atomic empirical facts evaluate to false.

 `emptyWorld`: the counterfactual state devoid of all contingent empirical facts. -/
def emptyWorld : World := fun _ => Logos.Semantics.TV.f

/--No empirical atomic entity exists in the empty world.

 In the empty world, every empirical atomic state fails to exist. -/
theorem emptyWorld_no_atom (n : Nat) : ¬ ExistsAt emptyWorld (Entity.ofAtom n) := by
  intro h
  nomatch h

/--Any entity existing in the empty world is a transcendental subject.

 Any entity capable of existing in the absence of empirical facts is a subject. -/
theorem entity_in_emptyWorld_is_subject (e : Entity) (he : ExistsAt emptyWorld e) :
    IsSubjectEntity e := by
  cases e with
  | ofSubject s => exact ⟨s, rfl⟩
  | ofAtom n => nomatch he

/-- Constructive proposition divergence: no proposition is equal to its own negation.
    Pure intuitionistic logic, zero axioms. -/
theorem prop_neq_not (q : Prop) : q ≠ (q → False) := by
  intro h
  have hnot : q → False := fun hq => (h ▸ hq) hq
  have hq : q := h.symm ▸ hnot
  exact hnot hq

/-- Intentional capacity of an entity: an entity means proposition `p` iff it is a
    subject performing the intentional act `Means s p`. Non-subject entities have
    no intentional capacity. Agency remains strictly restricted to `Subject`. -/
def EntityMeans (e : Entity) (p : Prop) : Prop :=
  match e with
  | Entity.ofSubject s => Means s p
  | Entity.ofAtom _ => False

/-- Ontological grounding between entities: entity `s` strictly grounds entity `x`.
    Substantive & analytical: `s` is distinct from `x`, `s` subsumes all intentional
    capacity of `x`, and `s` strictly transcends `x` in intentional capacity.
    Forms a strict partial order. -/
def GroundEntity (s x : Entity) : Prop :=
  s ≠ x ∧
  (∀ p : Prop, EntityMeans x p → EntityMeans s p) ∧
  (∃ p : Prop, EntityMeans s p ∧ ¬ EntityMeans x p)

/--Ontological grounding is strictly irreflexive: no entity can ground itself.

  Axiom footprint: `{}`. -/
theorem groundEntity_irreflexive (x : Entity) : ¬ GroundEntity x x := by
  intro ⟨hne, _, _⟩
  exact hne rfl

/--Ontological grounding is strictly asymmetric: if `s` grounds `x`, then `x` cannot ground `s`.

  Axiom footprint: `{}`. -/
theorem groundEntity_asymmetric {s x : Entity} :
    GroundEntity s x → ¬ GroundEntity x s := by
  intro ⟨_, _, ⟨p, hms_p, hnot_mx_p⟩⟩ ⟨_, hsub_xs, _⟩
  exact hnot_mx_p (hsub_xs p hms_p)

/--Ontological grounding is transitive: grounding chains compose.

  Axiom footprint: `{}`. -/
theorem groundEntity_transitive {a b c : Entity} :
    GroundEntity a b → GroundEntity b c → GroundEntity a c := by
  intro ⟨_, hsub_ab, ⟨p, hma_p, hnot_mb_p⟩⟩ ⟨_, hsub_bc, _⟩
  have hnot_mc_p : ¬ EntityMeans c p := fun hmc_p => hnot_mb_p (hsub_bc p hmc_p)
  refine ⟨?_, fun r hr => hsub_ab r (hsub_bc r hr), ⟨p, hma_p, hnot_mc_p⟩⟩
  intro heq
  subst heq
  exact hnot_mc_p hma_p

/--Step A: A necessary entity exists.

  Witnessed by the silent origin embedding into Entity.
  Axiom footprint: `{}`. -/
theorem necessary_entity_exists : ∃ s : Entity, NecessaryEntity s :=
  ⟨EntityOf (Sum.inl ()), subject_is_necessary (Sum.inl ())⟩

/--The silent origin grounds every posited content.

  The origin subsumes all intentional acts of the posited content and strictly transcends it.
  Axiom footprint: `{}`. -/
theorem origin_grounds_posited (q : Prop) :
    GroundEntity (EntityOf (Sum.inl ())) (EntityOf (Sum.inr q)) := by
  constructor
  · intro h
    nomatch h
  · constructor
    · intro p _
      exact ⟨True, p, rfl⟩
    · refine ⟨q → False, ⟨True, q → False, rfl⟩, ?_⟩
      intro ⟨w, w', heq⟩
      exact prop_neq_not q heq.1

/--The silent origin grounds every atomic non-subject entity.

  Non-subject entities have no intentional capacity; the origin trivially subsumes them
  and strictly transcends them with its universal agency.
  Axiom footprint: `{}`. -/
theorem origin_grounds_atom (n : Nat) :
    GroundEntity (EntityOf (Sum.inl ())) (Entity.ofAtom n) := by
  constructor
  · intro h
    nomatch h
  · constructor
    · intro p hp
      nomatch hp
    · exact ⟨True, ⟨True, True, rfl⟩, fun h => nomatch h⟩

/--Step B: The silent origin strictly grounds every entity distinct from itself.

  Every distinct entity is either a posited content or a non-subject worldly entity,
  both of which are subsumed and transcended by the origin.
  Axiom footprint: `{}`. -/
theorem origin_grounds_all_distinct (x : Entity) (hne : x ≠ EntityOf (Sum.inl ())) :
    GroundEntity (EntityOf (Sum.inl ())) x := by
  cases x with
  | ofSubject s =>
    cases s with
    | inl u => cases u; exact False.elim (hne rfl)
    | inr q => exact origin_grounds_posited q
  | ofAtom n => exact origin_grounds_atom n

/--There exists a necessary entity that strictly grounds all entities distinct from itself.

  Axiom footprint: `{}`. -/
theorem ground_all_distinct_exists :
    ∃ s : Entity, NecessaryEntity s ∧ ∀ x : Entity, x ≠ s → GroundEntity s x :=
  ⟨EntityOf (Sum.inl ()), subject_is_necessary (Sum.inl ()), origin_grounds_all_distinct⟩

/--Substantive grounding witness: the silent origin strictly grounds posited truth.

  Non-vacuous witness showing genuine grounding between distinct entities.
  Axiom footprint: `{}`. -/
theorem substantive_grounding_witness :
    ∃ s x : Entity, s ≠ x ∧ NecessaryEntity s ∧ GroundEntity s x := by
  refine ⟨EntityOf (Sum.inl ()), EntityOf (Sum.inr True), ?_,
          subject_is_necessary (Sum.inl ()), origin_grounds_posited True⟩
  intro h
  nomatch h

/--No entity grounds the silent origin: universal agency cannot be transcended.

  Axiom footprint: `{}`. -/
theorem origin_ungrounded (y : Entity) : ¬ GroundEntity y (EntityOf (Sum.inl ())) := by
  intro ⟨_, _, ⟨p, _, hnot_origin⟩⟩
  have horigin : EntityMeans (EntityOf (Sum.inl ())) p := ⟨True, p, rfl⟩
  exact hnot_origin horigin

/--Step C: The silent origin is strictly ungrounded by any entity in reality.

  Substantive consequence of universal agency capacity.
  Axiom footprint: `{}`. -/
theorem origin_not_grounded : ¬ ∃ y : Entity, GroundEntity y (EntityOf (Sum.inl ())) := by
  intro ⟨y, hy⟩
  exact origin_ungrounded y hy

/--There exists a necessary entity that is not grounded by any entity.

  Axiom footprint: `{}`. -/
theorem ungrounded_necessary_entity_exists :
    ∃ s : Entity, NecessaryEntity s ∧ ¬ ∃ y : Entity, GroundEntity y s :=
  ⟨EntityOf (Sum.inl ()), subject_is_necessary (Sum.inl ()), origin_not_grounded⟩

/--Every contingent entity is grounded in the silent origin (C78).

  Substantively proven: any contingent entity is necessarily distinct from the
  necessary origin, and is therefore strictly grounded by universal subsumption.
  Axiom footprint: `{}`. -/
theorem contingent_ground (x : Entity) (hx : Contingent x) :
    GroundEntity (EntityOf (Sum.inl ())) x := by
  apply origin_grounds_all_distinct
  intro heq
  subst heq
  exact hx (subject_is_necessary (Sum.inl ()))

/-- The Ultimate Ground: a necessary entity which strictly grounds everything
    distinct from itself and which is not grounded by another entity. -/
def UltimateGround (s : Entity) : Prop :=
  NecessaryEntity s ∧
  (∀ x : Entity, x ≠ s → GroundEntity s x) ∧
  (¬ ∃ y : Entity, GroundEntity y s)

/--Step D: An Ultimate Ground exists: there is a necessary entity that strictly grounds all entities distinct from itself and is not grounded by any entity.

  Synthesizes necessary existence (Step A), universal grounding of distinct entities (Step B),
  and strict non-derivation/ungroundedness (Step C).
  Axiom footprint: `{}`. -/
theorem ultimateGround_exists : ∃ s : Entity, UltimateGround s :=
  ⟨EntityOf (Sum.inl ()), subject_is_necessary (Sum.inl ()),
   origin_grounds_all_distinct, origin_not_grounded⟩

/--An entity has genuine self-initiation: it is an initiating person.

 `EntityInitiates e`: `e` possesses genuine spontaneous initiation, not deterministic transfer. -/
def EntityInitiates (e : Entity) : Prop :=
  match e with
  | Entity.ofSubject s => InitiatingPerson s
  | Entity.ofAtom _ => False

/--An entity has derived movement or lacks spontaneous initiation.

 `EntityIsDerived e`: `e` moves deterministically as a transfer or is a passive atomic state. -/
def EntityIsDerived (e : Entity) : Prop :=
  match e with
  | Entity.ofSubject s => ¬ InitiatingPerson s
  | Entity.ofAtom _ => True

/--The Primordial Origin possesses spontaneous self-initiation.

 Witnessed by the branching movement of the silent origin. -/
theorem origin_initiates : EntityInitiates (EntityOf (Sum.inl ())) :=
  origin_is_initiating_person

/--Posited contents are derived transfers, not self-initiators.

 Posited propositions move as deterministic transfers. -/
theorem posited_is_derived (q : Prop) : EntityIsDerived (EntityOf (Sum.inr q)) :=
  posited_not_initiating_person q

/--Atomic entities are derived states of affairs.

 Empirical atoms possess no self-initiating agency. -/
theorem atom_is_derived (n : Nat) : EntityIsDerived (Entity.ofAtom n) := by
  trivial

/--Ontological grounding as initiation dependence: the ground initiates, the grounded is derived.

 `GroundInitiation s x`: `s` strictly grounds `x` iff `s ≠ x`, `s` possesses unconditioned
 initiation, and `x` is derived or transferred. -/
def GroundInitiation (s x : Entity) : Prop :=
  s ≠ x ∧ EntityInitiates s ∧ EntityIsDerived x

/--Initiation grounding is strictly irreflexive: no entity can ground itself.

 A self-identical entity cannot be both initiating and derived relative to itself. -/
theorem groundInitiation_irreflexive (x : Entity) : ¬ GroundInitiation x x := by
  intro ⟨hne, _, _⟩
  exact hne rfl

/--Initiation grounding is strictly asymmetric: the initiator cannot be grounded by its derivative.

 Asymmetry is guaranteed by the incompatibility of unconditioned initiation and derived transfer. -/
theorem groundInitiation_asymmetric {s x : Entity} :
    GroundInitiation s x → ¬ GroundInitiation x s := by
  intro ⟨_, hs_init, hx_der⟩ ⟨_, hx_init, _⟩
  cases x with
  | ofSubject sx =>
    have hx_init' : InitiatingPerson sx := hx_init
    have hx_der' : ¬ InitiatingPerson sx := hx_der
    exact hx_der' hx_init'
  | ofAtom n =>
    nomatch hx_init

/--Initiation grounding is transitive: chains of derived dependence compose.

 Transitivity holds as derived entities cannot initiate. -/
theorem groundInitiation_transitive {a b c : Entity} :
    GroundInitiation a b → GroundInitiation b c → GroundInitiation a c := by
  intro ⟨_, ha_init, hb_der⟩ ⟨_, hb_init, _⟩
  cases b with
  | ofSubject sb =>
    have hb_init' : InitiatingPerson sb := hb_init
    have hb_der' : ¬ InitiatingPerson sb := hb_der
    exact False.elim (hb_der' hb_init')
  | ofAtom n =>
    nomatch hb_init

/--The silent origin strictly grounds all entities distinct from itself via initiation dependence.

 Every entity other than the origin is either a derived transfer or an empirical atom. -/
theorem origin_grounds_all_distinct_init (x : Entity) (hne : x ≠ EntityOf (Sum.inl ())) :
    GroundInitiation (EntityOf (Sum.inl ())) x := by
  constructor
  · intro h
    subst h
    exact hne rfl
  · constructor
    · exact origin_initiates
    · cases x with
      | ofSubject s =>
        cases s with
        | inl u => cases u; exact False.elim (hne rfl)
        | inr q => exact posited_is_derived q
      | ofAtom n => exact atom_is_derived n

/--The silent origin is strictly ungrounded: no entity can ground unconditioned initiation.

 An unconditioned initiator cannot be derived from any source. -/
theorem origin_ungrounded_init (y : Entity) :
    ¬ GroundInitiation y (EntityOf (Sum.inl ())) := by
  intro ⟨_, _, hy_der⟩
  have horig : InitiatingPerson (Sum.inl ()) := origin_is_initiating_person
  exact hy_der horig

/--The Ultimate Ground under Initiation: a necessary entity that initiates all and is ungrounded.

 `UltimateGroundInit u`: `u` is necessary, strictly grounds all distinct entities via initiation,
 and is strictly ungrounded. -/
def UltimateGroundInit (u : Entity) : Prop :=
  NecessaryEntity u ∧
  (∀ x : Entity, x ≠ u → GroundInitiation u x) ∧
  (¬ ∃ y : Entity, GroundInitiation y u)

/--The Ultimate Ground exists under genuine initiation grounding.

 Proven with empty axiom footprint: the silent origin satisfies all requirements. -/
theorem ultimateGroundInit_exists : ∃ u : Entity, UltimateGroundInit u := by
  refine ⟨EntityOf (Sum.inl ()), subject_is_necessary (Sum.inl ()),
          origin_grounds_all_distinct_init, ?_⟩
  intro ⟨y, hy⟩
  exact origin_ungrounded_init y hy

/--An atomic formula true in every world is grounded by a single entity existing in every world (the quantifier swap, atom-restricted).

 AxGlobalGround (theorem, batch A2-swap-theorem 2026-09-17; former SEM
    axiom, D7): a necessarily-true atom is grounded by a single entity
    that exists in every world. Name kept (precedent: `AxPersonStability`).

    Proof: In the empty world (all atoms false), no atomic entity exists,
    so any grounder of an atomic truth in that world must be a subject;
    subjects exist across all worlds, so the witness holds in every world.
    Axiom footprint: `{Ground}`. -/
theorem AxGlobalGround (n : Nat) (hnec : NecessarilyTrue (Form.atom n)) :
    ∃ e : Entity, ∀ w : World, ExistsAt w e ∧ Ground e (Form.atom n) := by
  obtain ⟨e, he_f, hg⟩ := hnec (fun _ => Logos.Semantics.TV.f)
  cases e with
  | ofSubject s => exact ⟨Entity.ofSubject s, fun _w => ⟨trivial, hg⟩⟩
  | ofAtom k => nomatch he_f

/--Atomic necessary truth forces necessary reality: whatever atom is true in every world is grounded by an entity existing in every world.

 T7 — atomic necessary truth forces necessary reality (base.txt T7,
    atom-restricted).

    PROVEN {Ground}-vocab (batch A2-swap-theorem; former PROVEN↑ under the
    `AxGlobalGround` axiom). -/
theorem T7_necessaryReality (n : Nat) (hnec : NecessarilyTrue (Form.atom n)) :
    ∃ e : Entity, NecessaryEntity e ∧ Ground e (Form.atom n) := by
  obtain ⟨e, he⟩ := AxGlobalGround n hnec
  exact ⟨e, fun w => (he w).1, (he actualWorld).2⟩

/--Transcendental Quantifier Swap: a necessary atom forces a necessary subject grounder.

 Any necessarily true atom must be grounded by a transcendental subject existing in all worlds. -/
theorem transcendental_quantifier_swap (n : Nat) (hnec : NecessarilyTrue (Form.atom n)) :
    ∃ s : Subject, NecessaryEntity (EntityOf s) ∧ Ground (EntityOf s) (Form.atom n) := by
  obtain ⟨e, he_empty, hg⟩ := hnec emptyWorld
  cases e with
  | ofSubject s =>
    refine ⟨s, subject_is_necessary s, hg⟩
  | ofAtom k =>
    nomatch he_empty

/--Modal Rigidity of the Ground: the ground of necessity is transcendentally subject-like.

 What grounds a necessary truth is invariant across worlds and of personal/subjective nature. -/
theorem modal_rigidity_of_ground (n : Nat) (hnec : NecessarilyTrue (Form.atom n)) :
    ∃ e : Entity, NecessaryEntity e ∧ IsSubjectEntity e ∧ Ground e (Form.atom n) := by
  obtain ⟨s, hnec_s, hg⟩ := transcendental_quantifier_swap n hnec
  exact ⟨EntityOf s, hnec_s, ⟨s, rfl⟩, hg⟩

/--If every entity were contingent, no atom could be true in every world.

 The reductio shape of the prose, atom-restricted: if every entity were
    contingent, no atomic formula could be necessarily true. -/
theorem noNecessaryTruthIfAllContingent :
    (∀ e : Entity, Contingent e) → ∀ n : Nat, ¬ NecessarilyTrue (Form.atom n) := by
  intro hall n hτ
  obtain ⟨e, hne, _⟩ := T7_necessaryReality n hτ
  exact (hall e) hne

end Logos.Modal

-- Axiom footprint audit
#print axioms Logos.Modal.not_subject_ofAtom
#print axioms Logos.Modal.contingent_atom
#print axioms Logos.Modal.contingent_entity_exists
#print axioms Logos.Modal.contingent_non_subject_exists
#print axioms Logos.Modal.subject_is_necessary
#print axioms Logos.Modal.origin_is_necessary
#print axioms Logos.Modal.emptyWorld_no_atom
#print axioms Logos.Modal.entity_in_emptyWorld_is_subject
#print axioms Logos.Modal.transcendental_quantifier_swap
#print axioms Logos.Modal.modal_rigidity_of_ground
#print axioms Logos.Modal.groundEntity_irreflexive
#print axioms Logos.Modal.groundEntity_asymmetric
#print axioms Logos.Modal.groundEntity_transitive
#print axioms Logos.Modal.necessary_entity_exists
#print axioms Logos.Modal.origin_grounds_posited
#print axioms Logos.Modal.origin_grounds_atom
#print axioms Logos.Modal.origin_grounds_all_distinct
#print axioms Logos.Modal.ground_all_distinct_exists
#print axioms Logos.Modal.substantive_grounding_witness
#print axioms Logos.Modal.origin_ungrounded
#print axioms Logos.Modal.origin_not_grounded
#print axioms Logos.Modal.ungrounded_necessary_entity_exists
#print axioms Logos.Modal.contingent_ground
#print axioms Logos.Modal.ultimateGround_exists
#print axioms Logos.Modal.origin_initiates
#print axioms Logos.Modal.posited_is_derived
#print axioms Logos.Modal.atom_is_derived
#print axioms Logos.Modal.groundInitiation_irreflexive
#print axioms Logos.Modal.groundInitiation_asymmetric
#print axioms Logos.Modal.groundInitiation_transitive
#print axioms Logos.Modal.origin_grounds_all_distinct_init
#print axioms Logos.Modal.origin_ungrounded_init
#print axioms Logos.Modal.ultimateGroundInit_exists
#print axioms Logos.Modal.AxGlobalGround
#print axioms Logos.Modal.T7_necessaryReality
#print axioms Logos.Modal.noNecessaryTruthIfAllContingent
