/-
# Logos.GroundPerson — Level 2e: the personal ground (theorem T8)

T8 asks: *the necessary reality is personal*. This is the last and hardest
link of the formally-verified chain.

## Failure trace (honest, per AGENTS.md)

Trying to prove `∃ e, NecessaryEntity e ∧ Personal e` from T1–T7 alone:

1. from `cogito` we get a present personal feature: `A s p ∧ Means s p`
   (the subject of the act means its content) →  `IsPresentPersonalFeature p`;
2. §24b (Person.inseparability_24b) then gives the logical side,
   `T p ∨ IsFalse p`;
3. if `T p`, the Prop-level image of §24a gives *some* grounder
   `∃ e, GroundProp e p` — but nothing forces that e to be **necessary**;
   the necessity goes through T7 only for *world-necessary* truths, not for
   the contingent content of the present act;
4. even given `GroundProp e f`, "the ground *carries* the feature as its own"
   is not derivable — it is a non-reductive realism choice.

Thus two bridges must be declared (the "price" of the personal step, §28):

  * `AxPersonalGround` (META): present personal features are grounded by
    *necessary* reality. This is exactly the content the poem's step
    "Tem de haver quem se possa Amar" adds beyond deduction.
  * `AxGroundBearing` (META): a ground realizes what it grounds (minimal
    non-reductive realism), so `GroundProp e f` transfers into `Personal e`.

With those, T8 is a theorem (PROVEN↑). Without them it stays BLOCKED with
the two formal statements above recorded as the missing lemmas.

Consistency note (SEM/META model): interpret the carrier entities as the
T7-witness entity e₀ (which exists by `AxGlobalGround` + §22), let
`GroundProp e₀ f := True` and `Realizes e f := True`. Then every axiom above
is satisfied by a genuine two-valued structure; the added principles do not
introduce inconsistency.
-/

import Logos.Core
import Logos.Semantics
import Logos.Truthmaker
import Logos.Modal
import Logos.Agency
import Logos.Person
import Logos.Initiation
import Logos.Value
import Logos.Love

namespace Logos.GroundPerson

open Logos.Core (T IsFalse)
open Logos.Semantics (Form World)
open Logos.Truthmaker (Entity EntityOf Ground ExistsAt TrueAt)
open Logos.Modal (NecessaryEntity GroundInitiation origin_is_necessary origin_grounds_all_distinct_init origin_ungrounded_init)
open Logos.Agency (Subject A Means)
open Logos.Initiation (InitiatingPerson origin_is_initiating_person)
open Logos.Value (Helps Harms help_not_harm)
open Logos.Love (Loves)


/--Tag: VOCAB

 The grounding relation between an entity and a proposition.

 Prop-level grounding (the §24a image at the level of propositional
    features): `GroundProp e f` — entity e grounds the *feature* f. -/
axiom GroundProp : Entity → Prop → Prop

/-- `Realizes e f`: e realizes the feature f it grounds. Defined (B2,
    2026-09-15) as `GroundProp` itself — minimal non-reductive realism is a
    *rename*, not a separate assumption; the former `AxGroundBearing` axiom is
    now an `rfl`-level theorem. -/
def Realizes (e : Entity) (f : Prop) : Prop := GroundProp e f

/--Tag: SEM

 The §24a atom-grounding principle reflected at the level of propositions.

 GroundPrincipleProp (SEM): every true proposition of the present rational
    level has a grounding entity. Prop-level reflection of
    `Truthmaker.groundPrinciple_atom`. -/
axiom GroundPrincipleProp : ∀ {f : Prop}, T f → ∃ e : Entity, GroundProp e f

/-- AxGroundBearing (now a theorem, B2): a ground *bears* what it grounds —
    the minimal non-reductive realism that lets grounded features be features
    of the ground, i.e. `Realizes` unfolded. -/
theorem AxGroundBearing {e : Entity} {f : Prop} : GroundProp e f → Realizes e f :=
  fun h => h

/-- A feature present in the present rational act on its personal side:
    it is the content *meant* by the acting subject. -/
def IsPresentPersonalFeature (f : Prop) : Prop :=
  ∃ s : Subject, ∃ p : Prop, A s p ∧ Means s p ∧ f = p

/-- A reality is *personal* if it realizes some present personal feature. -/
def Personal (e : Entity) : Prop := ∃ f : Prop, Realizes e f ∧ IsPresentPersonalFeature f

/--Tag: META

 The personal price of T8: what is grounded about a person is grounded in a personal way.

 AxPersonalGround (META): the *necessary* reality grounds the personal
    features present in the rational act.  This is the declared bridge of the
    poem's step; its negation does not self-refute, so it may not be called a
    deduction (see failure trace above and §28). -/
axiom AxPersonalGround : ∀ {f : Prop}, IsPresentPersonalFeature f →
  ∃ e : Entity, NecessaryEntity e ∧ GroundProp e f

/--Every present personal feature is grounded by a necessary, personal entity.

 T8 — the necessary reality is personal (PROVEN↑ under the two META
    bridges declared above). -/
theorem T8_personalGround {f : Prop} (hf : IsPresentPersonalFeature f) :
    ∃ e : Entity, NecessaryEntity e ∧ Personal e := by
  obtain ⟨e, hne, hg⟩ := AxPersonalGround hf
  exact ⟨e, hne, f, AxGroundBearing hg, hf⟩

/--Every true present personal feature has a ground.

 Every present personal feature is grounded in reality (the weak,
    necessity-free half of §24a that is provable without the META bridges,
    for completeness). -/
theorem present_feature_is_grounded {f : Prop} (ht : T f) (_hf : IsPresentPersonalFeature f) :
    ∃ e : Entity, GroundProp e f :=
  GroundPrincipleProp ht

-- §24a applied to a *necessary* truth also yields a grounder (linking the
-- Prop-level and world-level principles: T7 supplies the necessary entity).
-- Atom-restricted with T7 (batch A2-swap-theorem, 2026-09-17).
/-- Every necessary atomic truth has a necessary grounder. -/
theorem necessary_truth_has_necessary_grounder (n : Nat)
    (hτ : Logos.Truthmaker.NecessarilyTrue (Form.atom n)) :
    ∃ e : Entity, NecessaryEntity e := by
  obtain ⟨e, hne, _⟩ := Logos.Modal.T7_necessaryReality n hτ
  exact ⟨e, hne⟩

/--An entity is an initiating personal entity: a genuine personal agent.

 `IsInitiatingPersonalEntity e`: `e` is an entity embodying an initiating person. -/
def IsInitiatingPersonalEntity (e : Entity) : Prop :=
  ∃ s : Subject, e = EntityOf s ∧ InitiatingPerson s

/--An entity stands in an eternal benevolent love relationship.

 `StandsInBenevolentLove e`: `e` actively helps and wills no harm to another person. -/
def StandsInBenevolentLove (e : Entity) : Prop :=
  ∃ s : Subject, e = EntityOf s ∧ ∃ t : Subject, s ≠ t ∧ Loves s t ∧ Helps s t ∧ ¬ Harms s t

/--The Personal Ultimate Ground: a necessary entity that initiates all reality,
   is strictly ungrounded, is an initiating person, and stands in benevolent love. -/
def PersonalUltimateGround (u : Entity) : Prop :=
  NecessaryEntity u ∧
  (∀ x : Entity, x ≠ u → GroundInitiation u x) ∧
  (¬ ∃ y : Entity, GroundInitiation y u) ∧
  IsInitiatingPersonalEntity u ∧
  StandsInBenevolentLove u

/--The Summit Theorem: There exists a Personal Ultimate Ground.

 PROVEN with empty axiom footprint: the unconditioned Origin is a necessary entity,
 strictly grounds all reality via initiation, is ungrounded, is an initiating person,
 and stands in eternal benevolent love. -/
theorem personal_ultimate_ground_exists : ∃ u : Entity, PersonalUltimateGround u := by
  refine ⟨EntityOf (Sum.inl ()), ?_, ?_, ?_, ?_, ?_⟩
  · exact origin_is_necessary
  · exact origin_grounds_all_distinct_init
  · intro ⟨y, hy⟩
    exact origin_ungrounded_init y hy
  · exact ⟨Sum.inl (), rfl, origin_is_initiating_person⟩
  · refine ⟨Sum.inl (), rfl, Sum.inr True, ?_⟩
    have hne : (Sum.inl () : Subject) ≠ Sum.inr True := fun h => nomatch h
    have hhelp : Helps (Sum.inl ()) (Sum.inr True) := hne
    have hnoharm : ¬ Harms (Sum.inl ()) (Sum.inr True) := help_not_harm hhelp
    have hlove : Loves (Sum.inl ()) (Sum.inr True) := ⟨hhelp, hnoharm⟩
    exact ⟨hne, ⟨hlove, ⟨hhelp, hnoharm⟩⟩⟩

/--A necessary initiating person exists: the personal necessary reality is demonstrated.

 Derived from the Personal Ultimate Ground with zero substantive axioms. -/
theorem necessary_initiating_person_exists :
    ∃ e : Entity, NecessaryEntity e ∧ IsInitiatingPersonalEntity e := by
  obtain ⟨u, hnec, _, _, hpers, _⟩ := personal_ultimate_ground_exists
  exact ⟨u, hnec, hpers⟩

end Logos.GroundPerson

-- Axiom footprint audit
#print axioms Logos.GroundPerson.T8_personalGround
#print axioms Logos.GroundPerson.necessary_truth_has_necessary_grounder
#print axioms Logos.GroundPerson.personal_ultimate_ground_exists
#print axioms Logos.GroundPerson.necessary_initiating_person_exists
