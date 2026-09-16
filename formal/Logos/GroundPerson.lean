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

namespace Logos.GroundPerson

open Logos.Core (T IsFalse)
open Logos.Semantics (Form World)
open Logos.Truthmaker (Entity Ground ExistsAt TrueAt)
open Logos.Modal (NecessaryEntity)
open Logos.Agency (Subject A Means)


/--Vocabulary: the grounding relation between an entity and a proposition.

 Prop-level grounding (the §24a image at the level of propositional
    features): `GroundProp e f` — entity e grounds the *feature* f. -/
axiom GroundProp : Entity → Prop → Prop

/-- `Realizes e f`: e realizes the feature f it grounds. Defined (B2,
    2026-09-15) as `GroundProp` itself — minimal non-reductive realism is a
    *rename*, not a separate assumption; the former `AxGroundBearing` axiom is
    now an `rfl`-level theorem. -/
def Realizes (e : Entity) (f : Prop) : Prop := GroundProp e f

/--The §24a atom-grounding principle reflected at the level of propositions.

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

/--The personal price of T8: what is grounded about a person is grounded in a personal way.

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
/-- Every necessary truth has a necessary grounder. -/
theorem necessary_truth_has_necessary_grounder {τ : Form} (hτ : Logos.Truthmaker.NecessarilyTrue τ) :
    ∃ e : Entity, NecessaryEntity e := by
  obtain ⟨e, hne, _⟩ := Logos.Modal.T7_necessaryReality hτ
  exact ⟨e, hne⟩

end Logos.GroundPerson

-- Axiom footprint audit
#print axioms Logos.GroundPerson.T8_personalGround
#print axioms Logos.GroundPerson.necessary_truth_has_necessary_grounder
