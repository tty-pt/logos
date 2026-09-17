/-
# Logos.Person — Level 2b: from agency to person; §24b inseparability

Person is *defined* structurally (T5, base.txt §12): the agent, rational,
intentional subject already present in the act — not an added axiom.

Tier 1 (2026-09-16): `Agent` and `Rational` are analytical definitions
(`:= True`), so the structural definition collapses to its intentional
core: a person IS a subject who means some content
(`Person s := ∃ p, Means s p`). The `Agent ∧ Rational` conjuncts remain in
the definition for §12 fidelity but are definitionally True.

§24b is formalized under the renderings of Q3.1/Q3.2 (see DESIGN.md):
  * a *feature* of the act is a proposition entailed by the act's content,
    `HasFeature a f := a → f` (logical-consequence reading);
  * a *personal* feature is one that a subject *means*, `Means s f`;
  * a *logical* feature is one that is true or false (bivalence, §10).
On these readings the inseparability becomes a theorem.
-/

import Logos.Core
import Logos.Agency

namespace Logos.Person

open Logos.Core (T IsFalse)
open Logos.Agency (Subject A Rational Means act_implies_means)

/-- Intentionality (§11): the subject means some content. -/
def Intentional (s : Subject) : Prop := ∃ p : Prop, Means s p

/-- Person (structural definition, base.txt §12 / theorem T5). -/
def Person (s : Subject) : Prop := Logos.Agency.Agent s ∧ Rational s ∧ Intentional s

-- ---------------------------------------------------------------------------
-- §24b — personal/logical inseparability of the rational act
-- ---------------------------------------------------------------------------

/-- An act whose content is `a`. -/
def RationalAct (a : Prop) : Prop := ∃ s : Subject, ∃ p : Prop, A s p ∧ a = p

/-- `f` is a feature of content `a` iff `a` logically entails `f`. -/
def HasFeature (a f : Prop) : Prop := a → f

/-- A personal feature of an act: someone means a feature of its content (Q3.1). -/
def CarriesPersonalFeature (a : Prop) : Prop :=
  ∃ p : Prop, HasFeature a p ∧ ∃ s : Subject, Means s p

/-- A logical feature of an act: a feature that is true-or-false (Q3.2). -/
def CarriesLogicalFeature (a : Prop) : Prop :=
  ∃ p : Prop, HasFeature a p ∧ (T p ∨ IsFalse p)

/--Every rational act carries a personal feature exactly when it carries a logical feature: personhood and logic travel together.

 §24b — in every rational act, personal and logical features coincide. -/
theorem inseparability_24b : ∀ a : Prop,
    RationalAct a → (CarriesPersonalFeature a ↔ CarriesLogicalFeature a) := by
  intro a hra
  constructor
  · intro h
    obtain ⟨p, hf, s, hm⟩ := h
    by_cases hT : T p
    · exact ⟨p, hf, Or.inl hT⟩
    · exact ⟨p, hf, Or.inr hT⟩
  · intro h
    obtain ⟨s, q, hq⟩ := hra
    obtain ⟨ha, heq⟩ := hq
    rw [heq]
    exact ⟨q, id, s, act_implies_means ha⟩

-- ---------------------------------------------------------------------------
-- Plurality from the definitional subject (addressee, 2026-09-17)
-- ---------------------------------------------------------------------------

/-- The content of a subject: the posited proposition of `Sum.inr q`, any
    proposition when the subject is the silent origin. -/
def contentOf : Subject → Prop
  | Sum.inl _ => True
  | Sum.inr q => q

/--The canonical pair: the origin and the addressee are two distinct persons.

  `twoPersonsFromSubject` — there are two distinct persons by WHAT A SUBJECT IS
    alone (definitional subject, 2026-09-17): the silent origin
    `Sum.inl ()` and the self-posited content `Sum.inr True` are both persons
    (`Person (Sum.inr True)` because `Means (Sum.inr True) True`) and are
    distinct by constructors. No plurality axiom: the addressee — the one for
    whom something signifies — is a person by the definition of person.
    Discharges the former bridge `AxTwoSubjects`. Footprint: `{}`. -/
theorem twoPersonsFromSubject :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ := by
  refine ⟨Sum.inl (), Sum.inr True, ?_, ?_, ?_⟩
  · exact ⟨trivial, trivial, ⟨True, ⟨True, ⟨True, rfl⟩⟩⟩⟩
  · exact ⟨trivial, trivial, ⟨True, ⟨True, ⟨True, ⟨rfl, rfl⟩⟩⟩⟩⟩
  · intro h
    cases h

/--Every content, raised to a subject, is a person.

  The plenum seed: `∀ p : Prop, Person (Sum.inr p)` — every posited content
    posits itself, so is intentional, so is a person. Distinctness of such
    persons is kernel-visible only for *incompatible* contents (equality of
    propositions is `propext`-collapsed), hence `positedDistinct` below for
    `True`/`False`. Footprint: `{}`. -/
theorem everyContentIsAPerson : ∀ p : Prop, Person (Sum.inr p) := by
  intro p
  exact ⟨trivial, trivial, ⟨p, ⟨True, ⟨p, ⟨rfl, rfl⟩⟩⟩⟩⟩

/--The two extreme contents are two distinct persons.

  `positedDistinct`: `Sum.inr True` and `Sum.inr False` are distinct because
    their contents are (incompatibility is the kernel-visible distinctness
    of propositions). Footprint: `{}`. -/
theorem positedDistinct : (Sum.inr True : Subject) ≠ Sum.inr False := by
  intro h
  have hTF : True = False := congrArg contentOf h
  exact cast hTF True.intro

end Logos.Person

-- Axiom footprint audit
#print axioms Logos.Person.inseparability_24b
#print axioms Logos.Person.twoPersonsFromSubject
#print axioms Logos.Person.everyContentIsAPerson
#print axioms Logos.Person.positedDistinct
