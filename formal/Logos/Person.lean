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

end Logos.Person

-- Axiom footprint audit
#print axioms Logos.Person.inseparability_24b
