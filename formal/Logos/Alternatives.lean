/-
# Logos.Alternatives — Level 2c: rational agency and incompatible alternatives (base.txt §13)

T9 is a genuinely *missing* lemma in the prose: §13 asserts the existence of
incompatible representable contents but does not derive it. Given bivalence
(T3 + tschema), it follows from the T3-results `∃p, T p` and `∃q, ¬T q`
with the explicit witnesses `True` / `False`.
-/

import Logos.Core

namespace Logos.Alternatives

open Logos.Core (T IsFalse tschema)

/-- `p` and `q` are incompatible contents. -/
def Incompatible (p q : Prop) : Prop := ¬ (p ∧ q)

/--There are two incompatible alternatives, one of them true and the other false.

 T9 — there are at least two incompatible contents, one true and one false:
    the minimal field of rational choice of §13 is non-empty, and it is
    present constructively (no choice axioms). -/
theorem T9_incompatibleAlternatives :
    ∃ p q : Prop, Incompatible p q ∧ T p ∧ IsFalse q := by
  refine ⟨True, False, ?_, ?_, ?_⟩
  · intro h
    exact h.2
  · exact Logos.Core.atomicTruthWitnessed
  · exact Logos.Core.atomicWitnessFalsehood

/--Every true proposition is incompatible with its own negation.

 General form: any true content and its own negation are incompatible. -/
theorem incompatible_with_negation {p : Prop} (hp : T p) :
    Incompatible p (¬ p) ∧ T p ∧ IsFalse (¬ p) := by
  refine ⟨fun h => h.2 h.1, hp, ?_⟩
  intro hTnot
  exact (tschema (¬ p)).1 hTnot ((tschema p).1 hp)

end Logos.Alternatives

-- Axiom footprint audit
#print axioms Logos.Alternatives.T9_incompatibleAlternatives
#print axioms Logos.Alternatives.incompatible_with_negation
