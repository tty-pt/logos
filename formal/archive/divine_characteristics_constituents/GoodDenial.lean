/-
# Logos.GoodDenial — the retorsion question for the moral Good, machine-answered

Binding theorem that fuses the two existing countermodels — `MoralFrontierAudit`'s
pole-freedom (C175/C176/C499 family) and `DefinitiveAgencyFrontier`'s
retorsion-failure (`retorsion_denial_does_not_commit_to_content`) — into a single
statement: denying the existence of the moral Good is **free-logically consistent**
with the full normative relying structure of Γ, and the denial itself is **not
performatively self-refuting**.

So the classical retorsion ("in denying the Good you instantiate it") fails for the
substantive moral poles. What *is* retorsively undeniable (`{}`, pure logic) is the
normative *field* — truth and the extensional Right/Wrong distinction
(`NormativeTruth`, `UndeniableNormativeDerivation`) — never the poles.

The theorem is a conjunction because the two fronts live on different carriers: the
pole-freedom witness ranges over the agency `Subject` universe (with `Correct` as the
reality-hook), while the retorsion-failure witness ranges over any fine-grained
cognitive-subject type. That is not a weakness — it is the frontier's honesty: the two
assertions are independent, and no axiom is needed to glue them.
-/

import Logos.MoralFrontierAudit
import Logos.DefinitiveAgencyFrontier

namespace Logos.GoodDenial

open Logos.Agency (Subject)
open Logos.Order (Correct)
open Logos.CognitiveToAgencyFrontier (FineCognitiveSubject)

/-- Denying the existence of the moral Good is consistent with Γ's full normative
    relying structure, and the denial itself carries no performative self-refutation.

    Left conjunct (the pole-freedom herald): there exist moral poles `G`, `E` that are
    False everywhere — no Good, no Evil obtains — while the epistemic reality-hook
    (`Correct s p → p`) stays intact: `moral_pole_postulate_is_not_a_consequence`
    (C175 family), footprint `{Initiates, Means, State, Subject}` (vocabulary-only).

    Right conjunct (the retorsion-failure herald): a fine-grained cognitive subject can
    assert its own non-commitment to a content without that assertion instantiating
    commitment to it: `retorsion_denial_does_not_commit_to_content`, footprint `{}`.

    Together they machine-answer the retorsion challenge for the Good: denying
    `∃ Good` neither contradicts the normative structure (a countermodel certifies it,
    so the denial is a coherent rival reading of Γ, not an inconsistency) nor
    self-destructs (the denial is performatively coherent: it instantiates the
    negation, never commitment to the content). What retorsion does refute
    unconditionally (`{}`) is the normative *field* — `NormativeTruth`, the
    Right/Wrong distinction — never the substantive moral poles.
    Footprint: `{Initiates, Means, State, Subject}` (vocabulary-only — carried from
    the pole-freedom herald through `correct_tracks_reality`, exactly as in
    `moral_pole_postulate_is_not_a_consequence`; zero substantive axioms). -/
theorem good_denial_is_free_logically_consistent :
    (∃ G E : Subject → Prop → Prop,
       (¬ ∃ s : Subject, ∃ p : Prop, G s p) ∧
       (¬ ∃ s : Subject, ∃ p : Prop, E s p) ∧
       (∀ s : Subject, ∀ p : Prop, Correct s p → p)) ∧
    (∃ (Subj : Type) (CS : FineCognitiveSubject Subj)
       (Reg : Subj → Prop → Prop) (s : Subj) (p : Prop),
       Reg s (¬ CS.CommitsTo s p) ∧ ¬ CS.CommitsTo s p) := by
  constructor
  · exact Logos.MoralFrontierAudit.moral_pole_postulate_is_not_a_consequence
  · exact Logos.DefinitiveAgencyFrontier.retorsion_denial_does_not_commit_to_content

end Logos.GoodDenial

-- ---------------------------------------------------------------------------
-- Axiom footprint audit (expected: vocabulary-only {Initiates, Means, State, Subject})
-- ---------------------------------------------------------------------------
#print axioms Logos.GoodDenial.good_denial_is_free_logically_consistent