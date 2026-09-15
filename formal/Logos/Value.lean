/-
# Logos.Value — interpersonal value (poem P5/P6; the "ser sozinho" premise)

P6 of the poem: "um Ser sózinho pode agir de uma forma ou de outra, não ajuda
nem prejudica ninguém." Formal content:

  * `Affects` is the *single primitive* relation from one subject to another;
    `Helps`/`Harms` are its definitional projections (A3-refactor);
  * lemma `alone_no_other_help_harm`: a lone subject helps/harms no *other*
    subject (an other = a t with t ≠ s).

The poem's *leap* (P5, "para haver escolha com significado, é preciso mais do
que uma pessoa") — the reality of right-and-wrong is *interpersonal* — is NOT
derivable from the axioms alone (failure traces in DESIGN.md D14 + C3-I spike;
the named missing lemma is `ALONE_EXCLUDED : ¬ ∃ s, Person s ∧ Alone s`). The
former single bridge `AxValueInterpersonal` is split (C3-I, 2026-09-15) into
two narrower priced bridges: the **plurality-claim** `AxTwoSubjects` (META: from
right-and-wrong to two distinct persons) and the **affectivity meaning-postulate**
`AxPersonsAffect` (SEM: distinct persons, by definition, bear on each other).
`valueInterpersonal_of_split` recovers the exact old statement, so no strength
is lost. Neither bridge's negation destroys the act of denying it: both stay
priced, never pure deduction (§29).
-/

import Logos.Core
import Logos.Agency
import Logos.Person

namespace Logos.Value

open Logos.Agency (Subject)
open Logos.Person (Person)

/-- `Affects s t`: what `s` does bears on `t`. NOW the single primitive value
    relation (A3-refactor): `Helps`/`Harms` are its definitional *projections*
    (see below), faithful to P6 ("não ajuda nem prejudica ninguém" — the lone
    subject affects no other). -/
axiom Affects : Subject → Subject → Prop

/-- `Helps s t`: `s` benefits `t` — definitional projection of `Affects`
    (the helps-direction). -/
def Helps (s t : Subject) : Prop := Affects s t

/-- `Harms s t`: `s` harms `t` — definitional projection of `Affects`
    (the harms-direction). -/
def Harms (s t : Subject) : Prop := Affects s t

/-- Helping is a way of affecting (unfolds to the identity). -/
theorem help_affects : ∀ {s t : Subject}, Helps s t → Affects s t := by
  intro s t h
  exact h

/-- Harming is a way of affecting (unfolds to the identity). -/
theorem harm_affects : ∀ {s t : Subject}, Harms s t → Affects s t := by
  intro s t h
  exact h

/-- `OtherAffects s`: `s`'s doings bear on some *other* subject. -/
def OtherAffects (s : Subject) : Prop := ∃ t : Subject, t ≠ s ∧ Affects s t

/-- `Alone s`: there is no other subject (the only subject is `s`). -/
def Alone (s : Subject) : Prop := ∀ t : Subject, t = s

/-- P6, half 1 — a lone subject's doings affect no other. -/
theorem alone_no_other_affects {s : Subject} (ha : Alone s) : ¬ OtherAffects s := by
  intro h
  obtain ⟨t, hne, _⟩ := h
  exact hne (ha t)

/-- P6, whole — a lone subject helps no other AND harms no other. -/
theorem alone_no_other_help_harm {s : Subject} (ha : Alone s) :
    (¬ ∃ t : Subject, t ≠ s ∧ Helps s t) ∧ (¬ ∃ t : Subject, t ≠ s ∧ Harms s t) := by
  constructor
  · intro h
    obtain ⟨t, hne, hh⟩ := h
    exact hne (ha t)
  · intro h
    obtain ⟨t, hne, hh⟩ := h
    exact hne (ha t)

/-- AxTwoSubjects (META; poem P5/P7, failure traces in DESIGN.md D14 and
    spike x2_spikeA): the *reality* of right-and-wrong demands that there be
    at least two distinct persons. Narrower than the former single bridge
    `AxValueInterpersonal` (plurality only; affectivity is AxPersonsAffect).
    Exclusion attempt recorded in /tmp/opencode/x2_spikeA.lean: the lone-subject
    scenario `Alone s` is consistent with cogito + T6 + P6, so no contradiction
    is derivable; named missing lemma `ALONE_EXCLUDED`. -/
axiom AxTwoSubjects :
    (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) →
      ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂

/-- AxPersonsAffect (SEM meaning-postulate; poem P5/P7): distinct persons
    necessarily bear on each other — affectivity in at least one direction.
    Universal statement, asserts no existence. Consistency model: two-subject
    boolean structure {present, other} with a mandatory directed affects edge.
    Exclusion attempt recorded in /tmp/opencode/x2_spikeB.lean: `Affects` has
    no introduction rule, so the claim is unprovable from the theory. -/
axiom AxPersonsAffect : ∀ s₁ s₂ : Subject, Person s₁ → Person s₂ → s₁ ≠ s₂ →
    (Affects s₁ s₂ ∨ Affects s₂ s₁)

/-- Recovery theorem: the exact statement of the deleted `AxValueInterpersonal`
    (line 70-73, 2026-09-14) is a theorem of the split — no strength lost. -/
theorem valueInterpersonal_of_split :
    (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) →
      ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
        (Affects s₁ s₂ ∨ Affects s₂ s₁) := by
  intro h
  obtain ⟨s₁, s₂, hs₁, hs₂, hne⟩ := AxTwoSubjects h
  exact ⟨s₁, s₂, hs₁, hs₂, hne, AxPersonsAffect s₁ s₂ hs₁ hs₂ hne⟩

end Logos.Value

-- Axiom footprint audit
#print axioms Logos.Value.alone_no_other_help_harm
#print axioms Logos.Value.valueInterpersonal_of_split