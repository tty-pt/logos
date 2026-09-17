/-
# Logos.Value — interpersonal value (poem P5/P6; the "ser sozinho" premise)

P6 of the poem: "um Ser sózinho pode agir de uma forma ou de outra, não ajuda
nem prejudica ninguém." Formal content:

  * `Affects` is now a *structural definition* (A3, M1 batch of
    `FORCED_SUBJECT.md`, 2026-09-15→16): bearing = distinctness
    (`Affects s t := s ≠ t`); `Helps`/`Harms` are its definitional
    projections; faithful to P6 ("não ajuda nem prejudica ninguém" — the lone
    subject affects no other);
  * lemma `alone_no_other_help_harm`: a lone subject helps/harms no *other*
    subject (an other = a t with t ≠ s). Now carries no `Affects` axiom.

The poem's *leap* (P5, "para haver escolha com significado, é preciso mais do
que uma pessoa") — the reality of right-and-wrong is *interpersonal* — is now
DERIVED, not priced (plurality-discharge, 2026-09-17): the named missing lemma
`ALONE_EXCLUDED : ¬ ∃ s, Person s ∧ Alone s` is a theorem (`aloneExcluded` —
no subject is alone, because the definitional subject has ≥2 inhabitants), and
`Person.twoPersonsFromSubject` exhibits the canonical pair (origin + addressee)
with no axiom. History: the former single bridge `AxValueInterpersonal` was
split (C3-I, 2026-09-15) into plurality (`AxTwoSubjects`, META) + affectivity
(`AxPersonsAffect`, SEM); M1 (2026-09-16) folded the SEM half into A3;
`AxTwoSubjects` is RETIRED here — its content moved into the definition of a
subject (Unit ⊕ Prop), the M2 countermodel is superseded, and the old M2 spike
`formal/Spikes/Spike_A4_2.lean` is void. `valueInterpersonal_of_split` still
recovers the exact old statement; no strength is lost.
-/

import Logos.Core
import Logos.Agency
import Logos.Person

namespace Logos.Value

open Logos.Agency (Subject)
open Logos.Person (Person)

/-- `Affects s t`: what `s` does bears on `t`. NOW a structural DEFINITION
    (A3, batch M1 of `FORCED_SUBJECT.md`, 2026-09-16): bearing = distinctness —
    a subject bears on what is *other*; the lone subject bears on nothing
    (P6: "não ajuda nem prejudica ninguém"). `Helps`/`Harms` are its
    definitional *projections* (see below).

    This is a SEM *position*, recorded and owned (same class as A2's structural
    `TrueAt`): it defines the minimal structural content of affectivity, it
    does not pretend to *derive* it. The former two-declaration swing
    (`axiom Affects` + `axiom AxPersonsAffect`) collapses to zero.

    Prose price: "Amar é escolhido" now rests entirely on `FreeWill` (F1,
    DEFERRED); `Loves := Affects` in Love.lean reads as the directed
    constitutive bearing of one subject on a *distinct* one. -/
def Affects (s t : Subject) : Prop := s ≠ t

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

/--A lone subject neither helps nor harms anyone else.

 P6, whole — a lone subject helps no other AND harms no other. -/
theorem alone_no_other_help_harm {s : Subject} (ha : Alone s) :
    (¬ ∃ t : Subject, t ≠ s ∧ Helps s t) ∧ (¬ ∃ t : Subject, t ≠ s ∧ Harms s t) := by
  constructor
  · intro h
    obtain ⟨t, hne, hh⟩ := h
    exact hne (ha t)
  · intro h
    obtain ⟨t, hne, hh⟩ := h
    exact hne (ha t)

/--The other of a subject: a distinct subject the field always supplies.

 `otherSubject`: given `s`, a subject guaranteed to be *other* than `s` — the
    definitional field provides it (`Unit ⊕ Prop` has at least two inhabitants):
    if `s` is the origin, `Sum.inr True`; if `s` is a posited content,
    `Sum.inl ()`. This is the seed of `neverAlone`/`aloneExcluded`. -/
def otherSubject (s : Subject) : Subject :=
  match s with
  | Sum.inl _ => Sum.inr True
  | Sum.inr _ => Sum.inl ()

/--`otherSubject` really is other: no subject equals its other.

  The definitional field makes solipsism structurally impossible — for every
    subject there is a distinct one, by constructors. Footprint: `{}`. -/
theorem otherSubject_ne (s : Subject) : otherSubject s ≠ s := by
  intro h
  cases s with
  | inl _ => cases h
  | inr _ => cases h

/--No subject is alone: for every `s` there is a distinct subject.

  `neverAlone s` — `¬ Alone s` for every subject: the negation of
    `Alone s` (`∀ t, t = s`) by exhibiting `otherSubject s ≠ s`. This kills
    the M2 lone-subject countermodel: no consistency model for a single
    subject exists under the definitional `Subject`. Footprint: `{}`. -/
theorem neverAlone (s : Subject) : ¬ Alone s := by
  intro h
  exact otherSubject_ne s (h (otherSubject s))

/--No person is alone: there is no personal lone subject.

 `aloneExcluded` — the formerly-named missing lemma
    `ALONE_EXCLUDED : ¬ ∃ s, Person s ∧ Alone s` (M2), now a theorem: a lone
    subject is a logical impossibility under the definitional subject, a
    fortiori a lone *person*. Footprint: `{}`. -/
theorem aloneExcluded : ¬ ∃ s : Subject, Person s ∧ Alone s := by
  intro ⟨s, _, hA⟩
  exact neverAlone s hA

/-- AxPersonsAffect (theorem of A3, M1 2026-09-16; formerly a SEM
    meaning-postulate): distinct persons necessarily bear on each other in at
    least one direction — because bearing IS distinctness, `hne : s₁ ≠ s₂`
    is the left disjunct itself. This formerly stood as a declared axiom
    (`axiom` with no introduction rule; exclusion attempt in
    /tmp/opencode/x2_spikeB.lean); the A3 definition supplies the missing
    introduction rule. -/
theorem AxPersonsAffect (s₁ s₂ : Subject) (_hs₁ : Person s₁) (_hs₂ : Person s₂)
    (hne : s₁ ≠ s₂) : Affects s₁ s₂ ∨ Affects s₂ s₁ :=
  Or.inl hne

/--Right-and-wrong yields two distinct persons who bear on each other.

  Recovery theorem: the exact statement of the deleted `AxValueInterpersonal`
    (line 70-73, 2026-09-14) is a theorem of the split — no strength lost.
    Now derived outright (definitional subject, 2026-09-17): the canonical
    pair of `Person.twoPersonsFromSubject` needs no right-and-wrong premise. -/
theorem valueInterpersonal_of_split :
    (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) →
      ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
        (Affects s₁ s₂ ∨ Affects s₂ s₁) := by
  intro _
  obtain ⟨s₁, s₂, hs₁, hs₂, hne⟩ := Logos.Person.twoPersonsFromSubject
  exact ⟨s₁, s₂, hs₁, hs₂, hne, AxPersonsAffect s₁ s₂ hs₁ hs₂ hne⟩

end Logos.Value

-- Axiom footprint audit
#print axioms Logos.Value.alone_no_other_help_harm
#print axioms Logos.Value.otherSubject_ne
#print axioms Logos.Value.neverAlone
#print axioms Logos.Value.aloneExcluded
#print axioms Logos.Value.valueInterpersonal_of_split
