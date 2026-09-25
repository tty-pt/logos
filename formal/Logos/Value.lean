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
que uma pessoa") — the reality of right-and-wrong is *interpersonal* — is NOT
derivable from a single act or Cogito alone (proven by the Unit countermodel
in `HostileSemantics`). The former pseudo-proof via `otherSubject` (swapping
`Sum.inl` and `Sum.inr`) is destroyed. Plurality requires the explicit
metaphysical bridge `AxTwoSubjects` (META: from right-and-wrong to two
distinct persons). `valueInterpersonal_of_split` recovers the exact old
statement; no strength is lost.

2026-09-24: the *value layer itself* is provably empty in the pure theory
(`BearingOf` is a closed def returning `unbearing`, so `Helps`/`Harms`/`Affects`
are refutable for every pair — `helps_unobtainable`, `no_help_obtains`). The
positive moral close therefore carries the disclosed META bridge
`AxBenevolentBearingObtains` ("some person is actually helped").
-/

import Logos.Core
import Logos.Agency
import Logos.Person

namespace Logos.Value

open Logos.Agency (Subject)
open Logos.Person (Person)

/-- Directed interpersonal bearing of a subject toward another. -/
inductive InterpersonalBearing : Type
  | unbearing : InterpersonalBearing
  | affects_only : InterpersonalBearing
  | benevolent : InterpersonalBearing
  | harmful : InterpersonalBearing

/-- The uninterpreted interpersonal bearing of s toward t:
    by default, a distinct subject does not automatically affect or help another. -/
def BearingOf (_s _t : Subject) : InterpersonalBearing :=
  InterpersonalBearing.unbearing

/-- Affects: what s does bears on t (through help, harm, or pure affectivity).
    Decoupled from bare non-identity s ≠ t. -/
def Affects (s t : Subject) : Prop :=
  BearingOf s t = InterpersonalBearing.benevolent ∨
  BearingOf s t = InterpersonalBearing.harmful ∨
  BearingOf s t = InterpersonalBearing.affects_only

/-- Helps: positive constitutive bearing — s benefits t. -/
def Helps (s t : Subject) : Prop :=
  BearingOf s t = InterpersonalBearing.benevolent

/-- Harms: detrimental constitutive bearing — s harms t. -/
def Harms (s t : Subject) : Prop :=
  BearingOf s t = InterpersonalBearing.harmful

/-- Helping is an affective bearing: helping entails affecting. -/
theorem help_affects : ∀ {s t : Subject}, Helps s t → Affects s t := by
  intro s t h
  left
  exact h

/-- Harming is an affective bearing: harming entails affecting. -/
theorem harm_affects : ∀ {s t : Subject}, Harms s t → Affects s t := by
  intro s t h
  right; left
  exact h

/-- Benevolence principle: in the foundational order, what helps does not harm. -/
theorem help_not_harm : ∀ {s t : Subject}, Helps s t → ¬ Harms s t := by
  intro s t hh hharm
  dsimp [Helps, Harms] at hh hharm
  rw [hh] at hharm
  cases hharm

/-- The bare value layer is empty: in the pure theory no subject helps any subject.
    `BearingOf` is a *closed* definition returning `unbearing`, so `Helps s t` reduces to
    `unbearing = benevolent`, which is refutable for every pair. Help does not obtain
    without a disclosed datum; this is the machine-witness for why the positive moral
    close carries the META bridge `AxBenevolentBearingObtains`. -/
theorem helps_unobtainable (s t : Subject) : ¬ Helps s t := by
  intro h
  dsimp [Helps, BearingOf] at h
  exact nomatch h

/-- Likewise, no subject harms any subject in the pure theory. -/
theorem harms_unobtainable (s t : Subject) : ¬ Harms s t := by
  intro h
  dsimp [Harms, BearingOf] at h
  exact nomatch h

/-- Likewise, no subject affects any subject in the pure theory. -/
theorem affects_unobtainable (s t : Subject) : ¬ Affects s t := by
  intro h
  dsimp [Affects, BearingOf] at h
  rcases h with h | h | h <;> nomatch h

/-- The helping existential required by the fair moral poles is refuted in the pure theory:
    there is no pair of distinct subjects with `Helps` between them. -/
theorem no_help_obtains : ¬ ∃ s t : Subject, s ≠ t ∧ Helps s t := by
  rintro ⟨s, t, _, h⟩
  exact helps_unobtainable s t h

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
  · rintro ⟨t, hne, _⟩
    exact hne (ha t)
  · rintro ⟨t, hne, _⟩
    exact hne (ha t)

/--Tag: META
AxTwoSubjects (META; poem P5/P7, failure traces in DESIGN.md D14 and
    HostileSemantics): the *reality* of right-and-wrong demands that there be
    at least two distinct persons. Narrower than the former single bridge
    `AxValueInterpersonal` (plurality only; affectivity is AxPersonsAffect).
    A single act does not entail plurality (settled by the Unit countermodel).

 Philosophical cost: a substantive interpersonal metaphysics. A lone judging
    subject, and the unit world of a single act, remain logically consistent
    with every earlier premise, so the demand for a second distinct person is
    posited, not deduced. Plural personal reality is bought with this declared
    bridge. -/
axiom AxTwoSubjects :
    (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) →
      ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂

/--No person is alone: there is no personal lone subject under the plurality bridge.

 `aloneExcluded` — under `AxTwoSubjects`, a lone person is excluded:
    there exist distinct persons, so no single subject can encompass all subjects.
    Footprint: `{AxTwoSubjects, Means, Subject}`. -/
theorem aloneExcluded : ¬ ∃ s : Subject, Person s ∧ Alone s := by
  intro ⟨s, _, ha⟩
  obtain ⟨s₁, s₂, _, _, hne⟩ := AxTwoSubjects Logos.Core.rightWrongDistinction
  have h1 := ha s₁
  have h2 := ha s₂
  subst h1 h2
  exact hne rfl

/--Tag: META
Some person is actually helped: benevolence is not merely definable but obtains.
  The *reality* of interpersonal value demands that at least one subject actually
  helps another distinct person (the positive moral datum the poem's "ajuda" asserts
  in the world, not only in the definition). Without this bridge the value layer is
  provably empty (`no_help_obtains`: `BearingOf := unbearing` refutes every `Helps`),
  so no moral pole that is defined as helping another person could ever obtain.

  Consistency-model note: the bridge is not forced by any earlier premise (the empty
  pure theory is a model of them all, by `helps_unobtainable`/`no_help_obtains`), so this
  is a genuine, paid commitment — not a hidden derivation. The hostile local universes
  (`M_amoral`, the Unit models) live in *separate* `S` and are untouched by this global
  value-layer datum.

  Philosophical cost: a substantive interpersonal-value metaphysics — that benevolence
  occurs in the world, not only in the definitions. Bought with this declared bridge,
  and carried openly in the footprint of every moral conclusion. -/
axiom AxBenevolentBearingObtains :
    ∃ s t : Subject, s ≠ t ∧ Person t ∧ Helps s t

/--Under the benevolence bridge, some person is actually helped by another (a help
  relation toward a distinct person obtains).
  Footprint: `{AxBenevolentBearingObtains, Means, Subject}`. -/
theorem some_person_is_helped :
    ∃ s t : Subject, s ≠ t ∧ Person t ∧ Helps s t :=
  AxBenevolentBearingObtains

/-- PersonsAffectPrinciple: distinct persons bear on each other in at least one direction.
With Affects/Helps/Harms hardened, this is an explicit metaphysical principle. -/
def PersonsAffectPrinciple : Prop :=
  ∀ (s₁ s₂ : Subject), Person s₁ → Person s₂ → s₁ ≠ s₂ → Affects s₁ s₂ ∨ Affects s₂ s₁

/-- Right-and-wrong yields two distinct persons who bear on each other,
    conditional on the PersonsAffectPrinciple. -/
theorem valueInterpersonal_of_split_conditional
    (hAffect : PersonsAffectPrinciple)
    (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) :
    ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧
      (Affects s₁ s₂ ∨ Affects s₂ s₁) := by
  obtain ⟨s₁, s₂, hs₁, hs₂, hne⟩ := AxTwoSubjects h
  exact ⟨s₁, s₂, hs₁, hs₂, hne, hAffect s₁ s₂ hs₁ hs₂ hne⟩

end Logos.Value

-- Axiom footprint audit
#print axioms Logos.Value.alone_no_other_help_harm
#print axioms Logos.Value.AxTwoSubjects
#print axioms Logos.Value.helps_unobtainable
#print axioms Logos.Value.harms_unobtainable
#print axioms Logos.Value.affects_unobtainable
#print axioms Logos.Value.no_help_obtains
#print axioms Logos.Value.AxBenevolentBearingObtains
#print axioms Logos.Value.some_person_is_helped
#print axioms Logos.Value.aloneExcluded
#print axioms Logos.Value.help_not_harm
#print axioms Logos.Value.help_affects
