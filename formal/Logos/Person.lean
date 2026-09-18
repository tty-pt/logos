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

Under hostile semantics, propositional content does NOT imply personhood,
and a single act does not entail plurality. The pseudo-theorems
`twoPersonsFromSubject`, `everyContentIsAPerson`, and `positedDistinct`
are retired as conflations of definitions with proofs.

Personhood frontier (2026-09-18, PLAN_C24_PERSONHOOD.md): the chain
`Act → SubjectExists → Intentional → Person` is a chain of *definitional
identities* — every node unfolds to `∃ p, Means s p` (since
`Act s p := Means s p`, `SubjectExists s := ∃ p, Act s p`,
`Intentional s := ∃ p, Means s p`, and `Person s := Agent s ∧ Rational s ∧
Intentional s` with `Agent := True`, `Rational := True`). The bridge lemmas
below state these identities explicitly instead of hiding them inside
`person_of_act`. Formal derivability (`{Means, Subject}`) is therefore
NOT semantic neutrality of the definition: the §12 label "person" is a
constitutive commitment, and any *substantive* reading of personhood
(deliberation, moral responsibility, self-reflection, autonomous rational
choice) is not established by the performative datum (see
`HostileSemantics.Part A2`).
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

/-- Act implies intentionality: an act's own content witnesses that the subject
    means something (`Intentional s := ∃ p, Means s p`) — a definitional
    identity, not a semantic discovery (PLAN_C24_PERSONHOOD.md).
    Footprint: `{Means, Subject}` (VOCAB). -/
theorem act_implies_intentional {s : Subject} {p : Prop} (h : Logos.Agency.Act s p) :
    Intentional s :=
  ⟨p, h⟩

/-- SubjectExists is definitionally Intentional: both are `∃ p, Means s p`
    (Agency.SubjectExists s := ∃ p, Act s p, Act s p := Means s p) — direct
    identity. Footprint: `{Means, Subject}` (VOCAB). -/
theorem subjectExists_implies_intentional (h : Logos.Agency.SubjectExists s) : Intentional s :=
  h

/-- Intentionality is definitionally SubjectExists (converse of the same
    identity). Footprint: `{Means, Subject}` (VOCAB). -/
theorem intentional_implies_subjectExists (h : Intentional s) : Logos.Agency.SubjectExists s :=
  h

/--The §12 bridge made explicit: `Person ↔ Intentional` is exactly the current
    ontology (`Agent` and `Rational` are analytically `True`) — in Logos
    personhood is *nominal*, it adds no property beyond being an actualized
    meaning-subject. Direct unfolding, weakest proof.
    Footprint: `{Means, Subject}` (VOCAB). -/
theorem person_intentional_iff (s : Subject) : Person s ↔ Intentional s :=
  ⟨fun h => h.2.2, fun h => ⟨trivial, trivial, h⟩⟩

/-- Arrow 2 (Case A: Merely Definitional under §12 structural definition):
    Bridge from subject actuality to personhood.

    Audit notice (2026-09-18, personhood frontier): this implication is
    NOMINAL/CONSTITUTIVE, not an independent metaphysical discovery. Under the
    §12 structural definition of Person (`Person s := Agent s ∧ Rational s ∧
    Intentional s`, with `Agent := True`, `Rational := True`), personhood
    collapses to intentional agency (`∃ p, Means s p`), which is definitionally
    IDENTICAL to `SubjectExists s` — see `subjectExists_implies_intentional`,
    `intentional_implies_subjectExists`, `person_intentional_iff`. The
    performative datum thereby forces exactly the *actualized meaning-subject*;
    it does NOT establish substantive personhood (deliberation, responsibility,
    self-reflection, autonomous rational choice): formal derivability ≠
    semantic neutrality of the definition. Under hostile semantics where
    Person is an independent substantive predicate, this implication does NOT
    follow, as proved by `CountermodelSubjectWithoutPerson`
    (`not_entails_person`, HostileSemantics Part A / A2). -/
theorem person_of_subject {s : Subject} (h : Logos.Agency.SubjectExists s) : Person s :=
  ⟨trivial, trivial, h⟩

/-- An act directly yields a person — nominal consequence of the §12
    definitional collapse (Act → SubjectExists → Person is identity, see
    `act_implies_intentional`/`person_intentional_iff`), NOT independent
    evidence of substantive personhood. Footprint: `{Means, Subject}`. -/
theorem person_of_act {s : Subject} {p : Prop} (h : Logos.Agency.Act s p) : Person s :=
  person_of_subject ⟨p, h⟩

/-- The existence of an act entails that a person exists — formally valid
    under the current §12 constitutive definition (Person = Intentional =
    ∃ p, Means s p); the substantive notion of personhood is not
    independently established by this proof. Footprint: `{Means, Subject}`. -/
theorem person_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ s : Subject, Person s := by
  obtain ⟨s, p, ha⟩ := h
  exact ⟨s, person_of_act ha⟩

/-- An assertion entails that a person exists — same nominal §12 reading as
    `person_exists_of_act`. Footprint: `{Means, Subject}`. -/
theorem person_exists_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) :
    ∃ s' : Subject, Person s' :=
  ⟨s, person_of_act (Logos.Agency.assertion_is_act h)⟩

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
#print axioms Logos.Person.act_implies_intentional
#print axioms Logos.Person.subjectExists_implies_intentional
#print axioms Logos.Person.intentional_implies_subjectExists
#print axioms Logos.Person.person_intentional_iff
#print axioms Logos.Person.person_of_subject
#print axioms Logos.Person.person_of_act
#print axioms Logos.Person.person_exists_of_act
#print axioms Logos.Person.person_exists_of_assert
