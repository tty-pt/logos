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

/-- Intentional Subject: a subject who means some propositional content (§11).
    Purely definitional from the primitive `Means` relation. -/
def IntentionalSubject (s : Subject) : Prop := ∃ p : Prop, Means s p

/-- Backward-compatibility alias for intentionality. -/
def Intentional (s : Subject) : Prop := IntentionalSubject s

/-- Substantive personal feature: independent uninterpreted property
    representing a rational, deliberative personal center. -/
opaque SubstantivePerson : Subject → Prop

/-- Person: substantive metaphysical personhood (base.txt §12 / theorem T5).
    Requires both intentional directedness and substantive personal agency.
    Decoupled from degenerate analytical identities (`Agent := True`, `Rational := True`). -/
def Person (s : Subject) : Prop := IntentionalSubject s ∧ SubstantivePerson s

/-- Every substantive metaphysical person is an intentional subject:
    personhood entails intentional directedness at propositional content. -/
theorem person_is_intentional (s : Subject) (h : Person s) : IntentionalSubject s :=
  h.1

/-- Act implies an intentional subject: an act's own content witnesses that the subject
    means something (`IntentionalSubject s := ∃ p, Means s p`) — a definitional
    identity, not a semantic discovery.
    Footprint: `{Means, Subject}` (VOCAB). -/
theorem act_implies_intentionalSubject {s : Subject} {p : Prop} (h : Logos.Agency.Act s p) :
    IntentionalSubject s :=
  ⟨p, h.1⟩

theorem act_implies_intentional {s : Subject} {p : Prop} (h : Logos.Agency.Act s p) :
    Intentional s :=
  act_implies_intentionalSubject h

/-- An actualized subject of an act is an intentional subject.
    Footprint: `{Initiates, Means, State, Subject}` (VOCAB). -/
theorem subjectExists_implies_intentionalSubject (h : Logos.Agency.SubjectExists s) :
    IntentionalSubject s := by
  obtain ⟨p, ha⟩ := h
  exact ⟨p, ha.1⟩

theorem subjectExists_implies_intentional (h : Logos.Agency.SubjectExists s) :
    Intentional s :=
  subjectExists_implies_intentionalSubject h

/-- Under a bridge from meaning to initiation, intentionality implies SubjectExists. -/
theorem intentional_implies_subjectExists_of_bridge
    (hBridge : ∀ (s : Subject) (p : Prop), Logos.Agency.Means s p → ∃ w w' : Logos.Agency.State, Logos.Agency.Initiates s w w' p)
    (h : IntentionalSubject s) : Logos.Agency.SubjectExists s := by
  obtain ⟨p, hm⟩ := h
  exact ⟨p, hm, hBridge s p hm⟩

/-- The existence of an act entails that an intentional subject exists (formerly nominal T5).
    Footprint: `{Initiates, Means, State, Subject}` (VOCAB). -/
theorem intentionalSubject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ s : Subject, IntentionalSubject s := by
  obtain ⟨s, p, ha⟩ := h
  exact ⟨s, act_implies_intentionalSubject ha⟩

/-- Backward-compatibility alias for intentional subject existence. -/
theorem intentional_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :
    ∃ s : Subject, Intentional s :=
  intentionalSubject_exists_of_act h

/-- An assertion entails that an intentional subject exists.
    Footprint: `{Initiates, Means, State, Subject}`. -/
theorem intentionalSubject_exists_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) :
    ∃ s' : Subject, IntentionalSubject s' :=
  ⟨s, act_implies_intentionalSubject (Logos.Agency.assertion_is_act h)⟩

/-- Backward-compatibility alias for intentionality from assert. -/
theorem intentional_exists_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) :
    ∃ s' : Subject, Intentional s' :=
  intentionalSubject_exists_of_assert h

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
#print axioms Logos.Person.act_implies_intentionalSubject
#print axioms Logos.Person.subjectExists_implies_intentionalSubject
#print axioms Logos.Person.intentionalSubject_exists_of_act
#print axioms Logos.Person.person_is_intentional
