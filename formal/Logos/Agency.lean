/-
# Logos.Agency — Level 2a: the act, its subject, its content (base.txt §1–§2, T1–T2, T4)

The performative datum of §1 (the present act of reasoning is *given*, not
inferred) is no longer declared here. A1 (2026-09-16): the former
`axiom cogito` (tagged TRANS) is deleted — it was already derivable from
`Plurality.cogito_from_T12`, and its existence content now lives in
Plurality (see below).

Design decision B1 (D-batch "act bundle", 2026-09-15): `A s p` is a *defined*
relation, not a primitive. The act is — by the meaning rules of the system
(base.txt §1–§15) — the bundle of its aspects:

    A s p  :=  Agent s ∧ Exists s ∧ Content p ∧ Rational s ∧ Means s p.

Tier-1 collapse (2026-09-16): with `Agent` and `Rational` now *analytical
definitions* (`def := True`, same class as `Exists`/`Content`), every aspect
collapses and the bundle reduces to the meaning-act:

    A s p  :=  Means s p.

The meaning rules are now exactly E0-furnished: every subject exists
(`Exists _ := True`), every proposition is a content (`Content _ := True`),
agency and rationality are analytical (`Agent _ := True`, `Rational _ := True`),
and the act IS meaning (`A s p := Means s p`). Prose consequence realized:
"deny meaning and you contradict yourself" is *structural* — the present act
is a meaning-act. Consequences:
  * the six former meaning postulates `act_implies_*` hold analytically;
  * T2 is a projection of the collapse (axiom-free);
  * the remaining primitives `Subject` and `Means` stay opaque (declared, not
    derived): `Subject` is a pure-sort postulate (its inhabitants are the
    claimed persons of T12 / `cogito_from_T12`; any carrier definition would
    smuggle content — `Bool`/`fin 2` asserts exactly-two, `ℕ` asserts
    infinity, an empty `inductive` refutes `∃ s` and breaks the act-datum),
    and `Means` is the genuine intentional relation.

The act-datum (`∃ s p, A s p`) is resident via `Plurality.cogito_from_T12`
(derived under the ultimate anchor `AxTwoSubjects`). Agency cannot import
Plurality (cycle `Plurality → Value → Person → Agency`), so the existence
theorems that used to stand on the axiom live in Plurality as T12 projections:
`Plurality.T1_subjectExists`, `Plurality.T4_agentExists`,
`Plurality.T5_personExists`. Only `T2_contentExists` remains here (axiom-free).
-/

import Logos.Core

namespace Logos.Agency

open Logos.Core (T)

/-- Subjects: that which performs acts of reasoning. -/
axiom Subject : Type

/-- Existence predicate: `Exists s` (propositional form of "s exists").
    Analytical definition (cogito-rethinking, 2026-09-15): every subject we
    ever encounter is the subject of an act, hence exists. Former axiom,
    now def. -/
def Exists (_s : Subject) : Prop := True

/-- Content-ness: `Content p` — p is (a) a propositional content.
    Analytical definition (cogito-rethinking, 2026-09-15): the universe of
    propositions IS the universe of possible contents. Former axiom, now def. -/
def Content (_p : Prop) : Prop := True

/-- Agency: `Agent s`. Analytical definition (Tier 1, 2026-09-16): agency is
    not an additional opaque predicate — a subject of the present act is
    *by being such* an agent. Former axiom, now def (same class as
    `Exists`/`Content`). -/
def Agent (_s : Subject) : Prop := True

/-- Rationality of a subject: the present act is rational by being the act of
    reasoning (base.txt §12, T5 component). Analytical definition (Tier 1,
    2026-09-16): former axiom, now def — the act of reasoning is rational by
    being the act of reasoning. -/
def Rational (_s : Subject) : Prop := True

/-- `Means s p`: subject s means (intentionally relates to) proposition p
    (base.txt §11, T5 component; moved here in B1, same reason). -/
axiom Means : Subject → Prop → Prop

/-- The act — the meaning-act (B1 bundle; Tier-1 collapse, 2026-09-16): the
    act's aspects `Agent`/`Exists`/`Content`/`Rational` are analytical
    definitions (`:= True`), so the Six former `act_implies_*` axioms
    collapse and the act IS the intentional relation `Means s p`. -/
def A (s : Subject) (p : Prop) : Prop := Means s p

/-- An act entails a subject that exists (relational act, §1/T1).
    Analytic (Tier 1): `Exists _ := True`. -/
theorem act_implies_exists : ∀ {s : Subject} {p : Prop}, A s p → Exists s := by
  intro s p h
  trivial

/-- An act entails content (nothing is asserted without something asserted, T2).
    Analytic (Tier 1): `Content _ := True`. -/
theorem act_implies_content : ∀ {s : Subject} {p : Prop}, A s p → Content p := by
  intro s p h
  trivial

/-- An act entails an agent (T4, §12). Analytic (Tier 1): `Agent _ := True`. -/
theorem act_implies_agent : ∀ {s : Subject} {p : Prop}, A s p → Agent s := by
  intro s p h
  trivial

/-- An act entails its subject is rational (T5 component). Analytic (Tier 1):
    `Rational _ := True`. -/
theorem act_implies_rational : ∀ {s : Subject} {p : Prop}, A s p → Rational s := by
  intro s p h
  trivial

/-- An act entails that its subject means its content (§11, T5 component).
    Under the Tier-1 collapse `A s p := Means s p` this is the identity. -/
theorem act_implies_means : ∀ {s : Subject} {p : Prop}, A s p → Means s p := by
  intro s p h
  exact h

/-- T2 — there is propositional content. Now axiom-free: `Content` is the
    analytical definition `Content _ := True`, so `True` itself witnesses
    content (cogito no longer needed). -/
theorem T2_contentExists : ∃ p : Prop, Content p :=
  ⟨True, trivial⟩

end Logos.Agency

-- Axiom footprint audit
#print axioms Logos.Agency.T2_contentExists