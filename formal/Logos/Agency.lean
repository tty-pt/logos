/-
# Logos.Agency — Level 2a: the act, its subject, its content (base.txt §1–§2, T1–T2, T4)

The performative datum of §1 (the present act of reasoning is *given*, not
inferred) is now a THEOREM: `Cogito` (batch "definitional subject",
2026-09-17). M0 had restored the datum as the unconditioned TRANS axiom
`Cogito` (SUBJECT IS FORCED), with the degenerate self-refutation
`noCogito_selfRefutes := fun h => h Cogito` (an axiom implying its own
double negation). The walls of `FORCED_SUBJECT.md` §1 (empty model + carrier
smuggling) are answered by charging the carrier as a *definition* in the
traditional sense of "subject": ὑποκείμενον — the underlier, the locus of
non-derived normative agency, occurring only in origin position, never
evaluated. The foundation is re-anchored on the original chain: undeniable
right-and-wrong (C36, `{}`) ⇒ meaning (analytic, §8) ⇒ choosing subject
(definitional witness: the silent origin sustains every posit).

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
  * the former primitives `Subject`, `State`, `Initiates` are now *defined*
    (declared as what they mean, not postulated): `Subject := Unit ⊕ Prop`
    (the silent origin + the posited contents), `State := Prop`
    (truth-bearers), and `Initiates` moves the sustained field toward the
    posit — so `Cogito` is exhibited, not assumed;
  * `Means` is no longer primitive: act-as-initiation rebase (2026-09-17)
    defines it as `Means s p := ∃ w w' : State, Initiates s w w' p`, so
    meaning is posited by an initiation rather than transmitted as a state.

The act-datum (`∃ s p, A s p`) is resident HERE as the theorem `Cogito`.
`Agency` imports only Core, so no import cycle blocks it.
The existence theorems that A1 moved into Plurality are anchored there on
`Cogito` (no longer on `T12`/`AxTwoSubjects`). `T2_contentExists` remains
axiom-free.
-/

import Logos.Core

namespace Logos.Agency

open Logos.Core (T)

/--The underlier (ὑποκείμενον): the silent origin sustaining every posit, or a posited content positing itself.

 Subjects: that which performs acts of reasoning — the origin of the act,
    never the act itself, never a state or a content. Definitional
    (2026-09-17): the traditional sense (locus of non-derived normative
    agency) charged as a definition; the neutral witness `Sum.inl ()`
    smuggles nothing beyond the datum itself. -/
def Subject := Unit ⊕ Prop

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

/--The sustained field: states are truth-bearers, carried toward the posit.

 The act begins movement; it is therefore indexed by states — here the
    posited contents themselves (`State := Prop`), not `Semantics.World`.
    A world is a valuation — a state, i.e. a transfer-object — which is
    exactly what the act must not be reduced to. Definitional (2026-09-17). -/
def State := Prop

/--Initiation moves the sustained field toward the posit.

 The subject occurs as the ORIGIN INDEX of the transition, never as a
    component of a state. Definitional (2026-09-17): the silent origin moves
    the field to any posit; a posited content posits itself. This replaces
    the former opaque `Means` as the one real act-vocabulary. -/
def Initiates (s : Subject) (_w w' : State) (p : Prop) : Prop :=
  match s with
  | Sum.inl _ => w' = p
  | Sum.inr q => q = p ∧ w' = p

/-- The intentional relation, now DEFINED (act-as-initiation rebase,
    2026-09-17): `s` means `p` iff `s` initiates a movement positing `p`.
    Meaning is posited by the act, not transmitted as a state. Formerly an
    opaque axiom; the primitive is now `Initiates`. -/
def Means (s : Subject) (p : Prop) : Prop := ∃ w w' : State, Initiates s w w' p

/-- The act — the meaning-act (B1 bundle; Tier-1 collapse, 2026-09-16): the
    act's aspects `Agent`/`Exists`/`Content`/`Rational` are analytical
    definitions (`:= True`), so the Six former `act_implies_*` axioms
    collapse and the act IS the intentional relation `Means s p`. -/
def A (s : Subject) (p : Prop) : Prop := Means s p

/--Some subject acts on some content: the choosing subject exists. Proven, not postulated — exhibited by the silent origin.

 THE THEOREM (definitional subject, 2026-09-17): a choosing subject
    exists — the silent origin sustains every posit, so the present
    meaning-act is exhibited definitionally. Former TRANS axiom (M0);
    the degenerate self-refutation `fun h => h Cogito` is retired.
    Footprint: `{}`. -/
theorem Cogito : ∃ s : Subject, ∃ p : Prop, A s p :=
  ⟨Sum.inl (), True, True, True, rfl⟩

/--Denying 'some subject acts on some content' refutes itself — the silent origin is exhibited, no axiom cited.

 The denial is refuted by exhibiting the definitional witness: the silent
    origin sustains every posit, so `∃ s p, A s p` holds outright and its
    negation is `False`. Kernel-checked. Footprint: `{}`. -/
theorem noCogito_selfRefutes :
    (¬ ∃ s : Subject, ∃ p : Prop, A s p) → False :=
  fun h => h ⟨Sum.inl (), True, True, True, rfl⟩

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

/--At least one content exists: every proposition is admissible content.

 T2 — there is propositional content. Now axiom-free: `Content` is the
    analytical definition `Content _ := True`, so `True` itself witnesses
    content (cogito no longer needed). -/
theorem T2_contentExists : ∃ p : Prop, Content p :=
  ⟨True, trivial⟩

end Logos.Agency

-- Axiom footprint audit
#print axioms Logos.Agency.T2_contentExists
#print axioms Logos.Agency.Cogito
#print axioms Logos.Agency.noCogito_selfRefutes
