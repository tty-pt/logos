/-
# Logos.Agency — Level 2a: the act, its subject, its content (base.txt §1–§2, T1–T2, T4)

The performative datum of §1 (the present act of reasoning is *given*, not
inferred) is the performative foundation of the system: `Cogito` (TRANS).
Reconstructed under hostile semantics: the occurrence of an act is a
performative datum, not a theorem of pure mathematics. It is not proved by
manufacturing a witness constructor (such as `Sum.inl ()`), but declared as
the unconditioned transcendental datum whose denial is self-refuting
(`noCogito_selfRefutes`).

Design decision B1 (D-batch "act bundle", 2026-09-15): `A s p` is a *defined*
relation, not a primitive. The act is — by the meaning rules of the system
(base.txt §1–§15) — the bundle of its aspects:

    A s p  :=  Agent s ∧ Exists s ∧ Content p ∧ Rational s ∧ Means s p.

Tier-1 collapse (2026-09-16) and initiation dimension: with `Agent` and
`Rational` now *analytical definitions* (`def := True`, same class as `Exists`/`Content`),
every aspect collapses to the meaningful initiation:

    A s p  :=  Means s p ∧ ∃ w w', Initiates s w w' p.

The meaning rules are now exactly E0-furnished: every subject exists
(`Exists _ := True`), every proposition is a content (`Content _ := True`),
agency and rationality are analytical (`Agent _ := True`, `Rational _ := True`),
and an act is a meaningful initiation: its constitutive content is intentional meaning,
and its evental character is initiation.
-/

import Logos.Core

namespace Logos.Agency

open Logos.Core (T)

/--Tag: VOCAB
Vocabulary: the pure sort of subjects — that which performs acts of reasoning.

 Subjects: that which performs acts of reasoning — the origin of the act,
    never the act itself, never a state or a content. An uninterpreted pure
    sort, neither empty nor possessing encoded cardinalities. -/
axiom Subject : Type

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

/--Tag: VOCAB
Vocabulary: weak act / performed event — something is performed, uttered, asserted, or denied.

 `act s p`: weak act: performed event (utterance, assertion-event, performance).
    Distinguished from the strong act `Act s p := Means s p ∧ ∃ w w', Initiates s w w' p`. -/
axiom act : Subject → Prop → Prop

/--Tag: VOCAB
Vocabulary: the meaning-act relation — a subject means a proposition.

 `Means s p`: subject s means (intentionally relates to) proposition p
    (base.txt §11, T5 component). Primitive intentional relation. -/
axiom Means : Subject → Prop → Prop

/-- Intentional Subject: a subject that means some propositional content (§11).
    Constitutively follows from the primitive `Means` relation. -/
def IntentionalSubject (s : Subject) : Prop := ∃ p : Prop, Means s p

/-- Backward-compatibility alias for intentionality. -/
def Intentional (s : Subject) : Prop := IntentionalSubject s

/-- Act implies an intentional subject: an act's own content witnesses that the subject
    means something (`IntentionalSubject s := ∃ p, Means s p`). -/
theorem act_implies_intentionalSubject {s : Subject} {p : Prop} (h : Means s p) :
    IntentionalSubject s :=
  ⟨p, h⟩

theorem act_implies_intentional {s : Subject} {p : Prop} (h : Means s p) :
    Intentional s :=
  act_implies_intentionalSubject h

/--Tag: VOCAB
Vocabulary: the sort of natures (essences/kinds) distinct from subjects.

 Nature: the sort of natures. In Γ ontology, Person (Subject) ≠ Nature,
    and multiple distinct subjects may possess the same nature. -/
axiom Nature : Type

/--Tag: VOCAB
Vocabulary: the relation attributing a nature to a subject.

 HasNature s n: subject s possesses nature n. -/
axiom HasNature : Subject → Nature → Prop

/--Tag: VOCAB
Vocabulary: the sort of will faculties distinct from subjects and natures.

 Will: the sort of volitional faculties. Distinct from both Subject and Nature. -/
axiom Will : Type

/--Tag: VOCAB
Vocabulary: the mapping from each subject to its volitional faculty.

 subjectWill s: the unique will faculty possessed by subject s. -/
axiom subjectWill : Subject → Will

/--Tag: VOCAB
Vocabulary: numerical individuation of will faculties across distinct subjects.

 Numerical individuation of wills: distinct subjects possess numerically distinct wills. -/
axiom will_individuation : ∀ s₁ s₂ : Subject, s₁ ≠ s₂ → subjectWill s₁ ≠ subjectWill s₂

/--Tag: VOCAB
Vocabulary: the volitional act relation — a subject wills an action or content.

 Wills s p: subject s actively wills proposition/action p.
    This is the operation or act of willing, distinct from the faculty of willing (`subjectWill s`)
    and distinct from free will (`FreeWill s`). -/
axiom Wills : Subject → Prop → Prop

/--Tag: VOCAB
Vocabulary: abstract state space for initiation of movement.

 State: the state space of transitions for initiation — the act begins movement
    between states. An uninterpreted pure sort. -/
axiom State : Type

/--Tag: VOCAB
Vocabulary: the initiation relation — a subject initiates a transition between states positing content.

 `Initiates s w w' p`: subject s initiates a transition from state w to state w' positing proposition p. -/
axiom Initiates : Subject → State → State → Prop → Prop

/-- `Act s p`: strong act: meaningful initiation of movement.
    An act is a meaningful initiation: its constitutive content is intentional meaning,
    and its evental character is initiation. -/
def Act (s : Subject) (p : Prop) : Prop :=
  Means s p ∧ ∃ w w' : State, Initiates s w w' p

/-- Legacy alias for Act across the library. -/
abbrev A := Act

/-- Definitional consequence: an act entails an initiation of movement. -/
theorem act_implies_initiates {s : Subject} {p : Prop} (h : Act s p) :
    ∃ w w' : State, Initiates s w w' p :=
  h.2

/-- Exact structural decomposition of an intentional act:
    an act decomposes definitionally into an intentional horn (meaning p)
    and an executive horn (initiating a state transition positing p). -/
theorem act_decomposition (s : Subject) (p : Prop) :
    Act s p ↔ Means s p ∧ ∃ w w' : State, Initiates s w w' p :=
  Iff.rfl

/-- The performative act-datum gives intentional meaning without an extra bridge. -/
theorem act_datum_implies_means (h : ∃ s : Subject, ∃ p : Prop, Act s p) :
    ∃ s : Subject, ∃ p : Prop, Means s p := by
  obtain ⟨s, p, ha⟩ := h
  exact ⟨s, p, ha.1⟩

/-- The performative act-datum gives initiation without an extra bridge. -/
theorem act_datum_implies_initiates (h : ∃ s : Subject, ∃ p : Prop, Act s p) :
    ∃ s : Subject, ∃ p : Prop, ∃ w w' : State, Initiates s w w' p := by
  obtain ⟨s, p, _, w, w', hi⟩ := h
  exact ⟨s, p, w, w', hi⟩

-- ===========================================================================
-- Ontological Distinction: Sort vs. Actuality Predicate vs. Existential Claim
-- 1. Sort: `Subject : Type` (uninterpreted domain of candidate actors)
-- 2. Actuality Predicate: `SubjectExists (s : Subject) : Prop`
-- 3. Existential Proposition: `AnActualSubjectExists : Prop := ∃ s, SubjectExists s`
-- ===========================================================================

/-- Actuality Predicate: `SubjectExists s` (s is an actualized subject of an act).
    Constitutive definition of subjecthood in the agency layer:
    to be a subject in actuality is to be the performer of an act. -/
def SubjectExists (s : Subject) : Prop := ∃ p : Prop, Act s p

/-- Legacy alias: Exists s is definitionally SubjectExists s. -/
abbrev Exists : Subject → Prop := SubjectExists

/-- Existential Proposition: at least one actualized subject exists in reality. -/
def AnActualSubjectExists : Prop := ∃ s : Subject, SubjectExists s

/-- Arrow 1 (Case B: Explicit Constitutive Law):
    An act cannot exist without an originating subject that performs/actualizes it.
    Whenever `Act s p` holds, `s` is constitutively an actualized subject. -/
theorem act_requires_subject (s : Subject) (p : Prop) (h : Act s p) : SubjectExists s :=
  ⟨p, h⟩

/-- Legacy alias for act_requires_subject. -/
abbrev act_implies_exists := act_requires_subject

/-- Existence of an act strictly entails that an actualized subject exists. -/
theorem subject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) :
    ∃ s : Subject, SubjectExists s := by
  obtain ⟨s, p, ha⟩ := h
  exact ⟨s, act_requires_subject s p ha⟩

/-- The existential proposition AnActualSubjectExists follows from any act. -/
theorem an_actual_subject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) :
    AnActualSubjectExists :=
  subject_exists_of_act h

-- ===========================================================================
-- 1. Weak Act Layer: Performed Events and Weak Retorsion
-- ===========================================================================

/-- No weak act occurs: the radical thesis that no performed event occurs. -/
def NoWeakAct : Prop := ¬ ∃ s : Subject, ∃ p : Prop, act s p

/-- The weak assertion relation: a performed event affirming proposition `p`.
    `asserts s p` = weak assertion: performed event of asserting `p`. -/
def asserts (s : Subject) (p : Prop) : Prop := act s p ∧ p

/-- Step 1 (weak): The occurrence of a weak assertion is a weak act (performed event). -/
theorem assertion_is_weak_act {s : Subject} {p : Prop} (h : asserts s p) : act s p :=
  h.1

/-- Step 2 (weak): A weak assertion entails that a performed event exists. -/
theorem weak_act_exists_of_assert {s : Subject} {p : Prop} (h : asserts s p) :
    ∃ s' : Subject, ∃ p' : Prop, act s' p' :=
  ⟨s, p, assertion_is_weak_act h⟩

/-- Step 4 (weak retorsion): Asserting that no performed event occurs refutes itself directly.
    Establishes ONLY the weak act (performed event) without sliding into intentional meaning. -/
theorem noWeakAct_selfRefutes (speaker : Subject) (h : asserts speaker NoWeakAct) : False :=
  h.2 (weak_act_exists_of_assert h)

/-- Weak Cogito: any performative assertion entails that a performed event occurs. -/
theorem weak_Cogito {s : Subject} {p : Prop} (h : asserts s p) :
    ∃ s' : Subject, ∃ p' : Prop, act s' p' :=
  weak_act_exists_of_assert h

-- ===========================================================================
-- 2. Transition: Weak Act → Strong Act (Explicit Philosophical Burden)
-- ===========================================================================

/-- The explicit bridge proposition: every performed event is an intentional meaning-act.
    The transition `weak act → strong Act(s,p)`.
    This is a separately identified premise/philosophical target, not an analytical identity.
    A mechanical device or automaton can perform an event `act s p` without intentional meaning. -/
def weak_act_implies_strong_act : Prop :=
  ∀ (s : Subject) (p : Prop), act s p → Act s p

/-- Existential form of the bridge: existence of a performed event entails existence of an intentional act. -/
def weak_act_exists_implies_strong_act_exists : Prop :=
  (∃ s : Subject, ∃ p : Prop, act s p) → ∃ s : Subject, ∃ p : Prop, Act s p

/-- Step from weak act to strong Act under the explicit bridge premise. -/
theorem strong_act_of_weak_act (hBridge : weak_act_implies_strong_act)
    {s : Subject} {p : Prop} (h : act s p) : Act s p :=
  hBridge s p h

/-- Conditional Cogito: performative assertion yields an intentional meaning-act given the bridge. -/
theorem Cogito_of_bridge (hBridge : weak_act_implies_strong_act)
    {s : Subject} {p : Prop} (h : asserts s p) :
    ∃ s' : Subject, ∃ p' : Prop, Act s' p' := by
  obtain ⟨s', p', ha⟩ := weak_act_exists_of_assert h
  exact ⟨s', p', strong_act_of_weak_act hBridge ha⟩

/-- No strong act occurs: the thesis that no intentional meaning-act occurs. -/
def NoAct : Prop := ¬ ∃ s : Subject, ∃ p : Prop, Act s p

/-- Asserting NoAct refutes itself under a weak assertion ONLY given the bridge from weak act to strong Act. -/
theorem noAct_conditional_selfRefutes (hBridge : weak_act_implies_strong_act)
    (speaker : Subject) (h : asserts speaker NoAct) : False :=
  h.2 ⟨speaker, NoAct, strong_act_of_weak_act hBridge (assertion_is_weak_act h)⟩

-- ===========================================================================
-- 3. Strong Act Layer: Intentional Assertions (Strong Shortcut)
-- ===========================================================================

/-- The strong assertion relation: a subject performs an intentional meaning-act affirming `p`.
    `Asserts s p` = strong assertion: intentional/meaning-bearing act asserting `p`.
    Stipulates that the assertion already embodies full intentional meaning (`Act s p := Means s p`). -/
def Asserts (s : Subject) (p : Prop) : Prop := Act s p ∧ p

/-- Arrow 0 (Case A: Purely Definitional — Strong Shortcut):
    Step 1: The occurrence of a strong assertion is an intentional Act.
    Follows purely from the conjunction definition Asserts s p := Act s p ∧ p. -/
theorem assertion_is_act {s : Subject} {p : Prop} (h : Asserts s p) : Act s p :=
  h.1

/-- Step 2 (strong shortcut): A strong assertion entails that an intentional act exists. -/
theorem act_exists_of_assert {s : Subject} {p : Prop} (h : Asserts s p) :
    ∃ s' : Subject, ∃ p' : Prop, Act s' p' :=
  ⟨s, p, assertion_is_act h⟩

/-- The act of asserting NoAct strictly entails that an act occurs. -/
theorem act_of_asserting_no_act (speaker : Subject) (h : Asserts speaker NoAct) :
    ∃ s : Subject, ∃ p : Prop, Act s p :=
  act_exists_of_assert h

/-- Step 3: An assertion entails that an actualized subject exists. -/
theorem subject_exists_of_assert {s : Subject} {p : Prop} (h : Asserts s p) :
    ∃ s' : Subject, SubjectExists s' :=
  ⟨s, act_requires_subject s p (assertion_is_act h)⟩

/-- Step 4 (C58 strong shortcut): Retorsion — asserting that no act occurs refutes itself.
    If the assertion is stipulated as already intentional (strong assertion), refutation is immediate. -/
theorem noCogito_selfRefutes (speaker : Subject) (h : Asserts speaker NoAct) : False :=
  h.2 (act_exists_of_assert h)

/-- Cogito as a derived theorem (strong shortcut): any strong assertion entails that an intentional act occurs. -/
theorem Cogito {s : Subject} {p : Prop} (h : Asserts s p) :
    ∃ s' : Subject, ∃ p' : Prop, Act s' p' :=
  act_exists_of_assert h

/-- T1 derived from the performative act-datum: the subject of an act exists. -/
theorem T1_subjectExists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) :
    ∃ s : Subject, SubjectExists s :=
  subject_exists_of_act h

/-- The proposition that no actualized subject exists: the radical subject-nihilist thesis. -/
def NoSubject : Prop := ¬ ∃ s : Subject, SubjectExists s

/-- C57: Retorsion — asserting that no subject exists refutes itself.
    The performance of the assertion is an act performed by the speaker,
    which constitutively witnesses that the speaker is an actualized subject. -/
theorem noSubject_performative_selfRefutes (speaker : Subject) (h : Asserts speaker NoSubject) : False := by
  have hAct : Act speaker NoSubject := assertion_is_act h
  have hSubj : SubjectExists speaker := act_requires_subject speaker NoSubject hAct
  exact h.2 ⟨speaker, hSubj⟩

/-- C57 canonical theorem name in Agency. -/
theorem noSubject_selfRefutes (speaker : Subject) (h : Asserts speaker NoSubject) : False :=
  noSubject_performative_selfRefutes speaker h

/-- The bare sort nihilist thesis: no candidate subject exists in the domain of discourse. -/
def NoSubjectSort : Prop := ¬ ∃ _s : Subject, True

/-- Denying the domain of discourse refutes itself whenever a speaker asserts it. -/
theorem noSubjectSort_selfRefutes (speaker : Subject) (h : Asserts speaker NoSubjectSort) : False :=
  h.2 ⟨speaker, trivial⟩

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
    Constitutive definition: the first conjunct of `Act s p` is `Means s p`. -/
theorem act_implies_means : ∀ {s : Subject} {p : Prop}, A s p → Means s p := by
  intro s p h
  exact h.1

/--At least one content exists: every proposition is admissible content.

 T2 — there is propositional content. Now axiom-free: `Content` is the
    analytical definition `Content _ := True`, so `True` itself witnesses
    content (cogito no longer needed). -/
theorem T2_contentExists : ∃ p : Prop, Content p :=
  ⟨True, trivial⟩

end Logos.Agency

#print axioms Logos.Agency.T2_contentExists
#print axioms Logos.Agency.Cogito
#print axioms Logos.Agency.noCogito_selfRefutes
#print axioms Logos.Agency.noWeakAct_selfRefutes
#print axioms Logos.Agency.weak_Cogito
#print axioms Logos.Agency.strong_act_of_weak_act
#print axioms Logos.Agency.Cogito_of_bridge
#print axioms Logos.Agency.noAct_conditional_selfRefutes
#print axioms Logos.Agency.act_requires_subject
#print axioms Logos.Agency.subject_exists_of_act
#print axioms Logos.Agency.subject_exists_of_assert
#print axioms Logos.Agency.act_implies_initiates
#print axioms Logos.Agency.act_decomposition
#print axioms Logos.Agency.act_datum_implies_means
#print axioms Logos.Agency.act_datum_implies_initiates
