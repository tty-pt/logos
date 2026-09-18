# Γ — The Deduction

**Generated document.** Produced by `scripts/build_deduction.py`; do not edit it by hand (sync rule in `AGENTS.md`). A philosopher can read Sections 1–4 and understand the argument, its inline obstructions and caveats, and its unresolved frontier; a logician can follow the appendices down to the kernel proof and the exact axiom footprint.

- **Lean source:** `formal/Logos/*.lean` — kernel-checked (`lake build` green, sorryAx 0)
- **Kernel footprints:** `formal/axiom_audit.json` (`#print axioms` per declaration — the exact transitive kernel axiom set, meta-logic included)
- **Axiom tags:** the `Tag:` line (`VOCAB`/`SEM`/`META`) on each axiom's Lean docstring
- **Dependency graph:** `formal/depgraph.json` (LeanDepViz, kernel)
- **Claim ledger:** [`formal/GAPMAP.md`](formal/GAPMAP.md) — statuses transcribed and *checked* against the kernel, never its source
- **Prose:** [`base.txt`](base.txt) (§0–§29) · [`poem.txt`](poem.txt) (P1–P10) · [`theorems/`](theorems/)

Regeneration: `python3 scripts/audit_footprints.py && python3 scripts/build_deduction.py`

---

## 1. What the argument tries to establish

Γ does not begin from an arbitrary propositional premise. It begins from a performatively given datum: an act of meaning is occurring. From that datum the argument extracts the maximum that is *un-deniable*, marking at every step whether a claim is **LOGICAL** (logic alone), **DEFINITIONAL** (follows from how Γ's concepts are constituted), **SEMANTIC** (a substantive semantic principle), or **METAPHYSICAL** (a substantive metaphysical bridge). No claim is called a deduction unless it is derived; no bridge is smuggled in unnamed. The conclusion layers of `base.txt` §0 are kept separate: the performatively undeniable, the logically undeniable, the transcendentally necessary, and the metaphysically necessary *if the corresponding bridge is shown*. God is not derived; the relevant steps are faith or deferred.

**Status vocabulary.** **LOGICAL** (logic alone) · **DEFINITIONAL** (follows from how Γ's concepts are constituted) · **SEMANTIC** (a substantive semantic principle) · **METAPHYSICAL** (a substantive metaphysical bridge) · **OPEN** (not currently derived) · **COUNTERMODEL** (a proposed inference fails in a hostile model). A `/ CONDITIONAL` qualifier marks a conclusion resting on a premise clause.

---

## 2. The argument at a glance

```text
performative act → truth / falsehood                       LOGICAL
performative act → distinction (right / wrong)             LOGICAL
performative act → subject                                 DEFINITIONAL
performative act → person                                  DEFINITIONAL
performative act → choice field (weak choice)              DEFINITIONAL
weak choice / choice-field → genuine choice (strong choice) OPEN
genuine choice (strong choice) → free will                 DEFINITIONAL
performative act → necessary person / entity               DEFINITIONAL
performative act → necessary reality (T7)                  SEMANTIC
performative act → personal ground (T8)                    METAPHYSICAL
performative act → plurality                               METAPHYSICAL
performative act → love                                    METAPHYSICAL
performative act → God ?                                   OPEN
```

### 2.1 The genuine-choice frontier

```text
PERFORMATIVE ACT
       │
       ├──→ PERSON                 established (C24)
       ├──→ CHOICE FIELD           established (C51, C52)
       └──→ GENUINE CHOICE         OPEN (F1b)
                    │
                    ↓
                FREE WILL            follows by definition
```

Conceptual stipulation: `Chooses s p q` means genuine choice between incompatible alternatives. Therefore `Chooses s p q → FreeWill s` is valid by definition (`Chooses → FreeWill`, footprint `{Means, Subject}`). The substantive question is whether anything actually satisfies `Chooses`: that is the open existence claim F1b, not the implication.

---

## 3. The deduction

### Stage I — The Performative Starting Point

The argument begins not from an arbitrary propositional premise but from a performative datum: an act of affirming, denying, doubting or judging is occurring. The starting point (`base.txt` §0) is the contrast between an arbitrary premise and a claim whose negation destroys the very act of negating it. The steps below attempt, oppose and refute the absolute theses that nothing — or everything — is true.

**Definition (Weak act vs. strong Act).** `act(s, p)` — *weak act: performed event* (utterance, assertion-event, performance) vs. `Act(s, p) := Means(s, p)` (abbreviated `A(s, p)`) — *strong act: intentional/meaning-bearing act*.

**Definition (Weak assertion vs. strong assertion).** `asserts(s, p) := act(s, p) ∧ p` (*weak assertion: performed assertion event*) vs. `Asserts(s, p) := Act(s, p) ∧ p` (*strong assertion: meaning-bearing assertion*).

**Bridge (Weak act to strong act).** `weak_act_implies_strong_act := ∀ s p, act(s, p) → Act(s, p)` (*unforced intentionality bridge*).

**Definition (Subject actuality).** SubjectExists(s) := ∃ p, Act(s, p).

**Definition (Personhood).** Person(s) := Agent(s) ∧ Rational(s) ∧ Intentional(s), where Agent(s) := True, Rational(s) := True, and Intentional(s) := ∃ p, Means(s, p).

**Axiom A2 · Subject (VOCAB).**
\[ Subject : Type \]
The pure sort of subjects — that which performs acts of reasoning.

**Axiom A10 · act (VOCAB).**
\[ act : Subject → Prop → Prop \]
Weak act / performed event — something is performed, uttered, asserted, or denied.

**Proposition C58 (Step 4 (weak retorsion)).**

Asserting that no performed event occurs refutes itself directly

\[ asserts(speaker, NoWeakAct) → False \]

**Proof.** Assume asserts(speaker, NoWeakAct). Follows under **A10**, **A2**. ∎

**Obstruction.** `CountermodelWeakActWithoutMeaning` — A performed event (utterance, keystroke, physical emission) does not entail an intentional meaning-act: `act s p` can occur without `Means s p`.

**Γ's answer.** the step is constitutive in Γ, not a logical consequence.

`Lean: Agency.lean#L143 · uses A2, A10 · DEFINITIONAL ✔`

**Axiom A5 · Means (VOCAB).**
\[ Means : Subject → Prop → Prop \]
The meaning-act relation — a subject means a proposition.

**Proposition C68 (Cogito as a derived theorem (strong shortcut)).**

Any strong assertion entails that an intentional act occurs.

\[ Asserts(s, p) → ∃ s', p', Act(s', p') \]

**Proof.** Assume Asserts(s, p). Follows under **A2**. ∎

`Lean: Agency.lean#L222 · uses A2, A5 · DEFINITIONAL ✔`

**Proposition C83 (The Cartesian Retortion (half 1)).**

No subject can ever correctly judge that no act occurs

\[ ¬Correct(s, NoAct) \]

**Proof.** Under **a2**, the assumption refutes itself. ∎

`Lean: Order.lean#L159 · uses A2, A5 · DEFINITIONAL ✔`

**Proposition C84 (The Retorsive Cogito).**

Even the skeptic's denial that any act occurs strictly witnesses that an act occurs. The act cannot be denied without providing the witness that refutes the denial.

\[ (Correct(s, NoAct) ∨ Incorrect(s, NoAct)) → ∃ s', p', A(s', p') \]

**Proof.** Assume Correct(s, NoAct) ∨ Incorrect(s, NoAct). The required witness is constructed under **A2**. ∎

`Lean: Order.lean#L180 · uses A2, A5 · DEFINITIONAL ✔`

**Lemma C63 (Initiation is not transfer).**

A relation with genuine alternatives is not the graph of any function.

\[ Branches(R) → ¬IsTransfer(R) \]

**Proof.** Assume Branches(R). By definition, the assumption refutes itself. ∎

`Lean: Initiation.lean#L27 · LOGICAL ✔`


### Stage II — Truth and Falsehood

Once an act of meaning is occurring, truth and falsehood cannot both be abolished. The performative absolutes refute themselves (C1–C9); the classical laws and the object-language distinction between truth and falsehood follow (C10–C12). The stage closes with the transcendental principles of semantics and the elementary truthmaker step.

**Definition (Truth and falsehood).** T(p) := p (truth is identity, E0) and IsFalse(p) := ¬T(p).

**Definition (The absolutes).** N_T := ∀ p, ¬T(p) (nothing is true) and N_F := ∀ p, T(p) (everything is true).

**Lemma C1 (It cannot be true that nothing is true).**

Asserting 'nothing is true' would itself be a true proposition.

\[ ¬T(N_T) \]

**Proof.** `T(N_T)` cannot hold: assuming it forces both `N_T` and `¬T(N_T)`. ∎

`Lean: Core.lean#L61 · LOGICAL ✔`

**Lemma C2 (It is false that nothing is true).**

Some proposition is true.

\[ ¬N_T \]

**Proof.** ¬(∀p ¬T(p)): it is not the case that nothing is true (classical step §4). ∎

`Lean: Core.lean#L69 · LOGICAL ✔`

**Lemma C3 (Some proposition is true).**

\[ ∃ p, T(p) \]

**Proof.** There is at least one true proposition. ∎

`Lean: Core.lean#L77 · LOGICAL ✔`

**Lemma C4 (The proposition True is itself true).**

\[ T(True) \]

**Proof.** Follows directly from the definitions. ∎

`Lean: Core.lean#L85 · LOGICAL ✔`

**Lemma C5 (It cannot be true that nothing is false).**

If it were, the falsehood False would be true.

\[ ¬T(N_F) \]

**Proof.** `T(N_F)` cannot hold: `∀p T(p)` applied to the proposition `False`. ∎

`Lean: Core.lean#L94 · LOGICAL ✔`

**Lemma C6 (It is false that everything is true).**

Some proposition is false.

\[ ¬N_F \]

**Proof.** ¬(∀p T(p)): it is not the case that everything is true. ∎

`Lean: Core.lean#L103 · LOGICAL ✔`

**Lemma C7 (Some proposition is false).**

\[ ∃ q, IsFalse(q) \]

**Proof.** There is at least one false proposition. ∎

`Lean: Core.lean#L111 · LOGICAL ✔`

**Lemma C8 (Truth and falsehood both obtain).**

Some proposition is true and some proposition is false.

\[ ∃ p, q, T(p) ∧ IsFalse(q) \]

**Proof.** T3 — truth and falsehood are both necessarily instantiated, hence `T ≠ F` as statuses: `∃p, T(p)` and `∃q, ¬T(q)`. ∎

`Lean: Core.lean#L156 · LOGICAL ✔`

**Lemma C9 (No proposition is both true and false).**

\[ ∀ p, ¬(T(p) ∧ IsFalse(p)) \]

**Proof.** No proposition is both true and false (non-contradiction for T). ∎

`Lean: Core.lean#L162 · LOGICAL ✔`

**Lemma C10 (For every proposition p, 'p or not-p' is true).**

\[ ∀ p, T((p ∨ ¬p)) \]

**Proof.** Follows directly from the definitions. ∎

`Lean: Core.lean#L174 · LOGICAL ✔`

**Lemma C11 (For every proposition p, 'not (p and not-p)' is true).**

\[ ∀ p, T((¬(p ∧ ¬p))) \]

**Proof.** Follows directly from the definitions. ∎

`Lean: Core.lean#L180 · LOGICAL ✔`

**Lemma C12 (Every proposition is either true or false).**

\[ ∀ p, T(p) ∨ IsFalse(p) \]

**Proof.** Bivalence, §10: each proposition is true or false (is false iff not true). ∎

`Lean: Core.lean#L186 · LOGICAL ✔`

**Lemma C13 (In every world, 'φ or not-φ' is true).**

\[ □(φ ∨ ¬φ) \]

**Proof.** Follows by classical logic (**CL**). ∎

`Lean: Semantics.lean#L76 · LOGICAL ✔`

**Lemma C14 (In every world, 'φ and not-φ' cannot be true).**

\[ ¬◇(φ ∧ ¬φ) \]

**Proof.** By classical logic (**cl**), the assumption refutes itself. ∎

`Lean: Semantics.lean#L85 · LOGICAL ✔`

**Lemma C16 (In every world, 'φ or not-φ' is true — composite truth is Tarskian-compositional).**

\[ □(φ ∨ ¬φ) \]

**Proof.** Follows directly from the definitions. ∎

`Lean: Truthmaker.lean#L129 · LOGICAL ✔`

**Lemma C17 (In every world, 'φ and not-φ' cannot be true).**

\[ ¬◇(φ ∧ ¬φ) \]

**Proof.** By definition, the assumption refutes itself. ∎

`Lean: Truthmaker.lean#L137 · LOGICAL ✔`

**Lemma C31 (Consequence preserves truth).**

Whatever two true premises jointly imply is true.

\[ (p₁ → p₂ → q) → T(p₁) → T(p₂) → T(q) \]

**Proof.** Assume p₁ → p₂ → q, and T(p₁), and T(p₂). Follows directly from the definitions. ∎

`Lean: Order.lean#L150 · LOGICAL ✔`

**Lemma C35 (It is neither the case that nothing is true, nor that nothing is false).**

\[ ¬(N_T ∨ N_F) \]

**Proof.** `¬(N_T ∨ N_F)`: it is not the case that (either nothing is true or nothing is false) — the poem's "p1 ∨ p2 is a contradiction"; classically from `notNothingTrue` (C2) and `notEverythingTrue` (C6). ∎

`Lean: Core.lean#L129 · LOGICAL ✔`

**Lemma C36 (Right and wrong both obtain).**

It is false that nothing is true, and false that everything is true.

\[ ¬N_T ∧ ¬N_F \]

**Proof.** Right AND wrong both obtain: `¬N_T ∧ ¬N_F`, classically from `¬(N_T ∨ N_F)` — the direct witness for the poem's P2 conclusion "há certo e há errado". ∎

`Lean: Core.lean#L145 · LOGICAL ✔`


### Stage III — The Subject of Thought

The act is always an act *of* a subject and *about* content. From the performative datum Γ reads off the existence of a subject of thought (C21), the subject's inseparability from its act, and the collapse of the subject into the person (*esse est agere*). The stage is definitional modulo the vocabulary of agency.

**Proposition C21 (At least one subject exists).**

Derived from the performative act-datum.

\[ ∃ s, p, Act(s, p) → ∃ s, SubjectExists(s) \]

**Proof.** T1 (C21) — the subject of the present act exists: derived from the existence of an intentional act(C68, via) the constitutive rule `act_requires_subject` (Case B). Footprint: `{Means, Subject}` (VOCAB only; decoupled from AxTwoSubjects). ∎

**Obstruction.** `CountermodelActWithoutSubject` — Without a constitutive rule, an act can occur in the void with no actualizing subject (Lichtenberg's objection).

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from `Act s p := Means s p`; `act_requires_subject : Act s p → SubjectExists s`.

`Lean: Plurality.lean#L66 · uses A2, A5 · DEFINITIONAL ✔`

**Lemma C22 (At least one content exists).**

Every proposition is admissible content.

\[ ∃ p, Content(p) \]

**Proof.** T2 — there is propositional content. Now axiom-free: `Content` is the analytical definition `Content(_) := True`, so `True` itself witnesses content (cogito no longer needed). ∎

`Lean: Agency.lean#L281 · LOGICAL ✔`

**Proposition C23 (At least one agent exists).**

Someone who acts.

\[ ∃ s, p, Act(s, p) → ∃ s, SubjectExists(s) ∧ Agent(s) \]

**Proof.** T4 (C23) — the subject is an agent (`Agent` is analytical `:= True`): derived from the existence of an intentional act (C68 → C21). Footprint: `{Means, Subject}`. ∎

**Obstruction.** `CountermodelActWithoutSubject` — an act occurring with no actualizing subject (see Appendix C.1).

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from Act → Agent is constitutive in Γ.

`Lean: Plurality.lean#L74 · uses A2, A5 · DEFINITIONAL ✔`

**Theorem C24 (At least one person exists).**

Formally forced under the §12 constitutive definition of Person (`Person` → `Intentional` → `∃ p, Means s p`). It establishes only the actualized meaning-subject; substantive personhood is not independently established.

\[ ∃ s, p, Act(s, p) → ∃ s, Person(s) \]

**Proof.** The chain C68 → Act → SubjectExists → Intentional → Person(§12 nominal) makes the identity explicit (`Person.person_intentional_iff` + bridge lemmas); the substantive reading (deliberation, moral responsibility, self-reflection, autonomous agency) is not independently established — see `HostileSemantics` Part A2. Footprint: `{Means, Subject}` (VOCAB; decoupled from AxTwoSubjects). ∎

**Obstruction.** `CountermodelNoPerson` — The bare act-datum `∃ s p, A s p` does not force any `Person`.

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from §12 reduction `Person s := Agent s ∧ Rational s ∧ Intentional s` with `Agent, Rational := True` (`Person.person_intentional_iff`).

`Lean: Plurality.lean#L90 · uses A2, A5 · DEFINITIONAL ✔`

**Proposition C25 (Every rational act carries a personal feature exactly when it carries a logical feature).**

Personhood and logic travel together.

\[ ∀ a, RationalAct(a) → (CarriesPersonalFeature(a) ↔ CarriesLogicalFeature(a)) \]

**Proof.** Evaluating by disjunctive cases under **A2**, **A5**. ∎

`Lean: Person.lean#L144 · uses A2, A5 · DEFINITIONAL ✔`

**Proposition C49 (Meaning needs a subject).**

Whatever is meant is meant by someone.

\[ Means(s, p) → ∃ t, Means(t, p) \]

**Proof.** No meaning without a subject (analytic): the intentional relation `Means : Subject → Prop → Prop` only exists relata-subjected, so the subject of any meaning is itself the witness. ∎

`Lean: Choice.lean#L116 · uses A2, A5 · DEFINITIONAL ✔`

**Proposition C57 (Retorsion — asserting that no actual subject exists refutes itself).**

\[ Asserts(speaker, NoSubject) → False \]

**Proof.** Assume Asserts(speaker, NoSubject). Follows under **A2**. ∎

`Lean: Choice.lean#L351 · uses A2, A5 · DEFINITIONAL ✔`

**Proposition C62 (Right and wrong need meaning).**

The normative predicates are properties of meaning-acts, so wherever right-or-wrong is realized, a meaning (and thus a subject, C49) is realized.

\[ (∃ s, p, Correct(s, p)) ∨ (∃ s, p, Incorrect(s, p)) → ∃ p, Meaning_I(p) \]

**Proof.** "For right to be distinct from wrong, meaning must be a thing" (poem P3, line 18). Pure projection from the §8 definitions: `Correct(s, p)` unfolds to `A(s, p) ∧ T(p)` with `A(s, p) := Means(s, p)`, so the witness content `p`, meant by `s`, is a `Meaning_I`. Footprint `{Means, Subject}` (vocab-only — no substantive axiom): no model can assert `Correct`/`Incorrect` while denying meaning, because `A(s, p)` is a conjunct. ∎

`Lean: Order.lean#L46 · uses A2, A5 · DEFINITIONAL ✔`


### Stage IV — Agency and Choice

A subject that acts and judges is a person before a field of incompatible alternatives. C26/C27/C50 supply the alternatives; C39 and C51/C52 derive the choice field and its performative retorsion (C53); C54/C61 connect it to right-and-wrong; C28/C29 record fallibility. The genuine-choice frontier sits exactly here: that a person *has* a field of alternatives is established, but that anyone co-means incompatible horns — genuine choice (F1b) — is not; the step from choosing to free will is definitional.

**Definition (Incompatibility, weak choice, and strong choice).** Incompatible(p, q) := ¬(p ∧ q), ChoiceField(s, p, q) := A(s, p) ∧ Incompatible(p, q) (*weak choice: incompatible alternatives are present*), and Chooses(s, p, q) := A(s, p) ∧ A(s, q) ∧ Incompatible(p, q) (*strong choice: the subject co-means incompatible alternatives*).

**Definition (Free will).** FreeWill(s) := ∃ p, q (Chooses(s, p, q)) (*freedom: definitional from strong choice*).

**Frontier (Genuine choice).** rejectedHornCoMeant := ∃ s p, A(s, p) ∧ A(s, ¬p) (*the missing co-meaning resource, F1b BLOCKED*).

**Definition (Judgment quality).** Correct(s, p) := A(s, p) ∧ T(p), Incorrect(s, p) := A(s, p) ∧ IsFalse(p), and Fallible(s, p) := IsFalse(p).

**Lemma C26 (There are two incompatible alternatives, one of them true and the other false).**

\[ ∃ p, q, Incompatible(p, q) ∧ T(p) ∧ IsFalse(q) \]

**Proof.** T9 — there are at least two incompatible contents, one true and one false: the minimal field of rational choice of §13 is non-empty, and it is present constructively (no choice axioms). ∎

`Lean: Alternatives.lean#L24 · LOGICAL ✔`

**Lemma C27 (Every true proposition is incompatible with its own negation).**

\[ T(p) → Incompatible(p, ¬p) ∧ T(p) ∧ IsFalse(¬p) \]

**Proof.** General form: any true content and its own negation are incompatible. ∎

`Lean: Alternatives.lean#L35 · LOGICAL ✔`

**Lemma C50 (Every proposition is incompatible with its own negation).**

\[ Incompatible(p, ¬p) \]

**Proof.** A(proposition, and) its own negation are always incompatible options (`¬(p ∧ ¬p)`, pure logic, footprint `{}`) — the field around any meaning-act(is, non)-empty. ∎

`Lean: Choice.lean#L92 · LOGICAL ✔`

**Proposition C39 (There is a field of choice).**

Some person with two incompatible alternatives.

\[ ∃ s, p, A(s, p) → ∃ s, Person(s) ∧ ∃ p, q, Incompatible(p, q) \]

**Proof.** T11 (C39) — the minimal field of rational choice is non-empty for a person: derived from an intentional act(datum, (C68 → C24 → C39)). Footprint: `{Means, Subject}` (VOCAB only; decoupled from AxTwoSubjects). ∎

**Obstruction.** `CountermodelNoPerson` — the bare act datum forcing `Person` (see Appendix C.1).

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from `ChoiceField s p q := A s p ∧ Incompatible p q` (the second horn is supplied by logic, C27/C50).

`Lean: Choice.lean#L243 · uses A2, A5 · DEFINITIONAL ✔`

**Lemma C51 (Any person has a choice field).**

A person is always before two incompatible alternatives.

\[ Person(s) → ∃ p, q, ChoiceField(s, p, q) \]

**Proof.** Audit notice (freedom/choice fix, 2026-09-18): this yields `ChoiceField`, NOT genuine `Chooses`. The agent is related only to the adopted content `p`; the rejected horn `¬p` is supplied by pure logic (`incompatible_self_negation`), not by the agent. The genuine form (both horns co-meant) is BLOCKED on `rejectedHornCoMeant`. Nominal wrapper of `intentional_hasChoiceField` (the §12 label adds nothing). ∎

`Lean: Choice.lean#L273 · uses A2, A5 · DEFINITIONAL ✔`

**Proposition C52 (The choice field exists).**

Some subject is before two incompatible alternatives.

\[ ∃ s, p, A(s, p) → ∃ s, p, q, ChoiceField(s, p, q) \]

**Proof.** C52 (field form) — the field is real: derived from an intentional act(datum, (C68 → C52)) through the WEAKER predicate `Intentional` (via `act_implies_intentional`), not through the §12 person label: `SubjectExists`/`Intentional` suffices. Footprint: `{Means, Subject}` (VOCAB only). ∎

`Lean: Choice.lean#L283 · uses A2, A5 · DEFINITIONAL ✔`

**Proposition C53 (Performative retorsion — asserting that no choice field exists refutes itself).**

Footprint: `{Means, Subject}` (VOCAB only; zero AxTwoSubjects).

\[ Asserts(speaker, NoChoiceField) → False \]

**Proof.** Assume Asserts(speaker, NoChoiceField). Follows under **A2**. ∎

`Lean: Choice.lean#L308 · uses A2, A5 · DEFINITIONAL ✔`

**Axiom A6 · AxTwoSubjects (META).**
\[ (¬N_T ∧ ¬N_F) → ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ \]
The *reality* of right-and-wrong demands that there be at least two distinct persons. Narrower than the former single bridge `AxValueInterpersonal` (plurality only…

*Philosophical cost:* A substantive interpersonal metaphysics. A lone judging subject, and the unit world of a single act, remain logically consistent with every earlier premise, so the demand for a second distinct person is posited, not deduced. Plural personal reality is bought with this declared bridge.

**Theorem C54 (Right-and-wrong commits a choice field).**

Where there is truth and error, someone is before an incompatible pair.

\[ (¬N_T ∧ ¬N_F) → ∃ s, p, q, ChoiceField(s, p, q) \]

**Proof.** C54 (field form): "No right and wrong without (a field of) choice" — whenever the distinction holds, some subject before a choice field exists via AxTwoSubjects(poem P5). The genuine `Chooses` conclusion is BLOCKED on `rejectedHornCoMeant`. ∎

`Lean: Choice.lean#L324 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C61 (Right-and-wrong implies someone who means).**

(poem P3, line 18 "há certo e há errado → há significado → há alguém para quem algo significar")

\[ (¬N_T ∧ ¬N_F) → ∃ s, p, Means(s, p) \]

**Proof.** C61: `JUDGE_HAS_CHOICE_FIELD` (C54) composes with `rightWrongDistinction` (C36) to yield a field; its first conjunct is a meaning-act, so some subject means some content. ∎

`Lean: Choice.lean#L344 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C28 (A fallible judgment need not be true).**

Fallibility is real.

\[ ¬(∀ s, p, Fallible(s, p) → T(p)) \]

**Proof.** T6 — truth is not created by asserting: assertion ⇒ truth fails (under **A2**). ∎

`Lean: Order.lean#L90 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C29 (Truth is not the same as being fallibly judged).**

What is true transcends the will to judge.

\[ ¬(∀ s, p, Fallible(s, p) ↔ T(p)) \]

**Proof.** T6, second form: `Truth ≠ WillOfAgent` — no equivalence can hold between willing-asserting and being true. ∎

`Lean: Order.lean#L99 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Open problem F1b (Genuine choice exists).**

Some subject co-means two incompatible contents; that existence itself remains blocked. The modal side of openness is settled and inert — `atoms_are_modally_free` (C95) and `some_formula_contingent` (C96), both `{}`, prove content-openness, yet even fuelled as an extra datum the modal channel cannot force co-meaning (`modal_openness_does_not_entail_genuine_choice(_and_plurality)`, `{}`, HostileSemantics); the block is solely `rejectedHornCoMeant` (agency-side, option 3), not any modal determination.

\[ \exists s\,p\,q\; Chooses(s,p,q) \qquad (\text{not derived}) \]

**Obstruction.** `CountermodelVeridicalMeaning` — The act-datum does not force `genuineChoice_exists` even under the Logos definition of `Chooses`: veridical meaning makes co-meaning an incompatible pair impossible while the whole agency/choice/order fragment holds.

**Obstruction.** `CountermodelNoFreeWill` — Mere occurrence of an act does not entail genuine choice: an uninterpreted determined act with `Chooses := False` satisfies the datum while `Chooses` and `FreeWill` stay empty.

**Status: OPEN.**

`Lean: Choice.lean#L183 · uses A2, A5 · OPEN ✖`

**Corollary (Free will is definitional).**

\[ Chooses(s, p, q) → FreeWill(s) \]

**Proof.** Immediate from FreeWill(s) := ∃ p, q (Chooses(s, p, q)) (definitional unrolling). ∎

`Lean: Choice.lean#L151 · uses A5 · DEFINITIONAL ✔`

**Open problem F7 (The bipolar half of freedom is subsumed by unary `FreeWill`).**

The open gap is not 'freedom impossible to derive' but *existence of genuine choice* not yet derived from the performative datum (F1b, `genuineChoice_exists`). World-level `ChoiceAt : World → Subject → Prop → Prop` remains a future, priced SEM vocabulary.

**Status: OPEN.**

`Lean: HostileSemantics.lean#L458 · OPEN ✖`


### Stage V — Necessity

From the semantic principles and the modal backbone Γ derives the necessary: excluded middle and non-contradiction, the necessary person, and the necessary reality (T7). The person/entity lifts are definitional; the necessary reality itself is the first place a substantive bridge — `AxGlobalGround` — is priced.

**Definition (World necessity).** NecessarilyTrue(φ) := ∀ w, TrueAt(w, φ) (written □ φ) and NecessarilyFalse(φ) := ∀ w, FalseAt(w, φ) (written ¬◇ φ).

**Definition (Necessary entities and persistence).** NecessaryEntity(e) := ∀ w, ExistsAt(w, e), Contingent(e) := ¬NecessaryEntity(e), and NecessarySubject(s) := ∀ w, ExistsAt(w, EntityOf(s)).

**Lemma C37 (In every world there is necessarily-true content and necessarily-false content).**

\[ (∃ τ, □ τ) ∧ (∃ ρ, ¬◇ ρ) \]

**Proof.** There is a necessarily-true content AND a necessarily-false one (the poem's "há certo E há errado" where "errado" is level-1 falsity), witnessed by the excluded-middle tautology and the non-contradiction anti-tautology, respectively. ∎

`Lean: Semantics.lean#L102 · LOGICAL ✔`

**Lemma C38 (The distinction between right and wrong under the identity-model alias).**

\[ □(¬N_T ∧ ¬N_F) \]

**Proof.** NOTE: `Necessity(p)` is an identity alias (`Necessity(p) ↔ p`), not genuine metaphysical necessity. The genuine world-level modal theorem is `Semantics.bothNecessarilyTrueAndFalse` (C37). ∎

`Lean: Necessity.lean#L116 · LOGICAL ✔`

**Lemma C59 (Strong truth exists).**

Some formula is true in every world — axiom-free, the performative "há certo E há errado" (§27, poem.txt), resident as the excluded-middle datum C37 (footprint {CL}).

\[ ∃ τ, □ τ \]

**Proof.** The required witness is constructed directly. ∎

`Lean: Semantics.lean#L113 · LOGICAL ✔`

**Lemma C93 (Denying strong truth refutes itself).**

It cannot be the case that no formula is necessarily true — the act of denying strong truth is destroyed by strong truth (performative retorsion of C59, footprint {CL}).

\[ ¬(¬∃ τ, □ τ) \]

**Proof.** By definition, the assumption refutes itself. ∎

`Lean: Semantics.lean#L121 · LOGICAL ✔`

**Proposition C94 (No one can assert "there is no strong truth").**

The act of denying the world-level datum is destroyed by the datum itself (assertive retorsion of C93, completing the retorsion family at the assertion level; footprint {Means, Subject, CL}).

\[ Asserts(speaker, ¬∃ τ, □ τ) → False \]

**Proof.** Under **a2**, the assumption refutes itself. ∎

`Lean: Choice.lean#L387 · uses A2, A5 · DEFINITIONAL ✔`

**Lemma C95 (The atoms are modally free).**

No atom is fixed in either modal direction.

\[ ∀ n, ¬□atom(n) ∧ ¬¬◇atom(n) \]

**Proof.** The atom-wall, combined form (footprint {}). ∎

`Lean: Semantics.lean#L146 · LOGICAL ✔`

**Lemma C96 (Contingent content exists — the counterweight of C59 (GAPMAP.md C96)).**

Some formula is neither necessary nor impossible, derived from the atom-wall (footprint {}).

\[ ∃ τ, ¬□ τ ∧ ¬¬◇ τ \]

**Proof.** Evaluating by disjunctive cases from premises. ∎

`Lean: Semantics.lean#L160 · LOGICAL ✔`

**Theorem C77 (There exists a necessary person).**

Someone who is a person and persists in every world.

\[ ∃ s, p, Act(s, p) → ∃ s, Person(s) ∧ NecessarySubject(s) \]

**Proof.** C77 (re-anchored, 2026-09-18): from the performative act-datum (`h : ∃ s, p, Act(s, p)`, C68) a person exists (`T5_personExists`, C24) and it is necessary by definition (`AxPersonStability`, esse est agere). The old closed form ran through plurality (`T5_personExists_from_plurality`, footprint `{AxTwoSubjects, Means, Subject}`); the hypothesis-carrying form drops `AxTwoSubjects`. The necessity here is *definitional* (`ExistsAt (Subject) := ExistsAt (Entity.ofSubject _) := True`), not a bridge — and, like C24 itself, it needs only the actualized meaning-subject (`∃ p, Means(s, p)`), not the substantive reading of "person". A VOCAB-only kernel footprint does NOT certify semantic neutrality of the definitions: this is an ontology-internal constitutive necessity, not an ontology-independent metaphysical one. Footprint: `{Means, Subject}` (VOCAB only). ∎

**Obstruction.** `CountermodelPersonNotNecessary` — A person need not be a necessary subject: `Person → NecessarySubject` fails as a logical law (subject exists only in the `true` world).

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from `AxPersonStability : Person s → NecessarySubject s` (esse est agere).

`Lean: Love.lean#L129 · uses A2, A5 · DEFINITIONAL / CONDITIONAL ✔`

**Proposition C91 (A subject that is necessary has an entity-correlate that is a necessary entity).**

\[ NecessarySubject(s) → NecessaryEntity(EntityOf(s)) \]

**Proof.** Necessity(lift) (subject → entity, C91): if the subject `s` persists in every world (`NecessarySubject(s)`), its entity-correlate `EntityOf(s)` is an entity that exists in every world. The lift is *definitional*: `ExistsAt` is one shared relation and `EntityOf` is the Truthmaker(embedding), so both sides unfold to `∀ w, ExistsAt(w, EntityOf(s))`. It carries no SEM/META price; its force is exactly the definitions chosen in Plurality/Truthmaker. Hostile separation (not a logical law): `CountermodelSubjectNecessityNotEntityNecessity` in HostileSemantics. Footprint: `{Subject}`. ∎

**Obstruction.** `CountermodelSubjectNecessityNotEntity` — Subject-persistence does not entail entity-necessity by logic alone: the transfer fails with independent persistence/existence predicates.

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from `subject_nec_entity_nec : NecessarySubject s → NecessaryEntity (EntityOf s)`.

`Lean: Modal.lean#L103 · uses A2 · DEFINITIONAL ✔`

**Corollary C92 (There exists a necessary entity).**

The entity-correlate of the performing person exists in every world.

\[ ∃ s, p, Act(s, p) → ∃ e, NecessaryEntity(e) \]

**Proof.** E5 / C92 — from the demonstrated person (C24, `T5_personExists`) and its persistence (`AxPersonStability`, esse est agere) with the subject→entity lift (`Modal.subject_nec_entity_nec`, C91), some entity exists in every world. This does NOT close T7: it is the performing person's correlate, not a uniform ground of necessary truths (that stays `AxGlobalGround`-priced, C18). Like C77, it needs only the actualized meaning-subject; a VOCAB-only footprint does NOT certify semantic neutrality — this is constitutive necessity, not an ontology-independent metaphysical one. Footprint: `{Means, Subject}` (VOCAB only; no AxTwoSubjects, no SEM/META). ∎

**Obstruction.** `CountermodelPersonNotNecessary` — `Person → NecessarySubject` as a logical law (see Appendix C.1).

**Γ's answer.** the step is DEFINITIONAL in Γ, not LOGICAL: it follows from `AxPersonStability` and `subject_nec_entity_nec`.

`Lean: Love.lean#L147 · uses A2, A5 · DEFINITIONAL ✔`


### Stage VI — Grounding

Grounding turns truth into a relation to reality. The atomic truthmaker is definitional; its propositional and global reflections are the priced semantic bridge (`AxGlobalGround`), and the personal ground is the priced metaphysical bridge (`AxPersonalGround`). The withdrawn and blocked ground-theoretic steps are shown here as well.

**Axiom A1 · Ground (VOCAB).**
\[ Ground : Entity → Form → Prop \]
The truthmaker relation — an entity grounding a formula.

**Axiom A3 · Truthmaker (SEM).**
\[ ∀ w, φ, w ⊨ φ → ∃ e, ExistsAt(w, e) ∧ Ground(e, φ) \]
The truthmaker principle: truth is grounded in reality.

*Philosophical cost:* The price of a realist reading of correspondence — the bridge commits Γ to a non-vacuous grounding relation between satisfied formulas and existing entities, without deciding what kind of entities those must be. A coherence or deflationary account of truth is thereby excluded; the principle is posited, not derived.

**Theorem C15 (Every atomic truth is grounded).**

Where an atom is true, an entity exists there that grounds it.

\[ w ⊨ atom(n) → ∃ e, ExistsAt(w, e) ∧ Ground(e, atom(n)) \]

**Proof.** Follows under **A1**, **A3**. ∎

`Lean: Truthmaker.lean#L94 · uses A1, A2, A3 · SEMANTIC ⚠`

**Theorem C60 (The denial that atomic truth is grounded refutes itself under the Truthmaker bridge).**

\[ ¬(∃ w, n, w ⊨ atom(n) ∧ ¬(∃ e, ExistsAt(w, e) ∧ Ground(e, atom(n)))) \]

**Proof.** Under **a1**, **a3**, the assumption refutes itself. ∎

`Lean: Truthmaker.lean#L101 · uses A1, A2, A3 · SEMANTIC ⚠`

**Axiom A4 · AxGlobalGround (SEM).**
\[ ∀ φ, □ φ → ∃ e, ∀ w, ExistsAt(w, e) ∧ Ground(e, φ) \]
A formula true in every world is grounded by a single entity that exists in every world.

*Philosophical cost:* The declared modal price of the argument. The `∀w∃r … → ∃r∀w …` swap is not derivable from the atomic truthmaker (`groundPrinciple_atom`); it posits one necessary ground for every necessarily-true formula, which the worldwise-but-not-uniform model (`CountermodelWorldwiseTruthmaking`) shows is unforced by logic alone.

**Theorem C18 (T7 — necessary truth forces necessary reality (base.txt T7)).**

\[ □ τ → ∃ e, NecessaryEntity(e) ∧ Ground(e, τ) \]

**Proof.** Assume □ τ. The required witness is constructed under **A1**, **A4**. ∎

**Obstruction.** `CountermodelWorldwiseTruthmaking` — Worldwise truthmaking does not entail a uniform necessary ground: the `Bool` model has `∀ w ∃ e` with `ExistsAt w e := e = w` but no entity present in every world.

**Γ's answer.** Γ derives this only under AxGlobalGround; the countermodel shows that the stronger conclusion is not forced by worldwise truthmaking alone.

`Lean: Modal.lean#L74 · uses A1, A2, A4 · SEMANTIC ⚠`

**Corollary C19 (Grounding of the necessary excluded-middle reality under AxGlobalGround).**

\[ ∃ e, NecessaryEntity(e) ∧ Ground(e, (φ ∨ ¬φ)) \]

**Proof.** Follows under **A1**. ∎

**Obstruction.** `CountermodelWorldwiseTruthmaking` — worldwise truthmaking entailing a uniform necessary ground (see Appendix C.1).

**Γ's answer.** Γ derives this only under AxGlobalGround; the countermodel shows that the stronger conclusion is not forced by worldwise truthmaking alone.

`Lean: Modal.lean#L80 · uses A1, A2, A4 · SEMANTIC ⚠`

**Corollary C20 (The reductio shape of the prose).**

If every entity were contingent, no formula could be necessarily true.

\[ (∀ e, Contingent(e)) → ∀ φ, ¬□ φ \]

**Proof.** The required witness is constructed under **A1**. ∎

`Lean: Modal.lean#L86 · uses A1, A2, A4 · SEMANTIC / CONDITIONAL ⚠`

**Axiom A7 · AxPersonalGround (META).**
\[ ∀ f, IsPresentPersonalFeature(f) → ∃ e, NecessaryEntity(e) ∧ GroundProp(e, f) \]
The *necessary* reality grounds the personal features present in the rational act.

*Philosophical cost:* A metaphysical bridge. The necessary reality is asserted to carry the present rational (personal) features without this following from the performative datum: a world whose ultimate reality is impersonal is logically consistent with the premises (impersonal-ground countermodel). Γ names the bridge and pays for it explicitly.

**Axiom A8 · GroundProp (VOCAB).**
\[ GroundProp : Entity → Prop → Prop \]
The grounding relation between an entity and a proposition.

**Theorem C32 (T8 — the necessary reality is personal (PROVEN↑ under the two META bridges declared above)).**

\[ IsPresentPersonalFeature(f) → ∃ e, NecessaryEntity(e) ∧ Personal(e) \]

**Proof.** Assume IsPresentPersonalFeature(f). The required witness is constructed under **A7**, **A8**. ∎

**Obstruction.** `CountermodelImpersonalUltimateGround` — Existence of an ultimate ground does not entail that it is personal: `Personal := False` coexists with an ultimate element.

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: GroundPerson.lean#L112 · uses A2, A5, A7, A8 · METAPHYSICAL ⚠`

**Axiom A9 · GroundPrincipleProp (SEM).**
\[ ∀ f, T(f) → ∃ e, GroundProp(e, f) \]
The §24a atom-grounding principle reflected at the level of propositions.

*Philosophical cost:* A separate positive existential commitment over the whole propositional level — every true proposition, not merely every atomic formula, is guaranteed a ground. Beyond the definitional atom cases this is a substantive semantic postulate, not a theorem the axioms force.

**Theorem C33 (Every present personal feature is grounded in reality).**

(the weak, necessity-free half of §24a that is provable without the META bridges, for completeness)

\[ T(f) → IsPresentPersonalFeature(f) → ∃ e, GroundProp(e, f) \]

**Proof.** Assume T(f), and IsPresentPersonalFeature(f). Follows under **A8**, **A9**. ∎

`Lean: GroundPerson.lean#L120 · uses A2, A5, A8, A9 · SEMANTIC ⚠`

**Corollary C34 (§24a applied to a necessary truth yields a grounder).**

(linking Prop-level and world-level principles: T7 supplies the necessary entity)

\[ □ τ → ∃ e, NecessaryEntity(e) \]

**Proof.** Assume □ τ. The required witness is constructed under **A1**. ∎

`Lean: GroundPerson.lean#L125 · uses A1, A2, A4 · SEMANTIC ⚠`

**Open problem Q7.2 (Simulated world-existence).**

The subject exists only in the `true` world.

**Status: OPEN.**

`Lean: HostileSemantics.lean#L642 · OPEN ANSWERED`


### Stage VII — Plurality and Relation

Right and wrong are interpersonal. The unit world satisfies a single act with no second subject, so plurality is not derived: it is bought with `AxTwoSubjects`. Plurality also exhibits the acting subject (C48) and reaches the distinctness of correct and incorrect judging (C30) and the judge's choice field (C55). From two distinct persons the directed-pair and interpersonal-value steps follow.

**Definition (Interpersonal relations).** Affects(s, t) := s ≠ t, Alone(s) := ∀ t, t = s, Helps(s, t) := Affects(s, t), and Harms(s, t) := False.

**Theorem C40 (There are at least two distinct persons).**

\[ ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ \]

**Proof.** T12 — there is more than one person (poem P5/P7; PROVEN↑ under `AxTwoSubjects`): the reality of right-and-wrong demands plurality. A(single, act) does not entail plurality (settled by the Unit countermodel in HostileSemantics). Footprint: `{AxTwoSubjects}`. ∎

**Obstruction.** `CountermodelUnitPlurality` — A single act (one subject) cannot force a plurality of subjects: the unit model with `Person := True` satisfies act and personhood but has no second subject.

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Plurality.lean#L44 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C48 (The acting subject is exhibited from plurality).**

Someone acts on something.

\[ ∃ s, p, A(s, p) \]

**Proof.** cogito, RESTATED AS A(COROLLARY, OF) PLURALITY: from the demonstrated pair of persons, an act occurs. ∎

`Lean: Plurality.lean#L57 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C30 (Correct and incorrect judging are distinct).**

Correctness is not incorrectness.

\[ ¬(∀ s, p, Correct(s, p) ↔ Incorrect(s, p)) \]

**Proof.** Evaluating by disjunctive cases under **A2**. ∎

`Lean: Order.lean#L107 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C55 (The judge is before a choice field).**

Whoever judges acts, correctly or incorrectly.

\[ ∃ s, p, q, A(s, p) ∧ (Correct(s, p) ∨ Incorrect(s, p)) ∧ ChoiceField(s, p, q) \]

**Proof.** "There is no right and wrong without (a field of) choice" (IM_STUPID.md §1–§2): the judgment act — a subject asserting a content that is correct-or-incorrect (§8) — IS set against the incompatible alternative `¬p`. From `cogito_from_T12` (a meaning-act(with, content) p; corollary of the exhibited `Agency.Cogito`, 2026-09-17) + bivalence (p is right-or-wrong) + `Incompatible(p, ¬p)` (pure logic). ∎

`Lean: Order.lean#L127 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Proposition C56 (A lone subject neither helps nor harms anyone else).**

\[ Alone(s) → (¬∃ t, t ≠ s ∧ Helps(s, t)) ∧ (¬∃ t, t ≠ s ∧ Harms(s, t)) \]

**Proof.** P6, whole — a lone subject helps no other AND harms no other (under **A2**). ∎

`Lean: Value.lean#L97 · uses A2 · DEFINITIONAL ✔`

**Theorem C46 (Right-and-wrong yields two distinct persons who bear on each other).**

\[ (¬N_T ∧ ¬N_F) → ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ ∧ (Affects(s₁, s₂) ∨ Affects(s₂, s₁)) \]

**Proof.** Recovery theorem: the exact statement of the deleted `AxValueInterpersonal` (line 70-73, 2026-09-14) is a theorem of the split — no strength lost. ∎

`Lean: Value.lean#L151 · uses A2, A5, A6 · METAPHYSICAL / CONDITIONAL ⚠`

**Theorem C47 (There are two distinct persons where one bears on the other).**

\[ ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ ∧ Affects(s₁, s₂) \]

**Proof.** T12, directed form (chain node C47): the two-person pair can be oriented so that affectivity flows named-forward — under A3 (`Affects(s, t) := s ≠ t`) distinctness IS the forward direction. ∎

`Lean: Plurality.lean#L130 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C74 (No person is alone).**

There is no personal lone subject under the plurality bridge.

\[ ¬∃ s, Person(s) ∧ Alone(s) \]

**Proof.** `aloneExcluded` — under `AxTwoSubjects`, a lone person is excluded: there exist distinct persons, so no single subject can encompass all subjects. Footprint: `{AxTwoSubjects}`. ∎

**Obstruction.** `CountermodelUnitPlurality` — one act forcing a plurality of subjects (see Appendix C.1).

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Value.lean#L128 · uses A2, A5, A6 · METAPHYSICAL ⚠`


### Stage VIII — Love

Given two distinct persons, love is defined as the mutual help that does not harm. C41–C45 derive an eternal love-relation between two persons; plurality alone still does not force love — that is the separate bridge content.

**Definition (Love).** Loves(s, t) := Helps(s, t) ∧ ¬Harms(s, t) and Lovable(t) := ∃ s, s ≠ t ∧ Person(s).

**Theorem C41 (There are two distinct persons, both lovable).**

\[ ∃ s, t, Person(s) ∧ Person(t) ∧ s ≠ t ∧ Lovable(s) ∧ Lovable(t) \]

**Proof.** T13 — there is someone able to be loved (poem P7; PROVEN from T12): each member of the two-person pair is lovable by the other. ∎

**Obstruction.** `CountermodelPluralityWithoutLove` — Plurality of distinct persons does not entail love: `Bool` with `Person := True` and `Loves := False`.

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Love.lean#L81 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C42 (Two distinct persons stand in an eternal love-relation, and both persist in every world).**

\[ ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ ∧ Loves(s₁, s₂) ∧ NecessarySubject(s₁) ∧ NecessarySubject(s₂) \]

**Proof.** T14 — the eternal love-relation: a pair of distinct persons who love each other, both of whose entity-correlates exist in *every* world — the poem's "Amar é escolhido e também é necessário (de alguma forma)". Built on the directed pair `Plurality.T12_directedPair` (C47): direction and stability live on the *same* pair. Footprint: `{AxTwoSubjects}`. ∎

**Obstruction.** `CountermodelPluralityWithoutLove` — plurality entailing love (see Appendix C.1).

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Love.lean#L159 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C43 (Two distinct persons stand in a love-relation).**

\[ ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ ∧ Loves(s₁, s₂) \]

**Proof.** The eternal relation's *content*: there is a pair of loving persons (from T14_eternalRelation, past the stability half). ∎

**Obstruction.** `CountermodelPluralityWithoutLove` — plurality entailing love (see Appendix C.1).

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Love.lean#L194 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Theorem C44 (In every world, two distinct persons stand in a love-relation).**

\[ ∀ w, ∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ ∧ Loves(s₁, s₂) ∧ ExistsAt(w, EntityOf(s₁)) ∧ ExistsAt(w, EntityOf(s₂)) \]

**Proof.** T14, world-anchored form (`NecessityPH`): in every world there is a pair of distinct persons who love each other and whose entity-correlates exist in that world. This is the honest, world-indexed content of "eternal" — the love-relation, the relata, and the stability (from AxPersonStability). ∎

**Obstruction.** `CountermodelPluralityWithoutLove` — plurality entailing love (see Appendix C.1).

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Love.lean#L172 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Corollary C45 (Necessarily, two distinct persons stand in a love-relation).**

\[ □(∃ s₁, s₂, Person(s₁) ∧ Person(s₂) ∧ s₁ ≠ s₂ ∧ Loves(s₁, s₂)) \]

**Proof.** T14 in the *alias* modality (C1: `Necessity(p) := ∀ w, p`) — the image of the old statement shape `□(∃ loving pair)`, now a theorem by unfolding. ∎

**Obstruction.** `CountermodelPluralityWithoutLove` — plurality entailing love (see Appendix C.1).

**Γ's answer.** the step rests on a substantive metaphysical bridge, not logic alone.

`Lean: Love.lean#L184 · uses A2, A5, A6 · METAPHYSICAL ⚠`

**Proposition C85 (Helping excludes harming).**

Benevolence is incompatible with malice.

\[ ∀ s, t, Helps(s, t) → ¬Harms(s, t) \]

**Proof.** Benevolence principle: in the foundational order, what helps does not harm (under **A2**). ∎

`Lean: Value.lean#L78 · uses A2 · DEFINITIONAL ✔`

**Proposition C86 (Love implies positive help).**

The lover benefits the beloved.

\[ ∀ s, t, Loves(s, t) → Helps(s, t) \]

**Proof.** Loving unfolds to benevolence: loving entails helping (under **A2**). ∎

`Lean: Love.lean#L47 · uses A2 · DEFINITIONAL ✔`


### Stage IX — The Remaining Metaphysical Frontier

The remaining frontier is explicit: teleology, the moral good, the Trinity, incarnation and creation are deferred or faith data; the initiation-theoretic and ground-chain constructions are withdrawn under hostile semantics. Nothing here is presented as derived.

**Open problem F2 (Deontic teleology is deferred).**

How norms point at goals is not yet derived.

**Status: OPEN.**

`Lean: n/a · OPEN ➖`

**Open problem F3 (Moral good from logical normativity is deferred).**

Not yet derived.

**Status: OPEN.**

`Lean: n/a · OPEN ➖`

**Open problem F6 (The Trinity is deferred).**

No argument exists yet.

**Status: OPEN.**

`Lean: n/a · OPEN ➖`

**Open problem F8 (The Trinity is not attempted).**

**Status: OPEN.**

`Lean: n/a · OPEN ➖`

**Open problem F9 (Incarnation and creation are faith data from the poem, deferred).**

**Status: OPEN.**

`Lean: n/a · OPEN ➖`


## 4. Where the deduction stops

The frontier is the set of claims that are not currently derived. An **OPEN** claim has no kernel node (blocked, deferred, answered, or a missing lemma) and is listed below. A **COUNTERMODEL** claim is a proposed inference that a hostile model refutes: the step is *withdrawn*, and what survives is recorded in Appendix C.2. The premier frontier is genuine choice (F1b).

- **F1b** — Genuine choice exists \((\exists s\,p\,q,\; Chooses(s,p,q))\) _(countermodel: `CountermodelVeridicalMeaning`, `CountermodelNoFreeWill`)_
- **F2** — Deontic teleology is deferred
- **F3** — Moral good from logical normativity is deferred
- **F6** — The Trinity is deferred
- **Q7.2** — Simulated world-existence
- **F7** — The bipolar half of freedom is subsumed by unary `FreeWill`
- **F8** — The Trinity is not attempted
- **F9** — Incarnation and creation are faith data from the poem, deferred

**§28 open bridges.** The prose corpus lists the still-missing named lemmas: #7 `NecessaryEntity e → ∃ τ, Ground e τ`; #8 the target opposite of #7; #9 `Ground(e, personal) → Personal(e)`; #10 its target. Each appears above in the open inventory; none is silently assumed.

---

## Appendix A — Formal notation

Each step is the real Lean declaration, rendered in logic symbols by the `humanise` pipeline; the English meaning lives in code (docstrings / String constants).

| Symbol | Lean | Meaning |
|---|---|---|
| `\[ … \]` · `\( … \)` | (display/inline math) | standard mathematical display convention for formal statements |
| `¬` · `∧` · `∨` · `→` | `Not` · `And` · `Or` · `Imp` | negation, conjunction, disjunction, implication |
| `φ ∨ ¬φ` | `Form.or φ (Form.not φ)` | object-language formula (not `Prop`) |
| `τ` · `φ` | `Form` | formula/content of the object language |
| `∃ s p q, …` | `∃ (s : Subject), …` | quantifier binder types stripped by `mathify` for concise presentation |
| `□ τ` | `NecessarilyTrue τ` | true in every world (`∀ w, TrueAt w τ`) |
| `¬◇ τ` | `NecessarilyFalse τ` | false in every world (impossible: `∀ w, FalseAt w τ`) |
| `□ p` | `Necessity p` | box at the `Prop` level (degenerate identity alias, `□p := p`) |
| `□ₚ P` · `∀ w, P(w)` | `NecessityPH P` | world-level box — the real modality |
| `◇ p` | `Dia p` | possibility: `¬□(¬p)` |
| `w ⊨ τ` | `TrueAt w τ` / `Satisfies w τ` | τ is true in world w |
| `w ⊭ τ` | `FalseAt w τ` | τ is false in world w |
| `atom n` | `Form.atom n` | atomic proposition n of the object language |
| `T p` | `T p` (`def T p := p`) | "p is true" — truth is identity (E0) |
| `IsFalse p` | `IsFalse p` | "p is false" (`:= ¬ T p`) |
| `N_T` ≡ `N_F` | `N_T` · `N_F` | absolutes: "nothing is true" · "everything is true" |
| `A s p` · `Means s p` | `A s p` (`:= Means s p`) · `Means s p` (`:= ∃ w w', Initiates s w w' p`) | a subject's act on a content — the initiation of a movement |
| `Agent s` · `SubjectExists s` | `Agent s` (`:= True`) · `SubjectExists s` (`:= ∃ p, Act s p`) | nominal agent predicate; subject-actuality is constitutive via `Act` |
| `Subject` · `Person s` | `Subject` · `Person s` | sort of subjects · "s is a person" |
| `Chooses s p q` | `Chooses s p q` | subject s chooses between alternatives p and q |
| `Ground e τ` · `ExistsAt w e` | `Ground e τ` · `ExistsAt w e` | entity e grounds τ · e exists in world w |
| `NecessaryEntity e` · `NecessarySubject s` | `NecessaryEntity e` · `NecessarySubject s` | e exists in every world · s persists in every world |
| `Correct s p` · `Incorrect s p` · `Fallible s p` | `Correct` · `Incorrect` · `Fallible` | correct · incorrect · fallible judgment of subject s about p |
| `Incompatible p q` · `Lovable s` · `Loves s₁ s₂` | `Incompatible` · `Lovable` · `Loves` | incompatible alternatives · s is lovable · s₁'s love of s₂ |

---

## Appendix B — Axiom ledger (10 declarations)

| Axiom | A# | Tag | Meaning (EN) | Depended on by |
|---|---|---|---|---|
| `Ground` | A1 | `VOCAB` | The truthmaker relation — an entity grounding a formula. | C15, C18, C19, C20, C34, C60 |
| `Subject` | A2 | `VOCAB` | Vocabulary: the pure sort of subjects — that which performs acts of reasoning. | C15, C18, C19, C20, C21, C23, C24, C25, C28, C29, C30, C32, C33, C34, C39, C40, C41, C42, C43, C44, C45, C46, C47, C48, C49, C51, C52, C53, C54, C55, C56, C57, C58, C60, C61, C62, C68, C74, C77, C83, C84, C85, C86, C91, C92, C94, F1b, FAITH-2 |
| `Truthmaker` | A3 | `SEM` | The truthmaker principle: truth is grounded in reality. | C15, C60 |
| `AxGlobalGround` | A4 | `SEM` | AxGlobalGround (SEM): a formula true in every world is grounded by a single entity that exists in every world. | C18, C19, C20, C34 |
| `Means` | A5 | `VOCAB` | Vocabulary: the meaning-act relation — a subject means a proposition. | C21, C23, C24, C25, C28, C29, C30, C32, C33, C39, C40, C41, C42, C43, C44, C45, C46, C47, C48, C49, C51, C52, C53, C54, C55, C57, C61, C62, C68, C74, C77, C83, C84, C92, C94, F1b, FAITH-2 |
| `AxTwoSubjects` | A6 | `META` | AxTwoSubjects (META; poem P5/P7, failure traces in DESIGN.md D14 and HostileSemantics): the *reality* of right-and-wrong demands that there be at least two distinct persons. Narrower than the former single bridge `AxValueInterpersonal` (plurality only… | C28, C29, C30, C40, C41, C42, C43, C44, C45, C46, C47, C48, C54, C55, C61, C74, FAITH-2 |
| `AxPersonalGround` | A7 | `META` | AxPersonalGround (META): the *necessary* reality grounds the personal features present in the rational act. | C32 |
| `GroundProp` | A8 | `VOCAB` | The grounding relation between an entity and a proposition. | C32, C33 |
| `GroundPrincipleProp` | A9 | `SEM` | The §24a atom-grounding principle reflected at the level of propositions. | C33 |
| `act` | A10 | `VOCAB` | Vocabulary: weak act / performed event — something is performed, uttered, asserted, or denied. | C58 |

### Kernel declarations

- `Logos.Agency.Means`
- `Logos.Agency.Subject`
- `Logos.Agency.act`
- `Logos.GroundPerson.AxPersonalGround`
- `Logos.GroundPerson.GroundPrincipleProp`
- `Logos.GroundPerson.GroundProp`
- `Logos.Modal.AxGlobalGround`
- `Logos.Truthmaker.Ground`
- `Logos.Truthmaker.Truthmaker`
- `Logos.Value.AxTwoSubjects`

### Withdrawn / demoted axioms (history only)

Kept so a stale GAPMAP footprint referencing them is flagged; never used for status: `AxPersonStability`, `ExistsAt`.

---

## Appendix C — Obstructions & retired alternatives

A hostile model is a self-contained Lean structure in which the premises hold and the disputed inference fails. C.1 is the model reference; C.2 lists the proposed steps those models retire; C.3 lists the dissolved aliases. Each step's inline **Obstruction** line points back here.

### C.1 Countermodel reference

- **`CountermodelWeakActWithoutMeaning`** — The mechanical event: *attacks* a performed event entailing intentional meaning (`act → Act`). Refutes: A performed event (utterance, keystroke, physical emission) does not entail an intentional meaning-act: `act s p` can occur without `Means s p`. **What survives:** The weak retorsion proves directly only that an act-event occurs; the step from event to meaning requires the explicit intentionality bridge `weak_act_implies_strong_act`. · `Logos.HostileSemantics.CountermodelWeakActWithoutMeaning` · [HostileSemantics.lean#L377](formal/Logos/HostileSemantics.lean#L377)
- **`CountermodelActWithoutSubject`** — The void act (Lichtenberg): *attacks* an act occurring with no actualizing subject. Refutes: Without a constitutive rule, an act can occur in the void with no actualizing subject (Lichtenberg's objection). **What survives:** In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication. · `Logos.CountermodelActWithoutSubject` · [HostileSemantics.lean#L333](formal/Logos/HostileSemantics.lean#L333)
- **`CountermodelSubjectWithoutPerson`** — The unpredicated subject: *attacks* `Subject → Person` as a logical law. Refutes: A subject of an act need not be a person: if `Person` is an uninterpreted substantive predicate, `Subject → Person` fails as a logical law. **What survives:** Under §12 the identity `Person s ↔ ∃ p, Act s p` makes personhood definitional, so the implication holds in Γ by analysis, not by logic. · `Logos.HostileSemantics.CountermodelSubjectWithoutPerson` · [HostileSemantics.lean#L409](formal/Logos/HostileSemantics.lean#L409)
- **`CountermodelNoPerson`** — The personless act: *attacks* the bare act datum forcing `Person`. Refutes: The bare act-datum `∃ s p, A s p` does not force any `Person`. **What survives:** Personhood is introduced by the definition of Act (esse est agere), not by the raw datum. · `Logos.HostileSemantics.CountermodelNoPerson` · [HostileSemantics.lean#L435](formal/Logos/HostileSemantics.lean#L435)
- **`CountermodelNoFreeWill`** — The determined act: *attacks* `Act → Chooses` / `Act → FreeWill`. Refutes: Mere occurrence of an act does not entail genuine choice: an uninterpreted determined act with `Chooses := False` satisfies the datum while `Chooses` and `FreeWill` stay empty. **What survives:** `Chooses → FreeWill` holds in Γ by definition (`FreeWill s := ∃ p q, Chooses s p q`); the countermodel attacks the existence of genuine choice, not the implication. · `Logos.HostileSemantics.CountermodelNoFreeWill` · [HostileSemantics.lean#L454](formal/Logos/HostileSemantics.lean#L454)
- **`CountermodelUnitPlurality`** — The unit world: *attacks* one act forcing a plurality of subjects. Refutes: A single act (one subject) cannot force a plurality of subjects: the unit model with `Person := True` satisfies act and personhood but has no second subject. **What survives:** Plurality rests on `AxTwoSubjects` (the reality of right-and-wrong demands two subjects), not on the mere act. · `Logos.HostileSemantics.UnitPluralityCountermodel` · [HostileSemantics.lean#L471](formal/Logos/HostileSemantics.lean#L471)
- **`CountermodelContentWithoutPerson`** — Content without a person: *attacks* content existence entailing personhood. Refutes: Propositional existence plus meaning does not entail personhood: `S := Prop`, `Means s p := s = p`, `Person := False`. **What survives:** Content-existence is a distinct step from personhood; the definitional link `Person s ↔ ∃ p, Act s p` is what Γ uses, not a logical law. · `Logos.HostileSemantics.PropositionalPersonhood.CountermodelContentWithoutPerson` · [HostileSemantics.lean#L489](formal/Logos/HostileSemantics.lean#L489)
- **`CountermodelWorldwiseTruthmaking`** — Worldwise but not uniform: *attacks* worldwise truthmaking entailing a uniform necessary ground. Refutes: Worldwise truthmaking does not entail a uniform necessary ground: the `Bool` model has `∀ w ∃ e` with `ExistsAt w e := e = w` but no entity present in every world. **What survives:** For atoms the swap is a theorem without axioms; the compound/global instance is exactly what `AxGlobalGround` supplies. · `Logos.HostileSemantics.CountermodelWorldwiseTruthmaking` · [HostileSemantics.lean#L514](formal/Logos/HostileSemantics.lean#L514)
- **`CountermodelSubjectNecessityNotEntity`** — Persistence without entity: *attacks* subject-persistence entailing entity-necessity by logic alone. Refutes: Subject-persistence does not entail entity-necessity by logic alone: the transfer fails with independent persistence/existence predicates. **What survives:** In Γ `EntityOf` is the Truthmaker embedding and `ExistsAt` is one shared relation, so the lift (C91) is definitional, not a logical law. · `Logos.HostileSemantics.CountermodelSubjectNecessityNotEntityNecessity` · [HostileSemantics.lean#L553](formal/Logos/HostileSemantics.lean#L553)
- **`CountermodelPersonNotNecessary`** — The contingent person: *attacks* `Person → NecessarySubject` as a logical law. Refutes: A person need not be a necessary subject: `Person → NecessarySubject` fails as a logical law (subject exists only in the `true` world). **What survives:** Person-persistence is definitional (esse est agere, `AxPersonStability`), and `Love.no_contingent_person` shows the concrete refutation cannot exist in Γ. · `Logos.HostileSemantics.CountermodelPersonNotNecessary` · [HostileSemantics.lean#L636](formal/Logos/HostileSemantics.lean#L636)
- **`CountermodelVeridicalMeaning`** — Veridical meaning (one and two persons): *attacks* the act datum forcing genuine choice. Refutes: The act-datum does not force `genuineChoice_exists` even under the Logos definition of `Chooses`: veridical meaning makes co-meaning an incompatible pair impossible while the whole agency/choice/order fragment holds. **What survives:** The frontier is not the implication `Chooses → FreeWill` but whether any subject co-means an incompatible horn — the single irreducible resource is `rejectedHornCoMeant` (BLOCKED). · `Logos.HostileSemantics.CountermodelVeridicalMeaning` · [HostileSemantics.lean#L701](formal/Logos/HostileSemantics.lean#L701)
- **`CountermodelInfiniteGroundChain`** — The infinite descending chain: *attacks* grounding forcing an ultimate element. Refutes: A strict partial order need not have an ultimate element: descending infinite chains in `Int` have none. **What survives:** Γ never claimed order-theoretic well-foundedness; the missing assumption (if adopted) would be a further axiom, not a hidden theorem. · `Logos.HostileSemantics.CountermodelInfiniteGroundChain` · [HostileSemantics.lean#L945](formal/Logos/HostileSemantics.lean#L945)
- **`CountermodelImpersonalUltimateGround`** — The impersonal ultimate: *attacks* an ultimate ground entailing a personal one. Refutes: Existence of an ultimate ground does not entail that it is personal: `Personal := False` coexists with an ultimate element. **What survives:** Personal grounding is the content of `AxPersonalGround` (T8), a META bridge whose cost is explicit, not a consequence of grounding alone. · `Logos.HostileSemantics.CountermodelImpersonalUltimateGround` · [HostileSemantics.lean#L980](formal/Logos/HostileSemantics.lean#L980)
- **`CountermodelPluralityWithoutLove`** — Plurality without love: *attacks* plurality entailing love. Refutes: Plurality of distinct persons does not entail love: `Bool` with `Person := True` and `Loves := False`. **What survives:** Love follows in Γ from the definitions plus `AxTwoSubjects` — substantive relational bridges, not a logical consequence of plurality. · `Logos.HostileSemantics.CountermodelPluralityWithoutLove` · [HostileSemantics.lean#L1009](formal/Logos/HostileSemantics.lean#L1009)

### C.2 Retired and rejected alternatives

- **C78** — Contingent ground is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C79** — Ultimate ground existence is blocked · `CountermodelInfiniteGroundChain` · what survives: Γ never claimed order-theoretic well-foundedness; the missing assumption (if adopted) would be a further axiom, not a hidden theorem.
- **C87** — Origin necessity is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C88** — Transcendental quantifier swap is retired · `CountermodelWorldwiseTruthmaking` · what survives: For atoms the swap is a theorem without axioms; the compound/global instance is exactly what `AxGlobalGround` supplies.
- **C89** — Ultimate ground by initiation is blocked · `CountermodelInfiniteGroundChain` · what survives: Γ never claimed order-theoretic well-foundedness; the missing assumption (if adopted) would be a further axiom, not a hidden theorem.
- **C90** — Personal ultimate ground is blocked · `CountermodelImpersonalUltimateGround` · what survives: Personal grounding is the content of `AxPersonalGround` (T8), a META bridge whose cost is explicit, not a consequence of grounding alone.
- **C69** — Free will of origin is retired · `CountermodelNoFreeWill`, `CountermodelVeridicalMeaning` · what survives: `Chooses → FreeWill` holds in Γ by definition (`FreeWill s := ∃ p q, Chooses s p q`); the countermodel attacks the existence of genuine choice, not the implication. The frontier is not the implication `Chooses → FreeWill` but whether any subject co-means an incompatible horn — the single irreducible resource is `rejectedHornCoMeant` (BLOCKED).
- **C70** — Posited content non-freedom is retired · `CountermodelNoFreeWill`, `CountermodelVeridicalMeaning` · what survives: `Chooses → FreeWill` holds in Γ by definition (`FreeWill s := ∃ p q, Chooses s p q`); the countermodel attacks the existence of genuine choice, not the implication. The frontier is not the implication `Chooses → FreeWill` but whether any subject co-means an incompatible horn — the single irreducible resource is `rejectedHornCoMeant` (BLOCKED).
- **C71** — Origin freedom denial self-refuting is retired · `CountermodelNoFreeWill`, `CountermodelVeridicalMeaning` · what survives: `Chooses → FreeWill` holds in Γ by definition (`FreeWill s := ∃ p q, Chooses s p q`); the countermodel attacks the existence of genuine choice, not the implication. The frontier is not the implication `Chooses → FreeWill` but whether any subject co-means an incompatible horn — the single irreducible resource is `rejectedHornCoMeant` (BLOCKED).
- **C72** — Judge is free is retired · `CountermodelNoFreeWill`, `CountermodelVeridicalMeaning` · what survives: `Chooses → FreeWill` holds in Γ by definition (`FreeWill s := ∃ p q, Chooses s p q`); the countermodel attacks the existence of genuine choice, not the implication. The frontier is not the implication `Chooses → FreeWill` but whether any subject co-means an incompatible horn — the single irreducible resource is `rejectedHornCoMeant` (BLOCKED).
- **C73** — Plurality without bridges is blocked · `CountermodelUnitPlurality` · what survives: Plurality rests on `AxTwoSubjects` (the reality of right-and-wrong demands two subjects), not on the mere act.
- **C75** — Propositional personhood is blocked · `CountermodelContentWithoutPerson` · what survives: Content-existence is a distinct step from personhood; the definitional link `Person s ↔ ∃ p, Act s p` is what Γ uses, not a logical law.
- **C76** — Canonical rigid love is retired · `CountermodelPluralityWithoutLove` · what survives: Love follows in Γ from the definitions plus `AxTwoSubjects` — substantive relational bridges, not a logical consequence of plurality.
- **C64** — Movement not transfer is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C65** — Person iff originates is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C66** — Cogito as initiation is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C67** — Denial of initiation self-refuting is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C80** — Posited content deterministic transfer is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C81** — Origin branching is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.
- **C82** — Origin initiating person is retired · `CountermodelActWithoutSubject` · what survives: In Γ the Act relation is constitutive — `Act s p → Subject s` by definition — so the void-act is no countermodel to the formal implication.

### C.3 Dissolved aliases

- **F1a** → **C51** (shares `Logos.Choice.person_hasChoiceField`); see that block.
- **F4** → **C41** (shares `Logos.Love.T13_someoneLovable`); see that block.
- **F5** → **C42** (shares `Logos.Love.T14_eternalRelation`); see that block.
- **FAITH-1** → **C38** (shares `Logos.Necessity.necDistinction`); see that block.
- **FAITH-2** → **C42** (shares `Logos.Love.T14_eternalRelation`); see that block.

---

## Appendix D — Lean / kernel audit

### D.1 Kernel-derived status (badges vs. philosophical statuses)

| Machine badge | GAPMAP status | Philosophical status |
|---|---|---|
| `✔` | PROVEN | LOGICAL or DEFINITIONAL |
| `⚠` | PROVEN↑ | SEMANTIC or METAPHYSICAL |
| `◆` | AXIOM | tag of the axiom (`VOCAB`/`SEM`/`META`) |
| `✖` | BLOCKED | OPEN or COUNTERMODEL |
| `➖` | DEFERRED | OPEN |
| `→` | dissolved | cross-reference |
| `CL` | — | classical meta-logic `{propext, Classical.choice, Quot.sound}` |

### D.2 Reconciliation report (kernel ↔ GAPMAP)

- GAPMAP claims with a kernel declaration located (FOUND): **84** / 109
- Steps with an **English meaning in code**: **109** / 109
- **Withdrawn / blocked claims (outside the active deduction) (25):**
  - `C78` (`BLOCKED`) ref `Modal.contingent_ground` — T7
  - `C79` (`BLOCKED`) ref `Modal.ultimateGround_exists` — T7
  - `C87` (`BLOCKED`) ref `Modal.origin_is_necessary` — T7
  - `C88` (`BLOCKED`) ref `Modal.transcendental_quantifier_swap` — T7
  - `C89` (`BLOCKED`) ref `Modal.ultimateGroundInit_exists` — T7
  - `C90` (`BLOCKED`) ref `GroundPerson.personal_ultimate_ground_exists` — T8
  - `F2` (`DEFERRED`) ref `—` — §21 teleology (`Ought → Goal`)
  - `F3` (`DEFERRED`) ref `—` — §28 Good (`§20 → bem`)
  - `F6` (`DEFERRED`) ref `—` — §28 Trinity
  - `C69` (`BLOCKED`) ref `—` — §15/F1b
  - `C70` (`BLOCKED`) ref `—` — §15/F1b
  - `C71` (`BLOCKED`) ref `—` — §15/F1b
  - `C72` (`BLOCKED`) ref `—` — §15/F1b
  - `C73` (`BLOCKED`) ref `Person.twoPersonsFromSubject` — P5/P7
  - `C75` (`BLOCKED`) ref `Person.everyContentIsAPerson` — P7
  - `C76` (`BLOCKED`) ref `Love.T14_canonicalRigid` — P8
  - `C64` (`BLOCKED`) ref `Initiation.originates_not_transfer` — §1
  - `C65` (`BLOCKED`) ref `Initiation.person_iff_originates` — §1/T5
  - `C66` (`BLOCKED`) ref `Initiation.Cogito_Init` — §1 fnd
  - `C67` (`BLOCKED`) ref `Initiation.noInitiation_selfRefutes` — §1 fnd
  - `C80` (`BLOCKED`) ref `Initiation.posited_not_branch` — §1
  - `C81` (`BLOCKED`) ref `Initiation.origin_branches` — §1
  - `C82` (`BLOCKED`) ref `Initiation.origin_is_initiating_person` — §1/§12
  - `F8` (`DEFERRED`) ref `—` — Trinity
  - `F9` (`DEFERRED`) ref `—` — Incarnation / creation
- Kernel theorems **without a GAPMAP claim** (106): Agency.Cogito_of_bridge, Agency.T1_subjectExists_of_act, Agency.act_exists_of_assert, Agency.act_implies_agent, Agency.act_implies_content, Agency.act_implies_means, Agency.act_implies_rational, Agency.act_of_asserting_no_act, Agency.act_requires_subject, Agency.an_actual_subject_exists_of_act, Agency.assertion_is_act, Agency.assertion_is_weak_act, Agency.noAct_conditional_selfRefutes, Agency.noCogito_selfRefutes, Agency.noSubjectSort_selfRefutes, Agency.noSubject_performative_selfRefutes, Agency.noSubject_selfRefutes, Agency.strong_act_of_weak_act, Agency.subject_exists_of_act, Agency.subject_exists_of_assert, Agency.weak_Cogito, Agency.weak_act_exists_of_assert, Choice.T11_choiceField_from_plurality, Choice.asserting_noChoiceField_is_choiceField, Choice.assertion_consistency, Choice.canChoose_unfold, Choice.choiceField_exists_from_plurality, Choice.chooses_implies_freeWill, Choice.freeWillExists_of_chooses, Choice.freeWillExists_of_genuineChoice, Choice.genuineChoice_requires_error_possibility, Choice.intentional_hasChoiceField, Choice.judge_asserting_rightWrong_has_choiceField, Choice.meaning_I_needs_subject, Choice.noChoiceField_contradicts_field, Choice.noSubject_contradicts_subject, Choice.no_one_asserts_incompatible_pair, Choice.rejectedHornCoMeant_implies_genuineChoice, Core.atomicWitnessFalsehood, Core.someTruthAndSomeFalsehood, Core.tschema, GroundPerson.AxGroundBearing, HostileSemantics.act_exists_of_act, HostileSemantics.not_entails_content_person, HostileSemantics.not_entails_decoupled_freewill, HostileSemantics.not_entails_person, HostileSemantics.not_entails_plurality, HostileSemantics.not_entails_substantive_autonomy, HostileSemantics.not_entails_substantive_intentionality, HostileSemantics.not_entails_substantive_person, HostileSemantics.not_entails_substantive_rationality, HostileSemantics.subject_exists_of_act, Love.AxPersonStability, Love.love_affects, Love.love_not_harms, Love.loves_of_helps, Love.no_contingent_person, Modal.necessary_entity_exists_of_necessary_subject, Modal.subject_nec_entity_nec_iff, Necessity.dia_def, Necessity.nec4, Necessity.nec4PH, Necessity.necDistinction_content, Necessity.necK, Necessity.necKPH, Necessity.necMP, Necessity.necT, Necessity.necTPH, Necessity.nec_apply, Order.fallible_false, Order.judgment_implies_act, Order.judgment_implies_cogito, Order.judgment_of_no_act_is_incorrect, Order.rightDistinctWrong_implies_meaning, Order.rightWrongDistinction_implies_meaning, Person.act_implies_intentional, Person.intentional_implies_subjectExists, Person.person_exists_of_act, Person.person_exists_of_assert, Person.person_intentional_iff, Person.person_of_act, Person.person_of_subject, Person.subjectExists_implies_intentional, Plurality.T1_of_assert, Plurality.T1_subjectExists_from_plurality, Plurality.T4_agentExists_from_plurality, Plurality.T4_of_assert, Plurality.T5_of_assert, Plurality.T5_personExists_from_plurality, Plurality.notAlone, Semantics.atom_not_necessarily_false, Semantics.atom_not_necessarily_true, Semantics.sat_and, Semantics.sat_imp, Semantics.sat_not, Semantics.sat_or, Semantics.strongTruth_and_contingent_content, Semantics.strongTruth_is_not_atomic, Truthmaker.sat_ground_and, Truthmaker.sat_ground_imp, Truthmaker.sat_ground_not, Truthmaker.sat_ground_or, Value.AxPersonsAffect, Value.alone_no_other_affects, Value.harm_affects, Value.help_affects
- **Kernel-derived status** (#print axioms + axiom `Tag:`): **52 ✔** · **24 ⚠** · **0 ◆** (unique steps detailed in the map)
- **Reconciled claim inventory (109 total):** 76 unique active steps (52 ✔ + 24 ⚠) · 5 repeated / dissolved (→) · 22 blocked / missing (✖) · 5 deferred (➖) · 1 other (ANSWERED)
- **Philosophical status histogram:** **COUNTERMODEL 20** · **DEFINITIONAL 22** · **DISSOLVED 5** · **LOGICAL 30** · **METAPHYSICAL 17** · **OPEN 8** · **SEMANTIC 7**
- GAPMAP × derived status: **no divergences** (transcription verified).
- **Steps ⚠ under a substantive axiom (SEM/META)** (26): C15, C18, C19, C20, C28, C29, C30, C32, C33, C34, C40, C41, C42, C43, C44, C45, C46, C47, C48, C54, C55, C60, C61, C74, F4, F5
- **Displayed ✔ by vocabulary only (axiom-free modulo declared vocabulary)** (kernel footprint contains only the statement's own VOCAB axioms — no SEM/META/TRANS): C21, C23, C24, C25, C39, C49, C51, C52, C53, C56, C57, C58, C62, C68, C77, C83, C84, C85, C86, C91, C92, C94, F1a
- Kernel × GAPMAP footprint: **no divergences**.
- **Graph (closure) × audit (#print axioms) diverge on 1 claims** (depviz transitive undercount — toolchain, not ledger; the audit decides):
  - `FAITH-2` audit `{AxTwoSubjects, Means, Subject}` vs graph `{}`
- Axioms declared in the kernel: **10** — **all carry a `Tag:` line on their Lean docstring**

### D.3 Blocked / deferred / faith inventory

| ID | Prose | Status | Missing lemma / meaning (EN) |
|---|---|---|---|
| F1a | §13–§15 choice-field existence (`∃s p q`, `ChoiceField s p q`) | DISSOLVED | Any person has a choice field: a person is always before two incompatible alternatives. |
| F1b | §15 genuine choice & freedom of the actor | OPEN | Genuine choice exists: some subject co-means two incompatible contents; that existence itself remains blocked. The modal side of openness is settled and inert — `atoms_are_modally_free` (C95) and… |
| F2 | §21 teleology (`Ought → Goal`) | OPEN | Deontic teleology is deferred: how norms point at goals is not yet derived. |
| F3 | §28 Good (`§20 → bem`) | OPEN | Moral good from logical normativity is deferred: not yet derived. |
| F4 | §28 Love | DISSOLVED | There are two distinct persons, both lovable. |
| F5 | §28 EternalRelation | DISSOLVED | Two distinct persons stand in an eternal love-relation, and both persist in every world. |
| F6 | §28 Trinity | OPEN | The Trinity is deferred: no argument exists yet. |
| Q7.2 | weaker `AxGlobalGround` | OPEN | Simulated world-existence: the subject exists only in the `true` world. |
| FAITH-1 | P2 necessity | DISSOLVED | The distinction between right and wrong under the identity-model alias. |
| FAITH-2 | P8 eternal love | DISSOLVED | AxTwoSubjects (META; poem P5/P7, failure traces in DESIGN.md D14 and HostileSemantics): the *reality* of right-and-wrong demands that there be at least two distinct persons. Narrower than the former single bridge… |
| F7 | §15 the bipolar half of freedom | OPEN | The bipolar half of freedom is subsumed by unary `FreeWill`; the open gap is not 'freedom impossible to derive' but *existence of genuine choice* not yet derived from the performative datum (F1b… |
| F8 | Trinity | OPEN | The Trinity is not attempted. |
| F9 | Incarnation / creation | OPEN | Incarnation and creation are faith data from the poem, deferred. |

### D.4 Per-claim code annex

<details>
<summary>Lean declaration, file:line, kernel footprint and code dependencies, per claim →</summary>

| ID | Lean declaration | File#L | Kernel axioms | Depends on (Lean) | Used by |
|---|---|---|---|---|---|
| C1 | `Logos.Core.nothingTrueRefutes` | [Core.lean#L61](formal/Logos/Core.lean#L61) | `{}` | `Core.N_T`, `Core.T`, `Core.tschema` | **C2** `notNothingTrue` |
| C2 | `Logos.Core.notNothingTrue` | [Core.lean#L69](formal/Logos/Core.lean#L69) | `{}` | `Core.N_T`, `Core.T`, **C1** `nothingTrueRefutes`, `Core.tschema` | **C35** `negatedAbsolutes`, **C36** `rightWrongDistinction`, **C3** `someTrue` |
| C3 | `Logos.Core.someTrue` | [Core.lean#L77](formal/Logos/Core.lean#L77) | `{CL}` | `Core.N_T`, `Core.T`, **C2** `notNothingTrue` | `Core.someTruthAndSomeFalsehood` |
| C4 | `Logos.Core.atomicTruthWitnessed` | [Core.lean#L85](formal/Logos/Core.lean#L85) | `{}` | `Core.T`, `Core.tschema` | **C26** `T9_incompatibleAlternatives`, **C8** `greatResult` |
| C5 | `Logos.Core.nothingFalseRefutes` | [Core.lean#L94](formal/Logos/Core.lean#L94) | `{}` | `Core.N_F`, `Core.T`, `Core.tschema` | **C6** `notEverythingTrue` |
| C6 | `Logos.Core.notEverythingTrue` | [Core.lean#L103](formal/Logos/Core.lean#L103) | `{}` | `Core.N_F`, `Core.T`, **C5** `nothingFalseRefutes`, `Core.tschema` | **C35** `negatedAbsolutes`, **C36** `rightWrongDistinction` |
| C7 | `Logos.Core.someFalse` | [Core.lean#L111](formal/Logos/Core.lean#L111) | `{}` | `Core.IsFalse`, `Core.T`, `Core.tschema` | `Core.someTruthAndSomeFalsehood`, `Order.fallible_false` |
| C8 | `Logos.Core.greatResult` | [Core.lean#L156](formal/Logos/Core.lean#L156) | `{}` | `Core.IsFalse`, `Core.T`, **C4** `atomicTruthWitnessed`, `Core.atomicWitnessFalsehood` | — |
| C9 | `Logos.Core.noBothTrueAndFalse` | [Core.lean#L162](formal/Logos/Core.lean#L162) | `{}` | `Core.IsFalse`, `Core.T` | — |
| C10 | `Logos.Core.excludedMiddle` | [Core.lean#L174](formal/Logos/Core.lean#L174) | `{CL}` | `Core.T`, `Core.tschema` | — |
| C11 | `Logos.Core.nonContradiction` | [Core.lean#L180](formal/Logos/Core.lean#L180) | `{}` | `Core.T`, `Core.tschema` | — |
| C12 | `Logos.Core.bivalence` | [Core.lean#L186](formal/Logos/Core.lean#L186) | `{CL}` | `Core.IsFalse`, `Core.T` | — |
| C13 | `Logos.Semantics.lawExcludedMiddle` | [Semantics.lean#L76](formal/Logos/Semantics.lean#L76) | `{CL}` | `Semantics.Form`, `Semantics.NecessarilyTrue`, `Semantics.Satisfies`, `Semantics.TrueAt`, `Semantics.World`, `Semantics.sat_not`, `Semantics.sat_or` | **C37** `bothNecessarilyTrueAndFalse`, `Semantics.strongTruth_is_not_atomic` |
| C14 | `Logos.Semantics.nonContradiction` | [Semantics.lean#L85](formal/Logos/Semantics.lean#L85) | `{CL}` | `Semantics.FalseAt`, `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.Satisfies`, `Semantics.World`, `Semantics.sat_and`, `Semantics.sat_not` | **C37** `bothNecessarilyTrueAndFalse` |
| C15 | `Logos.Truthmaker.groundPrinciple_atom` | [Truthmaker.lean#L94](formal/Logos/Truthmaker.lean#L94) | `{Truthmaker, Ground, Subject}` | `Semantics.World`, `Truthmaker.Entity`, `Truthmaker.ExistsAt`, axiom `Ground` (VOCAB), `Truthmaker.TrueAt`, axiom `Truthmaker` (SEM) | — |
| C60 | `Logos.Truthmaker.noGround_selfRefutes` | [Truthmaker.lean#L101](formal/Logos/Truthmaker.lean#L101) | `{Truthmaker, Ground, Subject}` | `Semantics.World`, `Truthmaker.Entity`, `Truthmaker.ExistsAt`, axiom `Ground` (VOCAB), `Truthmaker.TrueAt`, axiom `Truthmaker` (SEM) | — |
| C16 | `Logos.Truthmaker.lawExcludedMiddle` | [Truthmaker.lean#L129](formal/Logos/Truthmaker.lean#L129) | `{CL}` | `Semantics.Form`, `Semantics.World`, `Truthmaker.NecessarilyTrue`, `Truthmaker.TrueAt` | **C19** `T7_excludedMiddleInstance` |
| C17 | `Logos.Truthmaker.nonContradiction` | [Truthmaker.lean#L137](formal/Logos/Truthmaker.lean#L137) | `{}` | `Semantics.Form`, `Semantics.Satisfies`, `Semantics.World`, `Truthmaker.NecessarilyFalse`, `Truthmaker.TrueAt` | — |
| C18 | `Logos.Modal.T7_necessaryReality` | [Modal.lean#L74](formal/Logos/Modal.lean#L74) | `{AxGlobalGround, Ground, Subject}` | axiom `AxGlobalGround` (SEM), `Modal.NecessaryEntity`, `Modal.actualWorld`, `Semantics.Form`, `Semantics.World`, `Truthmaker.Entity`, `Truthmaker.ExistsAt`, axiom `Ground` (VOCAB), `Truthmaker.NecessarilyTrue` | **C34** `necessary_truth_has_necessary_grounder`, **C19** `T7_excludedMiddleInstance`, **C20** `noNecessaryTruthIfAllContingent` |
| C19 | `Logos.Modal.T7_excludedMiddleInstance` | [Modal.lean#L80](formal/Logos/Modal.lean#L80) | `{AxGlobalGround, Ground, Subject, CL}` | `Modal.NecessaryEntity`, **C18** `T7_necessaryReality`, `Semantics.Form`, `Truthmaker.Entity`, axiom `Ground` (VOCAB), **C16** `lawExcludedMiddle` | — |
| C20 | `Logos.Modal.noNecessaryTruthIfAllContingent` | [Modal.lean#L86](formal/Logos/Modal.lean#L86) | `{AxGlobalGround, Ground, Subject}` | `Modal.Contingent`, `Modal.NecessaryEntity`, **C18** `T7_necessaryReality`, `Semantics.Form`, `Truthmaker.Entity`, axiom `Ground` (VOCAB), `Truthmaker.NecessarilyTrue` | — |
| C91 | `Logos.Modal.subject_nec_entity_nec` | [Modal.lean#L103](formal/Logos/Modal.lean#L103) | `{Subject}` | axiom `Subject` (VOCAB), `Modal.NecessaryEntity`, `Plurality.EntityOf`, `Plurality.NecessarySubject` | **C92** `necessary_entity_exists`, `Modal.necessary_entity_exists_of_necessary_subject` |
| C78 | — | — | — | — | Modal.contingent_ground |
| C79 | — | — | — | — | Modal.ultimateGround_exists |
| C87 | — | — | — | — | Modal.origin_is_necessary |
| C88 | — | — | — | — | Modal.transcendental_quantifier_swap |
| C89 | — | — | — | — | Modal.ultimateGroundInit_exists |
| C58 | `Logos.Agency.noWeakAct_selfRefutes` | [Agency.lean#L143](formal/Logos/Agency.lean#L143) | `{Subject, act}` | `Agency.NoWeakAct`, axiom `Subject` (VOCAB), axiom `act` (VOCAB), `Agency.asserts`, `Agency.weak_act_exists_of_assert` | — |
| C68 | `Logos.Agency.Cogito` | [Agency.lean#L222](formal/Logos/Agency.lean#L222) | `{Means, Subject}` | `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Agency.act_exists_of_assert` | — |
| C21 | `Logos.Plurality.T1_subjectExists` | [Plurality.lean#L66](formal/Logos/Plurality.lean#L66) | `{Means, Subject}` | `Agency.Act`, axiom `Subject` (VOCAB), `Agency.SubjectExists`, `Agency.subject_exists_of_act` | **C23** `T4_agentExists` |
| C22 | `Logos.Agency.T2_contentExists` | [Agency.lean#L281](formal/Logos/Agency.lean#L281) | `{}` | `Agency.Content` | — |
| C23 | `Logos.Plurality.T4_agentExists` | [Plurality.lean#L74](formal/Logos/Plurality.lean#L74) | `{Means, Subject}` | `Agency.Act`, `Agency.Agent`, axiom `Subject` (VOCAB), `Agency.SubjectExists`, **C21** `T1_subjectExists` | — |
| C24 | `Logos.Plurality.T5_personExists` | [Plurality.lean#L90](formal/Logos/Plurality.lean#L90) | `{Means, Subject}` | `Agency.Act`, axiom `Subject` (VOCAB), `Person.Person`, `Person.person_exists_of_act` | **C39** `T11_choiceField`, **C77** `necessaryPersonExists`, **C92** `necessary_entity_exists` |
| C25 | `Logos.Person.inseparability_24b` | [Person.lean#L144](formal/Logos/Person.lean#L144) | `{Means, Subject, CL}` | `Agency.A`, axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Agency.act_implies_means`, `Core.IsFalse`, `Core.T`, `Person.CarriesLogicalFeature`, `Person.CarriesPersonalFeature`, `Person.HasFeature`, `Person.RationalAct` | — |
| C26 | `Logos.Alternatives.T9_incompatibleAlternatives` | [Alternatives.lean#L24](formal/Logos/Alternatives.lean#L24) | `{}` | `Alternatives.Incompatible`, `Core.IsFalse`, `Core.T`, **C4** `atomicTruthWitnessed`, `Core.atomicWitnessFalsehood` | **C39** `T11_choiceField`, `Choice.T11_choiceField_from_plurality` |
| C27 | `Logos.Alternatives.incompatible_with_negation` | [Alternatives.lean#L35](formal/Logos/Alternatives.lean#L35) | `{}` | `Alternatives.Incompatible`, `Core.IsFalse`, `Core.T`, `Core.tschema` | — |
| C28 | `Logos.Order.T6_fallibility` | [Order.lean#L90](formal/Logos/Order.lean#L90) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Core.IsFalse`, `Core.T`, `Order.Fallible`, `Order.fallible_false` | — |
| C29 | `Logos.Order.T6_truthTranscendsWill` | [Order.lean#L99](formal/Logos/Order.lean#L99) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Core.IsFalse`, `Core.T`, `Order.Fallible`, `Order.fallible_false` | — |
| C30 | `Logos.Order.correctness_distinct` | [Order.lean#L107](formal/Logos/Order.lean#L107) | `{AxTwoSubjects, Means, Subject, CL}` | `Agency.A`, axiom `Subject` (VOCAB), `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect`, **C48** `cogito_from_T12` | — |
| C31 | `Logos.Order.consequence_preserves_truth` | [Order.lean#L150](formal/Logos/Order.lean#L150) | `{}` | `Core.T`, `Core.tschema` | — |
| C83 | `Logos.Order.no_correct_judgment_of_no_act` | [Order.lean#L159](formal/Logos/Order.lean#L159) | `{Means, Subject}` | `Agency.A`, axiom `Subject` (VOCAB), `Core.T`, `Order.Correct`, `Order.NoAct` | `Order.judgment_of_no_act_is_incorrect` |
| C84 | `Logos.Order.judgment_of_no_act_proves_act` | [Order.lean#L180](formal/Logos/Order.lean#L180) | `{Means, Subject}` | `Agency.A`, axiom `Subject` (VOCAB), `Order.Correct`, `Order.Incorrect`, `Order.NoAct`, `Order.judgment_implies_act` | — |
| C32 | `Logos.GroundPerson.T8_personalGround` | [GroundPerson.lean#L112](formal/Logos/GroundPerson.lean#L112) | `{AxPersonalGround, GroundProp, Means, Subject}` | `GroundPerson.AxGroundBearing`, axiom `AxPersonalGround` (META), axiom `GroundProp` (VOCAB), `GroundPerson.IsPresentPersonalFeature`, `GroundPerson.Personal`, `GroundPerson.Realizes`, `Modal.NecessaryEntity`, `Truthmaker.Entity` | — |
| C33 | `Logos.GroundPerson.present_feature_is_grounded` | [GroundPerson.lean#L120](formal/Logos/GroundPerson.lean#L120) | `{GroundPrincipleProp, GroundProp, Means, Subject}` | `Core.T`, axiom `GroundPrincipleProp` (SEM), axiom `GroundProp` (VOCAB), `GroundPerson.IsPresentPersonalFeature`, `Truthmaker.Entity` | — |
| C34 | `Logos.GroundPerson.necessary_truth_has_necessary_grounder` | [GroundPerson.lean#L125](formal/Logos/GroundPerson.lean#L125) | `{AxGlobalGround, Ground, Subject}` | `Modal.NecessaryEntity`, **C18** `T7_necessaryReality`, `Semantics.Form`, `Truthmaker.Entity`, axiom `Ground` (VOCAB), `Truthmaker.NecessarilyTrue` | — |
| C90 | — | — | — | — | GroundPerson.personal_ultimate_ground_exists |
| F1a | `Logos.Choice.person_hasChoiceField` | [Choice.lean#L273](formal/Logos/Choice.lean#L273) | `{Means, Subject}` | `Agency.Agent`, `Agency.Rational`, axiom `Subject` (VOCAB), `Choice.ChoiceField`, `Choice.intentional_hasChoiceField`, `Person.Intentional`, `Person.Person` | **C54** `JUDGE_HAS_CHOICE_FIELD`, `Choice.choiceField_exists_from_plurality` |
| F1b | `Logos.Choice.genuineChoice_exists` | [Choice.lean#L183](formal/Logos/Choice.lean#L183) | `{Means, Subject}` | axiom `Subject` (VOCAB), `Choice.Chooses` | `Choice.freeWillExists_of_genuineChoice`, `Choice.genuineChoice_requires_error_possibility`, `Choice.rejectedHornCoMeant_implies_genuineChoice` |
| F2 | — | — | — | — | — |
| F3 | — | — | — | — | — |
| F4 | `Logos.Love.T13_someoneLovable` | [Love.lean#L81](formal/Logos/Love.lean#L81) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Lovable`, `Person.Person`, **C40** `T12_twoPersons` | — |
| F5 | `Logos.Love.T14_eternalRelation` | [Love.lean#L159](formal/Logos/Love.lean#L159) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.AxPersonStability`, `Love.Loves`, `Love.loves_of_helps`, `Person.Person`, `Plurality.NecessarySubject`, **C47** `T12_directedPair`, `Value.Affects` | **C43** `T14_content`, **C45** `T14_square`, **C44** `T14_world` |
| F6 | — | — | — | — | — |
| Q7.2 | `CountermodelPersonNotNecessary.ExistsAt` | [HostileSemantics.lean#L642](formal/Logos/HostileSemantics.lean#L642) | `{}` | — | — |
| C35 | `Logos.Core.negatedAbsolutes` | [Core.lean#L129](formal/Logos/Core.lean#L129) | `{}` | `Core.N_F`, `Core.N_T`, **C6** `notEverythingTrue`, **C2** `notNothingTrue` | — |
| C36 | `Logos.Core.rightWrongDistinction` | [Core.lean#L145](formal/Logos/Core.lean#L145) | `{}` | `Core.N_F`, `Core.N_T`, **C6** `notEverythingTrue`, **C2** `notNothingTrue` | **FAITH-1** `necDistinction`, **C40** `T12_twoPersons`, **C74** `aloneExcluded` |
| C37 | `Logos.Semantics.bothNecessarilyTrueAndFalse` | [Semantics.lean#L102](formal/Logos/Semantics.lean#L102) | `{CL}` | `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, **C13** `lawExcludedMiddle`, **C14** `nonContradiction` | **C59** `strongTruthExists`, `Semantics.strongTruth_and_contingent_content` |
| C59 | `Logos.Semantics.strongTruthExists` | [Semantics.lean#L113](formal/Logos/Semantics.lean#L113) | `{CL}` | `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, **C37** `bothNecessarilyTrueAndFalse` | **C93** `noStrongTruth_selfRefutes` |
| C93 | `Logos.Semantics.noStrongTruth_selfRefutes` | [Semantics.lean#L121](formal/Logos/Semantics.lean#L121) | `{CL}` | `Semantics.Form`, `Semantics.NecessarilyTrue`, **C59** `strongTruthExists` | **C94** `noStrongTruth_assertable_refutes` |
| C94 | `Logos.Choice.noStrongTruth_assertable_refutes` | [Choice.lean#L387](formal/Logos/Choice.lean#L387) | `{Means, Subject, CL}` | `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Semantics.Form`, `Semantics.NecessarilyTrue`, **C93** `noStrongTruth_selfRefutes` | — |
| C95 | `Logos.Semantics.atoms_are_modally_free` | [Semantics.lean#L146](formal/Logos/Semantics.lean#L146) | `{}` | `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, `Semantics.atom_not_necessarily_false`, `Semantics.atom_not_necessarily_true` | **C96** `some_formula_contingent` |
| C96 | `Logos.Semantics.some_formula_contingent` | [Semantics.lean#L160](formal/Logos/Semantics.lean#L160) | `{}` | `Semantics.Form`, `Semantics.NecessarilyFalse`, `Semantics.NecessarilyTrue`, **C95** `atoms_are_modally_free` | `Semantics.strongTruth_and_contingent_content` |
| C38 | `Logos.Necessity.necDistinction` | [Necessity.lean#L116](formal/Logos/Necessity.lean#L116) | `{}` | `Core.N_F`, `Core.N_T`, **C36** `rightWrongDistinction`, `Necessity.Necessity`, `Semantics.World` | `Necessity.necDistinction_content` |
| C39 | `Logos.Choice.T11_choiceField` | [Choice.lean#L243](formal/Logos/Choice.lean#L243) | `{Means, Subject}` | `Agency.A`, axiom `Subject` (VOCAB), `Alternatives.Incompatible`, **C26** `T9_incompatibleAlternatives`, `Core.IsFalse`, `Core.T`, `Person.Person`, **C24** `T5_personExists` | — |
| C40 | `Logos.Plurality.T12_twoPersons` | [Plurality.lean#L44](formal/Logos/Plurality.lean#L44) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), **C36** `rightWrongDistinction`, `Person.Person`, **FAITH-2** `AxTwoSubjects` | `Choice.choiceField_exists_from_plurality`, **C41** `T13_someoneLovable`, **C47** `T12_directedPair`, `Plurality.T1_subjectExists_from_plurality`, `Plurality.T4_agentExists_from_plurality`, `Plurality.T5_personExists_from_plurality`, **C48** `cogito_from_T12`, `Plurality.notAlone` |
| C41 | `Logos.Love.T13_someoneLovable` | [Love.lean#L81](formal/Logos/Love.lean#L81) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Lovable`, `Person.Person`, **C40** `T12_twoPersons` | — |
| C48 | `Logos.Plurality.cogito_from_T12` | [Plurality.lean#L57](formal/Logos/Plurality.lean#L57) | `{AxTwoSubjects, Means, Subject}` | `Agency.A`, `Agency.Agent`, axiom `Means` (VOCAB), `Agency.Rational`, axiom `Subject` (VOCAB), `Person.Intentional`, `Person.Person`, **C40** `T12_twoPersons` | **C30** `correctness_distinct`, `Order.fallible_false`, **C55** `judge_commits` |
| C49 | `Logos.Choice.meaning_needs_subject` | [Choice.lean#L116](formal/Logos/Choice.lean#L116) | `{Means, Subject}` | axiom `Means` (VOCAB), axiom `Subject` (VOCAB) | — |
| C50 | `Logos.Choice.incompatible_self_negation` | [Choice.lean#L92](formal/Logos/Choice.lean#L92) | `{}` | `Alternatives.Incompatible` | `Choice.asserting_noChoiceField_is_choiceField`, `Choice.intentional_hasChoiceField`, `Choice.judge_asserting_rightWrong_has_choiceField`, `Choice.rejectedHornCoMeant_implies_genuineChoice`, **C55** `judge_commits` |
| C51 | `Logos.Choice.person_hasChoiceField` | [Choice.lean#L273](formal/Logos/Choice.lean#L273) | `{Means, Subject}` | `Agency.Agent`, `Agency.Rational`, axiom `Subject` (VOCAB), `Choice.ChoiceField`, `Choice.intentional_hasChoiceField`, `Person.Intentional`, `Person.Person` | **C54** `JUDGE_HAS_CHOICE_FIELD`, `Choice.choiceField_exists_from_plurality` |
| C52 | `Logos.Choice.choiceField_exists` | [Choice.lean#L283](formal/Logos/Choice.lean#L283) | `{Means, Subject}` | `Agency.A`, axiom `Subject` (VOCAB), `Choice.ChoiceField`, `Choice.intentional_hasChoiceField`, `Person.act_implies_intentional` | — |
| C53 | `Logos.Choice.noChoiceField_selfRefutes` | [Choice.lean#L308](formal/Logos/Choice.lean#L308) | `{Means, Subject}` | `Agency.Act`, `Agency.Asserts`, axiom `Subject` (VOCAB), `Choice.NoChoiceField`, `Choice.asserting_noChoiceField_is_choiceField` | — |
| C54 | `Logos.Choice.JUDGE_HAS_CHOICE_FIELD` | [Choice.lean#L324](formal/Logos/Choice.lean#L324) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Choice.ChoiceField`, **C51** `person_hasChoiceField`, `Core.N_F`, `Core.N_T`, `Person.Person`, **FAITH-2** `AxTwoSubjects` | **C61** `rightWrong_implies_someone_means` |
| C55 | `Logos.Order.judge_commits` | [Order.lean#L127](formal/Logos/Order.lean#L127) | `{AxTwoSubjects, Means, Subject, CL}` | `Agency.A`, axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.ChoiceField`, **C50** `incompatible_self_negation`, `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect`, **C48** `cogito_from_T12` | `Order.rightWrongDistinction_implies_meaning` |
| C56 | `Logos.Value.alone_no_other_help_harm` | [Value.lean#L97](formal/Logos/Value.lean#L97) | `{Subject}` | axiom `Subject` (VOCAB), `Value.Alone`, `Value.Harms`, `Value.Helps` | — |
| C57 | `Logos.Choice.noSubject_selfRefutes` | [Choice.lean#L351](formal/Logos/Choice.lean#L351) | `{Means, Subject}` | `Agency.Asserts`, `Agency.NoSubject`, axiom `Subject` (VOCAB), `Agency.noSubject_performative_selfRefutes` | — |
| C42 | `Logos.Love.T14_eternalRelation` | [Love.lean#L159](formal/Logos/Love.lean#L159) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.AxPersonStability`, `Love.Loves`, `Love.loves_of_helps`, `Person.Person`, `Plurality.NecessarySubject`, **C47** `T12_directedPair`, `Value.Affects` | **C43** `T14_content`, **C45** `T14_square`, **C44** `T14_world` |
| C43 | `Logos.Love.T14_content` | [Love.lean#L194](formal/Logos/Love.lean#L194) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, **C42** `T14_eternalRelation`, `Person.Person`, `Plurality.NecessarySubject` | — |
| C44 | `Logos.Love.T14_world` | [Love.lean#L172](formal/Logos/Love.lean#L172) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, **C42** `T14_eternalRelation`, `Necessity.NecessityPH`, `Person.Person`, `Plurality.EntityOf`, `Plurality.NecessarySubject`, `Semantics.World`, `Truthmaker.ExistsAt` | — |
| C45 | `Logos.Love.T14_square` | [Love.lean#L184](formal/Logos/Love.lean#L184) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, **C42** `T14_eternalRelation`, `Necessity.Necessity`, `Person.Person`, `Plurality.NecessarySubject`, `Semantics.World` | — |
| C46 | `Logos.Value.valueInterpersonal_of_split` | [Value.lean#L151](formal/Logos/Value.lean#L151) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Core.N_F`, `Core.N_T`, `Person.Person`, `Value.Affects`, `Value.AxPersonsAffect`, **FAITH-2** `AxTwoSubjects` | — |
| C47 | `Logos.Plurality.T12_directedPair` | [Plurality.lean#L130](formal/Logos/Plurality.lean#L130) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Person.Person`, **C40** `T12_twoPersons`, `Value.Affects` | **C42** `T14_eternalRelation` |
| C61 | `Logos.Choice.rightWrong_implies_someone_means` | [Choice.lean#L344](formal/Logos/Choice.lean#L344) | `{AxTwoSubjects, Means, Subject}` | `Agency.A`, axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Alternatives.Incompatible`, `Choice.ChoiceField`, **C54** `JUDGE_HAS_CHOICE_FIELD`, `Core.N_F`, `Core.N_T` | — |
| C62 | `Logos.Order.rightWrong_implies_meaning` | [Order.lean#L46](formal/Logos/Order.lean#L46) | `{Means, Subject}` | `Agency.A`, axiom `Means` (VOCAB), axiom `Subject` (VOCAB), `Choice.Meaning_I`, `Core.IsFalse`, `Core.T`, `Order.Correct`, `Order.Incorrect` | `Order.rightDistinctWrong_implies_meaning`, `Order.rightWrongDistinction_implies_meaning` |
| C69 | — | — | — | — | — |
| C70 | — | — | — | — | — |
| C71 | — | — | — | — | — |
| C72 | — | — | — | — | — |
| C73 | — | — | — | — | Person.twoPersonsFromSubject |
| C74 | `Logos.Value.aloneExcluded` | [Value.lean#L128](formal/Logos/Value.lean#L128) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), **C36** `rightWrongDistinction`, `Person.Person`, `Value.Alone`, **FAITH-2** `AxTwoSubjects` | — |
| C75 | — | — | — | — | Person.everyContentIsAPerson |
| C76 | — | — | — | — | Love.T14_canonicalRigid |
| C77 | `Logos.Love.necessaryPersonExists` | [Love.lean#L129](formal/Logos/Love.lean#L129) | `{Means, Subject}` | `Agency.Act`, axiom `Subject` (VOCAB), `Love.AxPersonStability`, `Person.Person`, `Plurality.NecessarySubject`, **C24** `T5_personExists` | — |
| C85 | `Logos.Value.help_not_harm` | [Value.lean#L78](formal/Logos/Value.lean#L78) | `{Subject}` | axiom `Subject` (VOCAB), `Value.Harms`, `Value.Helps` | `Love.loves_of_helps` |
| C86 | `Logos.Love.love_helps` | [Love.lean#L47](formal/Logos/Love.lean#L47) | `{Subject}` | axiom `Subject` (VOCAB), `Love.Loves`, `Value.Harms`, `Value.Helps` | — |
| C92 | `Logos.Love.necessary_entity_exists` | [Love.lean#L147](formal/Logos/Love.lean#L147) | `{Means, Subject}` | `Agency.Act`, axiom `Subject` (VOCAB), `Love.AxPersonStability`, `Modal.NecessaryEntity`, **C91** `subject_nec_entity_nec`, `Person.Person`, `Plurality.EntityOf`, **C24** `T5_personExists`, `Truthmaker.Entity` | — |
| C63 | `Logos.Initiation.branches_not_transfer` | [Initiation.lean#L27](formal/Logos/Initiation.lean#L27) | `{}` | `Initiation.Branches`, `Initiation.IsTransfer` | — |
| C64 | — | — | — | — | Initiation.originates_not_transfer |
| C65 | — | — | — | — | Initiation.person_iff_originates |
| C66 | — | — | — | — | Initiation.Cogito_Init |
| C67 | — | — | — | — | Initiation.noInitiation_selfRefutes |
| C80 | — | — | — | — | Initiation.posited_not_branch |
| C81 | — | — | — | — | Initiation.origin_branches |
| C82 | — | — | — | — | Initiation.origin_is_initiating_person |
| FAITH-1 | `Logos.Necessity.necDistinction` | [Necessity.lean#L116](formal/Logos/Necessity.lean#L116) | `{}` | `Core.N_F`, `Core.N_T`, **C36** `rightWrongDistinction`, `Necessity.Necessity`, `Semantics.World` | `Necessity.necDistinction_content` |
| FAITH-2 | `Logos.Value.AxTwoSubjects` | [Value.lean#L119](formal/Logos/Value.lean#L119) | `{AxTwoSubjects, Means, Subject}` | axiom `Subject` (VOCAB), `Core.N_F`, `Core.N_T`, `Person.Person` | **C54** `JUDGE_HAS_CHOICE_FIELD`, **C40** `T12_twoPersons`, **C74** `aloneExcluded`, **C46** `valueInterpersonal_of_split` |
| F7 | `CountermodelNoFreeWill.FreeWill` | [HostileSemantics.lean#L458](formal/Logos/HostileSemantics.lean#L458) | `{}` | — | — |
| F8 | — | — | — | — | — |
| F9 | — | — | — | — | — |

</details>

---
### D.5 Kernel declaration index

<details>
<summary>All user-authored theorems/defs, by module (line and kernel axioms) →</summary>

### `CountermodelActWithoutSubject`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L335](formal/Logos/HostileSemantics.lean#L335) | `def Act : Entity → Prop → Prop` | —  |
| `ConstitutiveAct` | def | [L349](formal/Logos/HostileSemantics.lean#L349) | `def ConstitutiveAct (I : ActOntology) : Prop` | —  |
| `Entity` | def | [L334](formal/Logos/HostileSemantics.lean#L334) | `def Entity : Type` | —  |
| `Person` | def | [L337](formal/Logos/HostileSemantics.lean#L337) | `def Person : Entity → Prop` | —  |
| `Subject` | def | [L336](formal/Logos/HostileSemantics.lean#L336) | `def Subject : Entity → Prop` | —  |
| `act_occurs` | theorem | [L339](formal/Logos/HostileSemantics.lean#L339) | `theorem act_occurs : ∃ s : Entity, ∃ p : Prop, Act s p` | —  |
| `act_without_subject` | theorem | [L344](formal/Logos/HostileSemantics.lean#L344) | `theorem act_without_subject : (∃ s : Entity, ∃ p : Prop, Act s p) ∧ ¬ (∃ s : Ent` | —  |
| `countermodel_violates_constitutive_act` | theorem | [L360](formal/Logos/HostileSemantics.lean#L360) | `theorem countermodel_violates_constitutive_act : ¬ ConstitutiveAct { Entity` | —  |
| `no_person` | theorem | [L341](formal/Logos/HostileSemantics.lean#L341) | `theorem no_person : ¬ ∃ s : Entity, Person s` | —  |
| `no_subject` | theorem | [L340](formal/Logos/HostileSemantics.lean#L340) | `theorem no_subject : ¬ ∃ s : Entity, Subject s` | —  |
| `subject_of_constitutive_act` | theorem | [L353](formal/Logos/HostileSemantics.lean#L353) | `theorem subject_of_constitutive_act (I : ActOntology) (hConst : ConstitutiveAct ` | —  |

### `CountermodelImpersonalUltimateGround`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Entity` | abbrev | [L982](formal/Logos/HostileSemantics.lean#L982) | `abbrev Entity : Type` | —  |
| `GroundEntity` | def | [L984](formal/Logos/HostileSemantics.lean#L984) | `def GroundEntity (_x _y : Entity) : Prop` | —  |
| `Personal` | def | [L986](formal/Logos/HostileSemantics.lean#L986) | `def Personal (_e : Entity) : Prop` | —  |
| `UltimateGround` | def | [L985](formal/Logos/HostileSemantics.lean#L985) | `def UltimateGround (u : Entity) : Prop` | —  |
| `no_personal_ultimate` | theorem | [L993](formal/Logos/HostileSemantics.lean#L993) | `theorem no_personal_ultimate : ¬ ∃ u : Entity, UltimateGround u ∧ Personal u` | —  |
| `ultimate_exists` | theorem | [L988](formal/Logos/HostileSemantics.lean#L988) | `theorem ultimate_exists : ∃ u : Entity, UltimateGround u` | —  |
| `ultimate_not_entails_personal` | theorem | [L998](formal/Logos/HostileSemantics.lean#L998) | `theorem ultimate_not_entails_personal : (∃ u : Entity, UltimateGround u) ∧ ¬ (∃ ` | —  |

### `CountermodelInfiniteGroundChain`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Entity` | abbrev | [L947](formal/Logos/HostileSemantics.lean#L947) | `abbrev Entity : Type` | —  |
| `GroundEntity` | def | [L950](formal/Logos/HostileSemantics.lean#L950) | `def GroundEntity (x y : Entity) : Prop` | —  |
| `UltimateGround` | def | [L952](formal/Logos/HostileSemantics.lean#L952) | `def UltimateGround (u : Entity) : Prop` | —  |
| `asymmetric` | theorem | [L957](formal/Logos/HostileSemantics.lean#L957) | `theorem asymmetric (x y : Entity) : GroundEntity x y → ¬ GroundEntity y x` | —  |
| `infinite_chain_has_no_ultimate` | theorem | [L967](formal/Logos/HostileSemantics.lean#L967) | `theorem infinite_chain_has_no_ultimate : (∀ x, ¬ GroundEntity x x) ∧ (∀ x y, Gro` | —  |
| `irreflexive` | theorem | [L954](formal/Logos/HostileSemantics.lean#L954) | `theorem irreflexive (x : Entity) : ¬ GroundEntity x x` | —  |
| `no_ultimate` | theorem | [L963](formal/Logos/HostileSemantics.lean#L963) | `theorem no_ultimate : ¬ ∃ u : Entity, UltimateGround u` | —  |
| `transitive` | theorem | [L960](formal/Logos/HostileSemantics.lean#L960) | `theorem transitive (x y z : Entity) : GroundEntity x y → GroundEntity y z → Grou` | —  |

### `CountermodelNoFreeWill`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A` | def | [L456](formal/Logos/HostileSemantics.lean#L456) | `def A : S → Prop → Prop` | —  |
| `Chooses` | def | [L457](formal/Logos/HostileSemantics.lean#L457) | `def Chooses : S → Prop → Prop → Prop` | —  |
| `FreeWill` | def | [L458](formal/Logos/HostileSemantics.lean#L458) | `def FreeWill : S → Prop` | — → F7 |
| `S` | def | [L455](formal/Logos/HostileSemantics.lean#L455) | `def S : Type` | —  |
| `act_does_not_imply_choice` | theorem | [L463](formal/Logos/HostileSemantics.lean#L463) | `theorem act_does_not_imply_choice : (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S, ∃` | —  |
| `act_does_not_imply_freewill` | theorem | [L466](formal/Logos/HostileSemantics.lean#L466) | `theorem act_does_not_imply_freewill : (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S,` | —  |
| `act_occurs` | theorem | [L460](formal/Logos/HostileSemantics.lean#L460) | `theorem act_occurs : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `no_choice` | theorem | [L461](formal/Logos/HostileSemantics.lean#L461) | `theorem no_choice : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q` | —  |
| `no_free_will` | theorem | [L462](formal/Logos/HostileSemantics.lean#L462) | `theorem no_free_will : ¬ ∃ s : S, FreeWill s` | —  |

### `CountermodelNoPerson`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A` | def | [L437](formal/Logos/HostileSemantics.lean#L437) | `def A : S → Prop → Prop` | —  |
| `Person` | def | [L438](formal/Logos/HostileSemantics.lean#L438) | `def Person : S → Prop` | —  |
| `S` | def | [L436](formal/Logos/HostileSemantics.lean#L436) | `def S : Type` | —  |
| `act_does_not_imply_person` | theorem | [L442](formal/Logos/HostileSemantics.lean#L442) | `theorem act_does_not_imply_person : (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ s : S, P` | —  |
| `act_occurs` | theorem | [L440](formal/Logos/HostileSemantics.lean#L440) | `theorem act_occurs : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `no_person` | theorem | [L441](formal/Logos/HostileSemantics.lean#L441) | `theorem no_person : ¬ ∃ s : S, Person s` | —  |

### `CountermodelPersonNotNecessary`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ExistsAt` | def | [L642](formal/Logos/HostileSemantics.lean#L642) | `def ExistsAt (w : World) (_s : Subject) : Prop` | — → Q7.2 |
| `NecessarySubject` | def | [L646](formal/Logos/HostileSemantics.lean#L646) | `def NecessarySubject (s : Subject) : Prop` | —  |
| `NecessitySignature` | structure | [L662](formal/Logos/HostileSemantics.lean#L662) | `structure NecessitySignature where` | —  |
| `Person` | def | [L644](formal/Logos/HostileSemantics.lean#L644) | `def Person (_s : Subject) : Prop` | —  |
| `Subject` | abbrev | [L638](formal/Logos/HostileSemantics.lean#L638) | `abbrev Subject : Type` | —  |
| `World` | abbrev | [L639](formal/Logos/HostileSemantics.lean#L639) | `abbrev World : Type` | —  |
| `no_necessary_subject` | theorem | [L650](formal/Logos/HostileSemantics.lean#L650) | `theorem no_necessary_subject : ¬ ∃ s : Subject, NecessarySubject s` | —  |
| `not_entails_person_necessary` | theorem | [L670](formal/Logos/HostileSemantics.lean#L670) | `theorem not_entails_person_necessary : ¬ (∀ I : NecessitySignature, (∃ s : I.Sub` | —  |
| `person_exists` | theorem | [L648](formal/Logos/HostileSemantics.lean#L648) | `theorem person_exists : ∃ s : Subject, Person s` | —  |
| `person_not_entails_necessary` | theorem | [L656](formal/Logos/HostileSemantics.lean#L656) | `theorem person_not_entails_necessary : (∃ s : Subject, Person s) ∧ ¬ (∃ s : Subj` | —  |

### `CountermodelPluralityWithoutLove`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Loves` | def | [L1013](formal/Logos/HostileSemantics.lean#L1013) | `def Loves (_s _t : Subject) : Prop` | —  |
| `Person` | def | [L1012](formal/Logos/HostileSemantics.lean#L1012) | `def Person (_s : Subject) : Prop` | —  |
| `Subject` | abbrev | [L1011](formal/Logos/HostileSemantics.lean#L1011) | `abbrev Subject : Type` | —  |
| `no_love` | theorem | [L1019](formal/Logos/HostileSemantics.lean#L1019) | `theorem no_love : ¬ ∃ s₁ s₂ : Subject, Loves s₁ s₂` | —  |
| `plurality_not_entails_love` | theorem | [L1024](formal/Logos/HostileSemantics.lean#L1024) | `theorem plurality_not_entails_love : (∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧` | —  |
| `two_persons_exist` | theorem | [L1015](formal/Logos/HostileSemantics.lean#L1015) | `theorem two_persons_exist : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | —  |

### `CountermodelSubjectNecessityNotEntityNecessity`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Entity` | abbrev | [L557](formal/Logos/HostileSemantics.lean#L557) | `abbrev Entity : Type` | —  |
| `EntityExistsAt` | def | [L569](formal/Logos/HostileSemantics.lean#L569) | `def EntityExistsAt (w : World) (_e : Entity) : Prop` | —  |
| `EntityOf` | def | [L561](formal/Logos/HostileSemantics.lean#L561) | `def EntityOf (_s : Subject) : Entity` | —  |
| `NecessaryEntity` | def | [L575](formal/Logos/HostileSemantics.lean#L575) | `def NecessaryEntity (e : Entity) : Prop` | —  |
| `NecessarySubject` | def | [L572](formal/Logos/HostileSemantics.lean#L572) | `def NecessarySubject (s : Subject) : Prop` | —  |
| `NecessityLift` | structure | [L596](formal/Logos/HostileSemantics.lean#L596) | `structure NecessityLift where` | —  |
| `Subject` | abbrev | [L556](formal/Logos/HostileSemantics.lean#L556) | `abbrev Subject : Type` | —  |
| `SubjectExistsAt` | def | [L565](formal/Logos/HostileSemantics.lean#L565) | `def SubjectExistsAt (_w : World) (_s : Subject) : Prop` | —  |
| `World` | abbrev | [L555](formal/Logos/HostileSemantics.lean#L555) | `abbrev World : Type` | —  |
| `necessary_subject_is_necessary` | theorem | [L578](formal/Logos/HostileSemantics.lean#L578) | `theorem necessary_subject_is_necessary : NecessarySubject ()` | —  |
| `no_necessary_entity` | theorem | [L583](formal/Logos/HostileSemantics.lean#L583) | `theorem no_necessary_entity : ¬ ∃ e : Entity, NecessaryEntity e` | —  |
| `not_holds_of_arbitrary_signature` | theorem | [L605](formal/Logos/HostileSemantics.lean#L605) | `theorem not_holds_of_arbitrary_signature : ¬ (∀ (I : NecessityLift), ∀ s : I.Sub` | —  |
| `subject_necessity_not_entails_entity_necessity` | theorem | [L590](formal/Logos/HostileSemantics.lean#L590) | `theorem subject_necessity_not_entails_entity_necessity : (∃ s : Subject, Necessa` | —  |

### `CountermodelSubjectWithoutPerson`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L411](formal/Logos/HostileSemantics.lean#L411) | `def Act : Entity → Prop → Prop` | —  |
| `Entity` | def | [L410](formal/Logos/HostileSemantics.lean#L410) | `def Entity : Type` | —  |
| `Person` | def | [L413](formal/Logos/HostileSemantics.lean#L413) | `def Person : Entity → Prop` | —  |
| `Subject` | def | [L412](formal/Logos/HostileSemantics.lean#L412) | `def Subject : Entity → Prop` | —  |
| `act_and_subject_without_person` | theorem | [L429](formal/Logos/HostileSemantics.lean#L429) | `theorem act_and_subject_without_person : (∃ s : Entity, ∃ p : Prop, Act s p) ∧ (` | —  |
| `act_occurs` | theorem | [L419](formal/Logos/HostileSemantics.lean#L419) | `theorem act_occurs : ∃ s : Entity, ∃ p : Prop, Act s p` | —  |
| `constitutive_act_holds` | theorem | [L416](formal/Logos/HostileSemantics.lean#L416) | `theorem constitutive_act_holds : ∀ (s : Entity) (p : Prop), Act s p → Subject s` | —  |
| `no_person` | theorem | [L421](formal/Logos/HostileSemantics.lean#L421) | `theorem no_person : ¬ ∃ s : Entity, Person s` | —  |
| `subject_exists` | theorem | [L420](formal/Logos/HostileSemantics.lean#L420) | `theorem subject_exists : ∃ s : Entity, Subject s` | —  |
| `subject_without_person` | theorem | [L424](formal/Logos/HostileSemantics.lean#L424) | `theorem subject_without_person : (∃ s : Entity, Subject s) ∧ ¬ (∃ s : Entity, Pe` | —  |

### `CountermodelVeridicalMeaning`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `BoundaryDatum` | def | [L882](formal/Logos/HostileSemantics.lean#L882) | `def BoundaryDatum (I : BoundarySignature) : Prop` | —  |
| `BoundaryGenuineChoice` | def | [L887](formal/Logos/HostileSemantics.lean#L887) | `def BoundaryGenuineChoice (I : BoundarySignature) : Prop` | —  |
| `BoundarySignature` | structure | [L869](formal/Logos/HostileSemantics.lean#L869) | `structure BoundarySignature where` | —  |
| `BoundaryTwoSubjects` | def | [L892](formal/Logos/HostileSemantics.lean#L892) | `def BoundaryTwoSubjects (I : BoundarySignature) : Prop` | —  |
| `GCdatum` | def | [L820](formal/Logos/HostileSemantics.lean#L820) | `def GCdatum (I : GenuineChoiceSignature) : Prop` | —  |
| `GenuineChoice` | def | [L825](formal/Logos/HostileSemantics.lean#L825) | `def GenuineChoice (I : GenuineChoiceSignature) : Prop` | —  |
| `GenuineChoiceSignature` | structure | [L816](formal/Logos/HostileSemantics.lean#L816) | `structure GenuineChoiceSignature where` | —  |
| `ModalOpen` | def | [L878](formal/Logos/HostileSemantics.lean#L878) | `def ModalOpen (I : BoundarySignature) : Prop` | —  |
| `modal_openness_and_plurality_do_not_entail_genuine_choice` | theorem | [L918](formal/Logos/HostileSemantics.lean#L918) | `theorem modal_openness_and_plurality_do_not_entail_genuine_choice : ¬ (∀ I : Bou` | —  |
| `modal_openness_does_not_entail_genuine_choice` | theorem | [L899](formal/Logos/HostileSemantics.lean#L899) | `theorem modal_openness_does_not_entail_genuine_choice : ¬ (∀ I : BoundarySignatu` | —  |
| `not_entails_genuine_choice` | theorem | [L834](formal/Logos/HostileSemantics.lean#L834) | `theorem not_entails_genuine_choice : ¬ (∀ I : GenuineChoiceSignature, GCdatum I ` | —  |
| `not_entails_genuine_choice_with_plurality` | theorem | [L846](formal/Logos/HostileSemantics.lean#L846) | `theorem not_entails_genuine_choice_with_plurality : ¬ (∀ I : GenuineChoiceSignat` | —  |
| `Γ_twoGCSubjects` | def | [L829](formal/Logos/HostileSemantics.lean#L829) | `def Γ_twoGCSubjects (I : GenuineChoiceSignature) : Prop` | —  |

### `CountermodelVeridicalMeaning.Single`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A` | def | [L708](formal/Logos/HostileSemantics.lean#L708) | `def A (s : S) (p : Prop) : Prop` | —  |
| `Chooses` | def | [L710](formal/Logos/HostileSemantics.lean#L710) | `def Chooses (s : S) (p q : Prop) : Prop` | —  |
| `FreeWill` | def | [L711](formal/Logos/HostileSemantics.lean#L711) | `def FreeWill (s : S) : Prop` | —  |
| `M` | def | [L707](formal/Logos/HostileSemantics.lean#L707) | `def M (_s : S) (p : Prop) : Prop` | —  |
| `Person` | def | [L709](formal/Logos/HostileSemantics.lean#L709) | `def Person (s : S) : Prop` | —  |
| `S` | def | [L706](formal/Logos/HostileSemantics.lean#L706) | `def S : Type` | —  |
| `act_datum_holds` | theorem | [L713](formal/Logos/HostileSemantics.lean#L713) | `theorem act_datum_holds : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `act_does_not_imply_genuine_choice` | theorem | [L729](formal/Logos/HostileSemantics.lean#L729) | `theorem act_does_not_imply_genuine_choice : (∃ s : S, ∃ p : Prop, A s p) ∧ ¬ (∃ ` | —  |
| `field_holds` | theorem | [L716](formal/Logos/HostileSemantics.lean#L716) | `theorem field_holds : ∃ s : S, ∃ p q : Prop, A s p ∧ Logos.Alternatives.Incompat` | —  |
| `no_genuine_choice` | theorem | [L719](formal/Logos/HostileSemantics.lean#L719) | `theorem no_genuine_choice : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q` | —  |
| `no_rejected_horn` | theorem | [L723](formal/Logos/HostileSemantics.lean#L723) | `theorem no_rejected_horn : ¬ ∃ s : S, ∃ p : Prop, A s p ∧ A s (¬ p)` | —  |

### `CountermodelVeridicalMeaning.TwoPersons`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A` | def | [L742](formal/Logos/HostileSemantics.lean#L742) | `def A (s : S) (p : Prop) : Prop` | —  |
| `Chooses` | def | [L744](formal/Logos/HostileSemantics.lean#L744) | `def Chooses (s : S) (p q : Prop) : Prop` | —  |
| `Correct` | def | [L750](formal/Logos/HostileSemantics.lean#L750) | `def Correct (s : S) (p : Prop) : Prop` | —  |
| `Fallible` | def | [L752](formal/Logos/HostileSemantics.lean#L752) | `def Fallible (_s : S) (p : Prop) : Prop` | —  |
| `FreeWill` | def | [L745](formal/Logos/HostileSemantics.lean#L745) | `def FreeWill (s : S) : Prop` | —  |
| `Incorrect` | def | [L751](formal/Logos/HostileSemantics.lean#L751) | `def Incorrect (s : S) (p : Prop) : Prop` | —  |
| `IsFalse` | def | [L749](formal/Logos/HostileSemantics.lean#L749) | `def IsFalse (p : Prop) : Prop` | —  |
| `M` | def | [L741](formal/Logos/HostileSemantics.lean#L741) | `def M (_s : S) (p : Prop) : Prop` | —  |
| `Person` | def | [L743](formal/Logos/HostileSemantics.lean#L743) | `def Person (s : S) : Prop` | —  |
| `S` | def | [L740](formal/Logos/HostileSemantics.lean#L740) | `def S : Type` | —  |
| `T` | def | [L748](formal/Logos/HostileSemantics.lean#L748) | `def T (p : Prop) : Prop` | —  |
| `act_datum_holds` | theorem | [L754](formal/Logos/HostileSemantics.lean#L754) | `theorem act_datum_holds : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `fallibility_holds` | theorem | [L780](formal/Logos/HostileSemantics.lean#L780) | `theorem fallibility_holds : ∃ (s : S) (p : Prop), Fallible s p ∧ IsFalse p` | —  |
| `full_fragment_without_genuine_choice` | theorem | [L800](formal/Logos/HostileSemantics.lean#L800) | `theorem full_fragment_without_genuine_choice : (∃ s : S, ∃ p : Prop, A s p) ∧ (∃` | —  |
| `judge_commits_holds` | theorem | [L771](formal/Logos/HostileSemantics.lean#L771) | `theorem judge_commits_holds : ∃ (s : S) (p q : Prop), A s p ∧ (Correct s p ∨ Inc` | —  |
| `no_genuine_choice` | theorem | [L787](formal/Logos/HostileSemantics.lean#L787) | `theorem no_genuine_choice : ¬ ∃ s : S, ∃ p q : Prop, Chooses s p q` | —  |
| `no_rejected_horn` | theorem | [L791](formal/Logos/HostileSemantics.lean#L791) | `theorem no_rejected_horn : ¬ ∃ s : S, ∃ p : Prop, A s p ∧ A s (¬ p)` | —  |
| `rightWrong_holds` | theorem | [L764](formal/Logos/HostileSemantics.lean#L764) | `theorem rightWrong_holds : (¬ (∀ p : Prop, ¬ T p)) ∧ (¬ (∀ p : Prop, T p))` | —  |
| `two_persons_exist` | theorem | [L757](formal/Logos/HostileSemantics.lean#L757) | `theorem two_persons_exist : ∃ s₁ s₂ : S, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | —  |

### `CountermodelWeakActWithoutMeaning`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Act` | def | [L382](formal/Logos/HostileSemantics.lean#L382) | `def Act (s : Entity) (p : Prop) : Prop` | —  |
| `Entity` | def | [L379](formal/Logos/HostileSemantics.lean#L379) | `def Entity : Type` | —  |
| `Means` | def | [L381](formal/Logos/HostileSemantics.lean#L381) | `def Means : Entity → Prop → Prop` | —  |
| `act` | def | [L380](formal/Logos/HostileSemantics.lean#L380) | `def act : Entity → Prop → Prop` | —  |
| `no_strong_act` | theorem | [L385](formal/Logos/HostileSemantics.lean#L385) | `theorem no_strong_act : ¬ ∃ s : Entity, ∃ p : Prop, Act s p` | —  |
| `not_entails_strong_act` | theorem | [L394](formal/Logos/HostileSemantics.lean#L394) | `theorem not_entails_strong_act : ¬ (∀ (I_act : Entity → Prop → Prop) (I_Means : ` | —  |
| `weak_act_occurs` | theorem | [L384](formal/Logos/HostileSemantics.lean#L384) | `theorem weak_act_occurs : ∃ s : Entity, ∃ p : Prop, act s p` | —  |
| `weak_act_without_meaning` | theorem | [L388](formal/Logos/HostileSemantics.lean#L388) | `theorem weak_act_without_meaning : (∃ s : Entity, ∃ p : Prop, act s p) ∧ ¬ (∃ s ` | —  |

### `CountermodelWorldwiseTruthmaking`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Entity` | abbrev | [L517](formal/Logos/HostileSemantics.lean#L517) | `abbrev Entity : Type` | —  |
| `ExistsAt` | def | [L519](formal/Logos/HostileSemantics.lean#L519) | `def ExistsAt (w : World) (e : Entity) : Prop` | —  |
| `Ground` | def | [L520](formal/Logos/HostileSemantics.lean#L520) | `def Ground (_e : Entity) (_φ : Unit) : Prop` | —  |
| `World` | abbrev | [L516](formal/Logos/HostileSemantics.lean#L516) | `abbrev World : Type` | —  |
| `no_uniform_ground` | theorem | [L526](formal/Logos/HostileSemantics.lean#L526) | `theorem no_uniform_ground : ¬ ∃ e : Entity, ∀ w : World, ExistsAt w e ∧ Ground e` | —  |
| `worldwise_not_entails_uniform_ground` | theorem | [L534](formal/Logos/HostileSemantics.lean#L534) | `theorem worldwise_not_entails_uniform_ground : (∀ w : World, ∃ e : Entity, Exist` | —  |
| `worldwise_truthmaking` | theorem | [L522](formal/Logos/HostileSemantics.lean#L522) | `theorem worldwise_truthmaking : ∀ w : World, ∃ e : Entity, ExistsAt w e ∧ Ground` | —  |

### `Logos.Agency`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A` | abbrev | [L81](formal/Logos/Agency.lean#L81) | `abbrev A` | {Means, Subject}  |
| `Act` | def | [L78](formal/Logos/Agency.lean#L78) | `def Act (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `Agent` | def | [L53](formal/Logos/Agency.lean#L53) | `def Agent (_s : Subject) : Prop` | {Subject}  |
| `AnActualSubjectExists` | def | [L99](formal/Logos/Agency.lean#L99) | `def AnActualSubjectExists : Prop` | {Means, Subject}  |
| `Asserts` | def | [L193](formal/Logos/Agency.lean#L193) | `def Asserts (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `Cogito` | theorem | [L222](formal/Logos/Agency.lean#L222) | `theorem Cogito {s : Subject} {p : Prop} (h : Asserts s p) : ∃ s' : Subject, ∃ p'` | {Means, Subject} → C68 |
| `Cogito_of_bridge` | theorem | [L172](formal/Logos/Agency.lean#L172) | `theorem Cogito_of_bridge (hBridge : weak_act_implies_strong_act) {s : Subject} {` | {Means, Subject, act}  |
| `Content` | def | [L47](formal/Logos/Agency.lean#L47) | `def Content (_p : Prop) : Prop` | {}  |
| `Exists` | abbrev | [L96](formal/Logos/Agency.lean#L96) | `abbrev Exists : Subject → Prop` | {Means, Subject}  |
| `Means` | axiom | [L73](formal/Logos/Agency.lean#L73) | `axiom Means : Subject → Prop → Prop` | {Means, Subject}  |
| `NoAct` | def | [L179](formal/Logos/Agency.lean#L179) | `def NoAct : Prop` | {Means, Subject}  |
| `NoSubject` | def | [L232](formal/Logos/Agency.lean#L232) | `def NoSubject : Prop` | {Means, Subject}  |
| `NoSubjectSort` | def | [L247](formal/Logos/Agency.lean#L247) | `def NoSubjectSort : Prop` | {Subject}  |
| `NoWeakAct` | def | [L126](formal/Logos/Agency.lean#L126) | `def NoWeakAct : Prop` | {Subject, act}  |
| `Rational` | def | [L59](formal/Logos/Agency.lean#L59) | `def Rational (_s : Subject) : Prop` | {Subject}  |
| `Subject` | axiom | [L42](formal/Logos/Agency.lean#L42) | `axiom Subject : Type` | {Subject}  |
| `SubjectExists` | def | [L93](formal/Logos/Agency.lean#L93) | `def SubjectExists (s : Subject) : Prop` | {Means, Subject}  |
| `T1_subjectExists_of_act` | theorem | [L227](formal/Logos/Agency.lean#L227) | `theorem T1_subjectExists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s :` | {Means, Subject}  |
| `T2_contentExists` | theorem | [L281](formal/Logos/Agency.lean#L281) | `theorem T2_contentExists : ∃ p : Prop, Content p` | {} → C22 |
| `act` | axiom | [L66](formal/Logos/Agency.lean#L66) | `axiom act : Subject → Prop → Prop` | {Subject, act}  |
| `act_exists_of_assert` | theorem | [L202](formal/Logos/Agency.lean#L202) | `theorem act_exists_of_assert {s : Subject} {p : Prop} (h : Asserts s p) : ∃ s' :` | {Means, Subject}  |
| `act_implies_agent` | theorem | [L260](formal/Logos/Agency.lean#L260) | `theorem act_implies_agent : ∀ {s : Subject} {p : Prop}, A s p → Agent s` | {Means, Subject}  |
| `act_implies_content` | theorem | [L255](formal/Logos/Agency.lean#L255) | `theorem act_implies_content : ∀ {s : Subject} {p : Prop}, A s p → Content p` | {Means, Subject}  |
| `act_implies_exists` | abbrev | [L108](formal/Logos/Agency.lean#L108) | `abbrev act_implies_exists` | {Means, Subject}  |
| `act_implies_means` | theorem | [L272](formal/Logos/Agency.lean#L272) | `theorem act_implies_means : ∀ {s : Subject} {p : Prop}, A s p → Means s p` | {Means, Subject}  |
| `act_implies_rational` | theorem | [L266](formal/Logos/Agency.lean#L266) | `theorem act_implies_rational : ∀ {s : Subject} {p : Prop}, A s p → Rational s` | {Means, Subject}  |
| `act_of_asserting_no_act` | theorem | [L207](formal/Logos/Agency.lean#L207) | `theorem act_of_asserting_no_act (speaker : Subject) (h : Asserts speaker NoAct) ` | {Means, Subject}  |
| `act_requires_subject` | theorem | [L104](formal/Logos/Agency.lean#L104) | `theorem act_requires_subject (s : Subject) (p : Prop) (h : Act s p) : SubjectExi` | {Means, Subject}  |
| `an_actual_subject_exists_of_act` | theorem | [L117](formal/Logos/Agency.lean#L117) | `theorem an_actual_subject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p)` | {Means, Subject}  |
| `assertion_is_act` | theorem | [L198](formal/Logos/Agency.lean#L198) | `theorem assertion_is_act {s : Subject} {p : Prop} (h : Asserts s p) : Act s p` | {Means, Subject}  |
| `assertion_is_weak_act` | theorem | [L133](formal/Logos/Agency.lean#L133) | `theorem assertion_is_weak_act {s : Subject} {p : Prop} (h : asserts s p) : act s` | {Subject, act}  |
| `asserts` | def | [L130](formal/Logos/Agency.lean#L130) | `def asserts (s : Subject) (p : Prop) : Prop` | {Subject, act}  |
| `noAct_conditional_selfRefutes` | theorem | [L182](formal/Logos/Agency.lean#L182) | `theorem noAct_conditional_selfRefutes (hBridge : weak_act_implies_strong_act) (s` | {Means, Subject, act}  |
| `noCogito_selfRefutes` | theorem | [L218](formal/Logos/Agency.lean#L218) | `theorem noCogito_selfRefutes (speaker : Subject) (h : Asserts speaker NoAct) : F` | {Means, Subject}  |
| `noSubjectSort_selfRefutes` | theorem | [L250](formal/Logos/Agency.lean#L250) | `theorem noSubjectSort_selfRefutes (speaker : Subject) (h : Asserts speaker NoSub` | {Means, Subject}  |
| `noSubject_performative_selfRefutes` | theorem | [L237](formal/Logos/Agency.lean#L237) | `theorem noSubject_performative_selfRefutes (speaker : Subject) (h : Asserts spea` | {Means, Subject}  |
| `noSubject_selfRefutes` | theorem | [L243](formal/Logos/Agency.lean#L243) | `theorem noSubject_selfRefutes (speaker : Subject) (h : Asserts speaker NoSubject` | {Means, Subject}  |
| `noWeakAct_selfRefutes` | theorem | [L143](formal/Logos/Agency.lean#L143) | `theorem noWeakAct_selfRefutes (speaker : Subject) (h : asserts speaker NoWeakAct` | {Subject, act} → C58 |
| `strong_act_of_weak_act` | theorem | [L167](formal/Logos/Agency.lean#L167) | `theorem strong_act_of_weak_act (hBridge : weak_act_implies_strong_act) {s : Subj` | {Means, Subject, act}  |
| `subject_exists_of_act` | theorem | [L111](formal/Logos/Agency.lean#L111) | `theorem subject_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Act s p) : ∃ s : S` | {Means, Subject}  |
| `subject_exists_of_assert` | theorem | [L212](formal/Logos/Agency.lean#L212) | `theorem subject_exists_of_assert {s : Subject} {p : Prop} (h : Asserts s p) : ∃ ` | {Means, Subject}  |
| `weak_Cogito` | theorem | [L147](formal/Logos/Agency.lean#L147) | `theorem weak_Cogito {s : Subject} {p : Prop} (h : asserts s p) : ∃ s' : Subject,` | {Subject, act}  |
| `weak_act_exists_implies_strong_act_exists` | def | [L163](formal/Logos/Agency.lean#L163) | `def weak_act_exists_implies_strong_act_exists : Prop` | {Means, Subject, act}  |
| `weak_act_exists_of_assert` | theorem | [L137](formal/Logos/Agency.lean#L137) | `theorem weak_act_exists_of_assert {s : Subject} {p : Prop} (h : asserts s p) : ∃` | {Subject, act}  |
| `weak_act_implies_strong_act` | def | [L159](formal/Logos/Agency.lean#L159) | `def weak_act_implies_strong_act : Prop` | {Means, Subject, act}  |

### `Logos.Alternatives`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Incompatible` | def | [L17](formal/Logos/Alternatives.lean#L17) | `def Incompatible (p q : Prop) : Prop` | {}  |
| `T9_incompatibleAlternatives` | theorem | [L24](formal/Logos/Alternatives.lean#L24) | `theorem T9_incompatibleAlternatives : ∃ p q : Prop, Incompatible p q ∧ T p ∧ IsF` | {} → C26 |
| `incompatible_with_negation` | theorem | [L35](formal/Logos/Alternatives.lean#L35) | `theorem incompatible_with_negation {p : Prop} (hp : T p) : Incompatible p (¬ p) ` | {} → C27 |

### `Logos.Choice`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `CanChoose` | def | [L122](formal/Logos/Choice.lean#L122) | `def CanChoose (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `ChoiceField` | def | [L77](formal/Logos/Choice.lean#L77) | `def ChoiceField (s : Subject) (p : Prop) (q : Prop) : Prop` | {Means, Subject}  |
| `Chooses` | def | [L84](formal/Logos/Choice.lean#L84) | `def Chooses (s : Subject) (p : Prop) (q : Prop) : Prop` | {Means, Subject}  |
| `FreeWill` | def | [L145](formal/Logos/Choice.lean#L145) | `def FreeWill (s : Subject) : Prop` | {Means, Subject}  |
| `JUDGE_HAS_CHOICE_FIELD` | theorem | [L324](formal/Logos/Choice.lean#L324) | `theorem JUDGE_HAS_CHOICE_FIELD (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) : ∃ s :` | {AxTwoSubjects, Means, Subject} → C54 |
| `Meaning_I` | def | [L99](formal/Logos/Choice.lean#L99) | `def Meaning_I (p : Prop) : Prop` | {Means, Subject}  |
| `NoChoiceField` | def | [L297](formal/Logos/Choice.lean#L297) | `def NoChoiceField : Prop` | {Means, Subject}  |
| `T11_choiceField` | theorem | [L243](formal/Logos/Choice.lean#L243) | `theorem T11_choiceField (h : ∃ s : Subject, ∃ p : Prop, A s p) : ∃ s : Subject, ` | {Means, Subject} → C39 |
| `T11_choiceField_from_plurality` | theorem | [L250](formal/Logos/Choice.lean#L250) | `theorem T11_choiceField_from_plurality : ∃ s : Subject, Person s ∧ ∃ p q : Prop,` | {AxTwoSubjects, Means, Subject}  |
| `asserting_noChoiceField_is_choiceField` | theorem | [L301](formal/Logos/Choice.lean#L301) | `theorem asserting_noChoiceField_is_choiceField (speaker : Subject) (h : Logos.Ag` | {Means, Subject}  |
| `assertion_consistency` | theorem | [L367](formal/Logos/Choice.lean#L367) | `theorem assertion_consistency {s : Subject} {p : Prop} (h : Asserts s p) : ¬ Ass` | {Means, Subject}  |
| `canChoose_unfold` | theorem | [L127](formal/Logos/Choice.lean#L127) | `theorem canChoose_unfold {s : Subject} {p : Prop} : CanChoose s p ↔ ∃ q : Prop, ` | {Means, Subject, CL}  |
| `choiceField_exists` | theorem | [L283](formal/Logos/Choice.lean#L283) | `theorem choiceField_exists (h : ∃ s : Subject, ∃ p : Prop, A s p) : ∃ s : Subjec` | {Means, Subject} → C52 |
| `choiceField_exists_from_plurality` | theorem | [L291](formal/Logos/Choice.lean#L291) | `theorem choiceField_exists_from_plurality : ∃ s : Subject, ∃ p q : Prop, ChoiceF` | {AxTwoSubjects, Means, Subject}  |
| `chooses_implies_freeWill` | theorem | [L153](formal/Logos/Choice.lean#L153) | `theorem chooses_implies_freeWill {s : Subject} {p q : Prop} (h : Chooses s p q) ` | {Means, Subject}  |
| `freeWillExists_of_chooses` | theorem | [L160](formal/Logos/Choice.lean#L160) | `theorem freeWillExists_of_chooses (h : ∃ s : Subject, ∃ p q : Prop, Chooses s p ` | {Means, Subject}  |
| `freeWillExists_of_genuineChoice` | theorem | [L208](formal/Logos/Choice.lean#L208) | `theorem freeWillExists_of_genuineChoice : genuineChoice_exists → ∃ s : Subject, ` | {Means, Subject}  |
| `genuineChoice_exists` | def | [L183](formal/Logos/Choice.lean#L183) | `def genuineChoice_exists : Prop` | {Means, Subject} → F1b |
| `genuineChoice_requires_error_possibility` | theorem | [L232](formal/Logos/Choice.lean#L232) | `theorem genuineChoice_requires_error_possibility : genuineChoice_exists → ¬ (∀ s` | {Means, Subject}  |
| `incompatible_self_negation` | theorem | [L92](formal/Logos/Choice.lean#L92) | `theorem incompatible_self_negation (p : Prop) : Incompatible p (¬ p)` | {} → C50 |
| `intentional_hasChoiceField` | theorem | [L260](formal/Logos/Choice.lean#L260) | `theorem intentional_hasChoiceField {s : Subject} (hIn : Logos.Person.Intentional` | {Means, Subject}  |
| `judge_asserting_rightWrong_has_choiceField` | theorem | [L332](formal/Logos/Choice.lean#L332) | `theorem judge_asserting_rightWrong_has_choiceField (speaker : Subject) (h : Logo` | {Means, Subject}  |
| `meaning_I_needs_subject` | theorem | [L107](formal/Logos/Choice.lean#L107) | `theorem meaning_I_needs_subject {p : Prop} (h : Meaning_I p) : ∃ s : Subject, Me` | {Means, Subject}  |
| `meaning_needs_subject` | theorem | [L116](formal/Logos/Choice.lean#L116) | `theorem meaning_needs_subject {s : Subject} {p : Prop} (hm : Means s p) : ∃ t : ` | {Means, Subject} → C49 |
| `noChoiceField_contradicts_field` | theorem | [L313](formal/Logos/Choice.lean#L313) | `theorem noChoiceField_contradicts_field (hField : ∃ s : Subject, ∃ p q : Prop, C` | {Means, Subject}  |
| `noChoiceField_selfRefutes` | theorem | [L308](formal/Logos/Choice.lean#L308) | `theorem noChoiceField_selfRefutes (speaker : Subject) (h : Logos.Agency.Asserts ` | {Means, Subject} → C53 |
| `noStrongTruth_assertable_refutes` | theorem | [L387](formal/Logos/Choice.lean#L387) | `theorem noStrongTruth_assertable_refutes (speaker : Subject) : Asserts speaker (` | {Means, Subject, CL} → C94 |
| `noSubject_contradicts_subject` | theorem | [L356](formal/Logos/Choice.lean#L356) | `theorem noSubject_contradicts_subject (hSubj : ∃ s : Subject, Logos.Agency.Subje` | {Means, Subject}  |
| `noSubject_selfRefutes` | theorem | [L351](formal/Logos/Choice.lean#L351) | `theorem noSubject_selfRefutes (speaker : Subject) (h : Logos.Agency.Asserts spea` | {Means, Subject} → C57 |
| `no_one_asserts_incompatible_pair` | theorem | [L378](formal/Logos/Choice.lean#L378) | `theorem no_one_asserts_incompatible_pair : ¬ ∃ s : Subject, ∃ p q : Prop, Assert` | {Means, Subject}  |
| `person_hasChoiceField` | theorem | [L273](formal/Logos/Choice.lean#L273) | `theorem person_hasChoiceField {s : Subject} (hs : Person s) : ∃ p q : Prop, Choi` | {Means, Subject} → C51 |
| `rejectedHornCoMeant` | def | [L200](formal/Logos/Choice.lean#L200) | `def rejectedHornCoMeant : Prop` | {Means, Subject}  |
| `rejectedHornCoMeant_implies_genuineChoice` | theorem | [L219](formal/Logos/Choice.lean#L219) | `theorem rejectedHornCoMeant_implies_genuineChoice : rejectedHornCoMeant → genuin` | {Means, Subject}  |
| `rightWrong_implies_someone_means` | theorem | [L344](formal/Logos/Choice.lean#L344) | `theorem rightWrong_implies_someone_means (h : ¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_` | {AxTwoSubjects, Means, Subject} → C61 |

### `Logos.ClaimMeanings`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `C19` | def | [L32](formal/Logos/ClaimMeanings.lean#L32) | `def C19 : String` | —  |
| `C64` | def | [L62](formal/Logos/ClaimMeanings.lean#L62) | `def C64 : String` | —  |
| `C65` | def | [L64](formal/Logos/ClaimMeanings.lean#L64) | `def C65 : String` | —  |
| `C66` | def | [L66](formal/Logos/ClaimMeanings.lean#L66) | `def C66 : String` | —  |
| `C67` | def | [L68](formal/Logos/ClaimMeanings.lean#L68) | `def C67 : String` | —  |
| `C69` | def | [L48](formal/Logos/ClaimMeanings.lean#L48) | `def C69 : String` | —  |
| `C70` | def | [L50](formal/Logos/ClaimMeanings.lean#L50) | `def C70 : String` | —  |
| `C71` | def | [L52](formal/Logos/ClaimMeanings.lean#L52) | `def C71 : String` | —  |
| `C72` | def | [L54](formal/Logos/ClaimMeanings.lean#L54) | `def C72 : String` | —  |
| `C73` | def | [L56](formal/Logos/ClaimMeanings.lean#L56) | `def C73 : String` | —  |
| `C75` | def | [L58](formal/Logos/ClaimMeanings.lean#L58) | `def C75 : String` | —  |
| `C76` | def | [L60](formal/Logos/ClaimMeanings.lean#L60) | `def C76 : String` | —  |
| `C78` | def | [L36](formal/Logos/ClaimMeanings.lean#L36) | `def C78 : String` | —  |
| `C79` | def | [L38](formal/Logos/ClaimMeanings.lean#L38) | `def C79 : String` | —  |
| `C80` | def | [L70](formal/Logos/ClaimMeanings.lean#L70) | `def C80 : String` | —  |
| `C81` | def | [L72](formal/Logos/ClaimMeanings.lean#L72) | `def C81 : String` | —  |
| `C82` | def | [L74](formal/Logos/ClaimMeanings.lean#L74) | `def C82 : String` | —  |
| `C87` | def | [L40](formal/Logos/ClaimMeanings.lean#L40) | `def C87 : String` | —  |
| `C88` | def | [L42](formal/Logos/ClaimMeanings.lean#L42) | `def C88 : String` | —  |
| `C89` | def | [L44](formal/Logos/ClaimMeanings.lean#L44) | `def C89 : String` | —  |
| `C90` | def | [L46](formal/Logos/ClaimMeanings.lean#L46) | `def C90 : String` | —  |
| `F1b` | def | [L12](formal/Logos/ClaimMeanings.lean#L12) | `def F1b : String` | —  |
| `F2` | def | [L14](formal/Logos/ClaimMeanings.lean#L14) | `def F2 : String` | —  |
| `F3` | def | [L16](formal/Logos/ClaimMeanings.lean#L16) | `def F3 : String` | —  |
| `F4` | def | [L18](formal/Logos/ClaimMeanings.lean#L18) | `def F4 : String` | —  |
| `F5` | def | [L20](formal/Logos/ClaimMeanings.lean#L20) | `def F5 : String` | —  |
| `F6` | def | [L22](formal/Logos/ClaimMeanings.lean#L22) | `def F6 : String` | —  |
| `F7` | def | [L24](formal/Logos/ClaimMeanings.lean#L24) | `def F7 : String` | —  |
| `F8` | def | [L26](formal/Logos/ClaimMeanings.lean#L26) | `def F8 : String` | —  |
| `F9` | def | [L28](formal/Logos/ClaimMeanings.lean#L28) | `def F9 : String` | —  |
| `Q7_2` | def | [L30](formal/Logos/ClaimMeanings.lean#L30) | `def Q7_2 : String` | —  |

### `Logos.Core`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `IsFalse` | def | [L52](formal/Logos/Core.lean#L52) | `def IsFalse (p : Prop) : Prop` | {}  |
| `N_F` | def | [L49](formal/Logos/Core.lean#L49) | `def N_F : Prop` | {}  |
| `N_T` | def | [L46](formal/Logos/Core.lean#L46) | `def N_T : Prop` | {}  |
| `T` | def | [L40](formal/Logos/Core.lean#L40) | `def T (p : Prop) : Prop` | {}  |
| `atomicTruthWitnessed` | theorem | [L85](formal/Logos/Core.lean#L85) | `theorem atomicTruthWitnessed : T True` | {} → C4 |
| `atomicWitnessFalsehood` | theorem | [L117](formal/Logos/Core.lean#L117) | `theorem atomicWitnessFalsehood : IsFalse False` | {}  |
| `bivalence` | theorem | [L186](formal/Logos/Core.lean#L186) | `theorem bivalence : ∀ p : Prop, T p ∨ IsFalse p` | {CL} → C12 |
| `excludedMiddle` | theorem | [L174](formal/Logos/Core.lean#L174) | `theorem excludedMiddle : ∀ p : Prop, T (p ∨ ¬ p)` | {CL} → C10 |
| `greatResult` | theorem | [L156](formal/Logos/Core.lean#L156) | `theorem greatResult : ∃ p q : Prop, T p ∧ IsFalse q` | {} → C8 |
| `negatedAbsolutes` | theorem | [L129](formal/Logos/Core.lean#L129) | `theorem negatedAbsolutes : ¬ (N_T ∨ N_F)` | {} → C35 |
| `noBothTrueAndFalse` | theorem | [L162](formal/Logos/Core.lean#L162) | `theorem noBothTrueAndFalse : ∀ p : Prop, ¬ (T p ∧ IsFalse p)` | {} → C9 |
| `nonContradiction` | theorem | [L180](formal/Logos/Core.lean#L180) | `theorem nonContradiction : ∀ p : Prop, T (¬ (p ∧ ¬ p))` | {} → C11 |
| `notEverythingTrue` | theorem | [L103](formal/Logos/Core.lean#L103) | `theorem notEverythingTrue : ¬ N_F` | {} → C6 |
| `notNothingTrue` | theorem | [L69](formal/Logos/Core.lean#L69) | `theorem notNothingTrue : ¬ N_T` | {} → C2 |
| `nothingFalseRefutes` | theorem | [L94](formal/Logos/Core.lean#L94) | `theorem nothingFalseRefutes : ¬ T N_F` | {} → C5 |
| `nothingTrueRefutes` | theorem | [L61](formal/Logos/Core.lean#L61) | `theorem nothingTrueRefutes : ¬ T N_T` | {} → C1 |
| `rightWrongDistinction` | theorem | [L145](formal/Logos/Core.lean#L145) | `theorem rightWrongDistinction : ¬ N_T ∧ ¬ N_F` | {} → C36 |
| `someFalse` | theorem | [L111](formal/Logos/Core.lean#L111) | `theorem someFalse : ∃ q : Prop, IsFalse q` | {} → C7 |
| `someTrue` | theorem | [L77](formal/Logos/Core.lean#L77) | `theorem someTrue : ∃ p : Prop, T p` | {CL} → C3 |
| `someTruthAndSomeFalsehood` | theorem | [L137](formal/Logos/Core.lean#L137) | `theorem someTruthAndSomeFalsehood : (∃ p : Prop, T p) ∧ (∃ q : Prop, IsFalse q)` | {CL}  |
| `tschema` | theorem | [L43](formal/Logos/Core.lean#L43) | `theorem tschema (p : Prop) : T p ↔ p` | {}  |

### `Logos.CountermodelMeanings`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ActWithoutSubject_refutes` | def | [L16](formal/Logos/CountermodelMeanings.lean#L16) | `def ActWithoutSubject_refutes : String` | —  |
| `ActWithoutSubject_survives` | def | [L19](formal/Logos/CountermodelMeanings.lean#L19) | `def ActWithoutSubject_survives : String` | —  |
| `ContentWithoutPerson_refutes` | def | [L62](formal/Logos/CountermodelMeanings.lean#L62) | `def ContentWithoutPerson_refutes : String` | —  |
| `ContentWithoutPerson_survives` | def | [L65](formal/Logos/CountermodelMeanings.lean#L65) | `def ContentWithoutPerson_survives : String` | —  |
| `ImpersonalUltimateGround_refutes` | def | [L110](formal/Logos/CountermodelMeanings.lean#L110) | `def ImpersonalUltimateGround_refutes : String` | —  |
| `ImpersonalUltimateGround_survives` | def | [L113](formal/Logos/CountermodelMeanings.lean#L113) | `def ImpersonalUltimateGround_survives : String` | —  |
| `InfiniteGroundChain_refutes` | def | [L102](formal/Logos/CountermodelMeanings.lean#L102) | `def InfiniteGroundChain_refutes : String` | —  |
| `InfiniteGroundChain_survives` | def | [L105](formal/Logos/CountermodelMeanings.lean#L105) | `def InfiniteGroundChain_survives : String` | —  |
| `NoFreeWill_refutes` | def | [L46](formal/Logos/CountermodelMeanings.lean#L46) | `def NoFreeWill_refutes : String` | —  |
| `NoFreeWill_survives` | def | [L49](formal/Logos/CountermodelMeanings.lean#L49) | `def NoFreeWill_survives : String` | —  |
| `NoPerson_refutes` | def | [L38](formal/Logos/CountermodelMeanings.lean#L38) | `def NoPerson_refutes : String` | —  |
| `NoPerson_survives` | def | [L41](formal/Logos/CountermodelMeanings.lean#L41) | `def NoPerson_survives : String` | —  |
| `PersonNotNecessary_refutes` | def | [L86](formal/Logos/CountermodelMeanings.lean#L86) | `def PersonNotNecessary_refutes : String` | —  |
| `PersonNotNecessary_survives` | def | [L89](formal/Logos/CountermodelMeanings.lean#L89) | `def PersonNotNecessary_survives : String` | —  |
| `PluralityWithoutLove_refutes` | def | [L118](formal/Logos/CountermodelMeanings.lean#L118) | `def PluralityWithoutLove_refutes : String` | —  |
| `PluralityWithoutLove_survives` | def | [L121](formal/Logos/CountermodelMeanings.lean#L121) | `def PluralityWithoutLove_survives : String` | —  |
| `SubjectNecessityNotEntity_refutes` | def | [L78](formal/Logos/CountermodelMeanings.lean#L78) | `def SubjectNecessityNotEntity_refutes : String` | —  |
| `SubjectNecessityNotEntity_survives` | def | [L81](formal/Logos/CountermodelMeanings.lean#L81) | `def SubjectNecessityNotEntity_survives : String` | —  |
| `SubjectWithoutPerson_refutes` | def | [L32](formal/Logos/CountermodelMeanings.lean#L32) | `def SubjectWithoutPerson_refutes : String` | —  |
| `SubjectWithoutPerson_survives` | def | [L35](formal/Logos/CountermodelMeanings.lean#L35) | `def SubjectWithoutPerson_survives : String` | —  |
| `UnitPlurality_refutes` | def | [L54](formal/Logos/CountermodelMeanings.lean#L54) | `def UnitPlurality_refutes : String` | —  |
| `UnitPlurality_survives` | def | [L57](formal/Logos/CountermodelMeanings.lean#L57) | `def UnitPlurality_survives : String` | —  |
| `VeridicalMeaning_refutes` | def | [L94](formal/Logos/CountermodelMeanings.lean#L94) | `def VeridicalMeaning_refutes : String` | —  |
| `VeridicalMeaning_survives` | def | [L97](formal/Logos/CountermodelMeanings.lean#L97) | `def VeridicalMeaning_survives : String` | —  |
| `WeakActWithoutMeaning_refutes` | def | [L24](formal/Logos/CountermodelMeanings.lean#L24) | `def WeakActWithoutMeaning_refutes : String` | —  |
| `WeakActWithoutMeaning_survives` | def | [L27](formal/Logos/CountermodelMeanings.lean#L27) | `def WeakActWithoutMeaning_survives : String` | —  |
| `WorldwiseTruthmaking_refutes` | def | [L70](formal/Logos/CountermodelMeanings.lean#L70) | `def WorldwiseTruthmaking_refutes : String` | —  |
| `WorldwiseTruthmaking_survives` | def | [L73](formal/Logos/CountermodelMeanings.lean#L73) | `def WorldwiseTruthmaking_survives : String` | —  |

### `Logos.GroundPerson`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AxGroundBearing` | theorem | [L84](formal/Logos/GroundPerson.lean#L84) | `theorem AxGroundBearing {e : Entity} {f : Prop} : GroundProp e f → Realizes e f` | {GroundProp, Subject}  |
| `AxPersonalGround` | axiom | [L107](formal/Logos/GroundPerson.lean#L107) | `axiom AxPersonalGround : ∀ {f : Prop}, IsPresentPersonalFeature f → ∃ e : Entity` | {AxPersonalGround, GroundProp, Means, Subject}  |
| `GroundPrincipleProp` | axiom | [L79](formal/Logos/GroundPerson.lean#L79) | `axiom GroundPrincipleProp : ∀ {f : Prop}, T f → ∃ e : Entity, GroundProp e f` | {GroundPrincipleProp, GroundProp, Subject}  |
| `GroundProp` | axiom | [L60](formal/Logos/GroundPerson.lean#L60) | `axiom GroundProp : Entity → Prop → Prop` | {GroundProp, Subject}  |
| `IsPresentPersonalFeature` | def | [L89](formal/Logos/GroundPerson.lean#L89) | `def IsPresentPersonalFeature (f : Prop) : Prop` | {Means, Subject}  |
| `Personal` | def | [L93](formal/Logos/GroundPerson.lean#L93) | `def Personal (e : Entity) : Prop` | {GroundProp, Means, Subject}  |
| `Realizes` | def | [L66](formal/Logos/GroundPerson.lean#L66) | `def Realizes (e : Entity) (f : Prop) : Prop` | {GroundProp, Subject}  |
| `T8_personalGround` | theorem | [L112](formal/Logos/GroundPerson.lean#L112) | `theorem T8_personalGround {f : Prop} (hf : IsPresentPersonalFeature f) : ∃ e : E` | {AxPersonalGround, GroundProp, Means, Subject} → C32 |
| `necessary_truth_has_necessary_grounder` | theorem | [L125](formal/Logos/GroundPerson.lean#L125) | `theorem necessary_truth_has_necessary_grounder {τ : Form} (hτ : Logos.Truthmaker` | {AxGlobalGround, Ground, Subject} → C34 |
| `present_feature_is_grounded` | theorem | [L120](formal/Logos/GroundPerson.lean#L120) | `theorem present_feature_is_grounded {f : Prop} (ht : T f) (_hf : IsPresentPerson` | {GroundPrincipleProp, GroundProp, Means, Subject} → C33 |

### `Logos.HostileSemantics`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `ActOntology` | structure | [L325](formal/Logos/HostileSemantics.lean#L325) | `structure ActOntology where` | —  |
| `CoreSignature` | structure | [L73](formal/Logos/HostileSemantics.lean#L73) | `structure CoreSignature where` | —  |
| `FreeWillExistence` | def | [L96](formal/Logos/HostileSemantics.lean#L96) | `def FreeWillExistence (I : CoreSignature) : Prop` | {}  |
| `PersonExistence` | def | [L90](formal/Logos/HostileSemantics.lean#L90) | `def PersonExistence (I : CoreSignature) : Prop` | {}  |
| `SubstantiveAuto` | def | [L221](formal/Logos/HostileSemantics.lean#L221) | `def SubstantiveAuto (I : SubstantivePersonhood) : Prop` | {}  |
| `SubstantiveDatum` | def | [L216](formal/Logos/HostileSemantics.lean#L216) | `def SubstantiveDatum (I : SubstantivePersonhood) : Prop` | {}  |
| `SubstantiveDegree` | def | [L222](formal/Logos/HostileSemantics.lean#L222) | `def SubstantiveDegree (I : SubstantivePersonhood) : Prop` | {}  |
| `SubstantiveMind` | def | [L219](formal/Logos/HostileSemantics.lean#L219) | `def SubstantiveMind (I : SubstantivePersonhood) : Prop` | {}  |
| `SubstantivePersonhood` | structure | [L208](formal/Logos/HostileSemantics.lean#L208) | `structure SubstantivePersonhood where` | —  |
| `SubstantiveRatio` | def | [L220](formal/Logos/HostileSemantics.lean#L220) | `def SubstantiveRatio (I : SubstantivePersonhood) : Prop` | {}  |
| `TwoPersons` | def | [L93](formal/Logos/HostileSemantics.lean#L93) | `def TwoPersons (I : CoreSignature) : Prop` | {}  |
| `act_exists_of_act` | theorem | [L319](formal/Logos/HostileSemantics.lean#L319) | `theorem act_exists_of_act (hAct : ∃ s : S, ∃ p : Prop, A s p) : ∃ s : S, ∃ p : P` | {}  |
| `not_entails_content_person` | theorem | [L171](formal/Logos/HostileSemantics.lean#L171) | `theorem not_entails_content_person : ¬ (∀ (S : Type) (Means : S → Prop → Prop) (` | {}  |
| `not_entails_decoupled_freewill` | theorem | [L154](formal/Logos/HostileSemantics.lean#L154) | `theorem not_entails_decoupled_freewill : ¬ (∀ I : CoreSignature, Γ_act I ∧ (∀ s ` | {}  |
| `not_entails_person` | theorem | [L109](formal/Logos/HostileSemantics.lean#L109) | `theorem not_entails_person : ¬ (∀ I : CoreSignature, Γ_person I → PersonExistenc` | {}  |
| `not_entails_plurality` | theorem | [L125](formal/Logos/HostileSemantics.lean#L125) | `theorem not_entails_plurality : ¬ (∀ I : CoreSignature, Γ_act I ∧ (∃ s : I.Subje` | {}  |
| `not_entails_substantive_autonomy` | theorem | [L267](formal/Logos/HostileSemantics.lean#L267) | `theorem not_entails_substantive_autonomy : ¬ (∀ I : SubstantivePersonhood, Subst` | {}  |
| `not_entails_substantive_intentionality` | theorem | [L229](formal/Logos/HostileSemantics.lean#L229) | `theorem not_entails_substantive_intentionality : ¬ (∀ I : SubstantivePersonhood,` | {}  |
| `not_entails_substantive_person` | theorem | [L289](formal/Logos/HostileSemantics.lean#L289) | `theorem not_entails_substantive_person : ¬ (∀ I : SubstantivePersonhood, Substan` | {}  |
| `not_entails_substantive_rationality` | theorem | [L248](formal/Logos/HostileSemantics.lean#L248) | `theorem not_entails_substantive_rationality : ¬ (∀ I : SubstantivePersonhood, Su` | {}  |
| `subject_exists_of_act` | theorem | [L314](formal/Logos/HostileSemantics.lean#L314) | `theorem subject_exists_of_act (hAct : ∃ s : S, ∃ p : Prop, A s p) : ∃ _s : S, Tr` | {}  |
| `Γ_act` | def | [L81](formal/Logos/HostileSemantics.lean#L81) | `def Γ_act (I : CoreSignature) : Prop` | {}  |
| `Γ_means` | def | [L84](formal/Logos/HostileSemantics.lean#L84) | `def Γ_means (I : CoreSignature) : Prop` | {}  |
| `Γ_person` | def | [L87](formal/Logos/HostileSemantics.lean#L87) | `def Γ_person (I : CoreSignature) : Prop` | {}  |

### `Logos.Initiation`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Branches` | def | [L23](formal/Logos/Initiation.lean#L23) | `def Branches {α β : Type} (R : α → β → Prop) : Prop` | {}  |
| `IsTransfer` | def | [L19](formal/Logos/Initiation.lean#L19) | `def IsTransfer {α β : Type} (R : α → β → Prop) : Prop` | {}  |
| `branches_not_transfer` | theorem | [L27](formal/Logos/Initiation.lean#L27) | `theorem branches_not_transfer {α β : Type} {R : α → β → Prop} (h : Branches R) :` | {} → C63 |

### `Logos.Love`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AxPersonStability` | theorem | [L96](formal/Logos/Love.lean#L96) | `theorem AxPersonStability : ∀ s : Subject, Person s → NecessarySubject s` | {Means, Subject}  |
| `Lovable` | def | [L75](formal/Logos/Love.lean#L75) | `def Lovable (t : Subject) : Prop` | {Means, Subject}  |
| `Loves` | def | [L42](formal/Logos/Love.lean#L42) | `def Loves (s t : Subject) : Prop` | {Subject}  |
| `T13_someoneLovable` | theorem | [L81](formal/Logos/Love.lean#L81) | `theorem T13_someoneLovable : ∃ s t : Subject, Person s ∧ Person t ∧ s ≠ t ∧ Lova` | {AxTwoSubjects, Means, Subject} → C41 |
| `T14_content` | theorem | [L194](formal/Logos/Love.lean#L194) | `theorem T14_content : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Loves` | {AxTwoSubjects, Means, Subject} → C43 |
| `T14_eternalRelation` | theorem | [L159](formal/Logos/Love.lean#L159) | `theorem T14_eternalRelation : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | {AxTwoSubjects, Means, Subject} → C42 |
| `T14_square` | theorem | [L184](formal/Logos/Love.lean#L184) | `theorem T14_square : □(∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Love` | {AxTwoSubjects, Means, Subject} → C45 |
| `T14_world` | theorem | [L172](formal/Logos/Love.lean#L172) | `theorem T14_world : ∀ w, ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ Lo` | {AxTwoSubjects, Means, Subject} → C44 |
| `love_affects` | theorem | [L61](formal/Logos/Love.lean#L61) | `theorem love_affects : ∀ {s t : Subject}, Loves s t → Affects s t` | {Subject}  |
| `love_helps` | theorem | [L47](formal/Logos/Love.lean#L47) | `theorem love_helps : ∀ {s t : Subject}, Loves s t → Helps s t` | {Subject} → C86 |
| `love_not_harms` | theorem | [L54](formal/Logos/Love.lean#L54) | `theorem love_not_harms : ∀ {s t : Subject}, Loves s t → ¬ Harms s t` | {Subject}  |
| `loves_of_helps` | theorem | [L69](formal/Logos/Love.lean#L69) | `theorem loves_of_helps : ∀ {s t : Subject}, Helps s t → Loves s t` | {Subject}  |
| `necessaryPersonExists` | theorem | [L129](formal/Logos/Love.lean#L129) | `theorem necessaryPersonExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s` | {Means, Subject} → C77 |
| `necessary_entity_exists` | theorem | [L147](formal/Logos/Love.lean#L147) | `theorem necessary_entity_exists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act` | {Means, Subject} → C92 |
| `no_contingent_person` | theorem | [L110](formal/Logos/Love.lean#L110) | `theorem no_contingent_person : ¬ (∃ s : Subject, Person s ∧ ¬ NecessarySubject s` | {Means, Subject}  |

### `Logos.Modal`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `AxGlobalGround` | axiom | [L67](formal/Logos/Modal.lean#L67) | `axiom AxGlobalGround : ∀ (φ : Form), □ φ → ∃ e : Entity, ∀ w : World, ExistsAt w` | {AxGlobalGround, Ground, Subject}  |
| `Contingent` | def | [L50](formal/Logos/Modal.lean#L50) | `def Contingent (e : Entity) : Prop` | {Subject}  |
| `NecessaryEntity` | def | [L47](formal/Logos/Modal.lean#L47) | `def NecessaryEntity (e : Entity) : Prop` | {Subject}  |
| `T7_excludedMiddleInstance` | theorem | [L80](formal/Logos/Modal.lean#L80) | `theorem T7_excludedMiddleInstance (φ : Form) : ∃ e : Entity, NecessaryEntity e ∧` | {AxGlobalGround, Ground, Subject, CL} → C19 |
| `T7_necessaryReality` | theorem | [L74](formal/Logos/Modal.lean#L74) | `theorem T7_necessaryReality {τ : Form} (hτ : □ τ) : ∃ e : Entity, NecessaryEntit` | {AxGlobalGround, Ground, Subject} → C18 |
| `actualWorld` | def | [L44](formal/Logos/Modal.lean#L44) | `def actualWorld : World` | {}  |
| `necessary_entity_exists_of_necessary_subject` | theorem | [L115](formal/Logos/Modal.lean#L115) | `theorem necessary_entity_exists_of_necessary_subject {s : Subject} (h : Necessar` | {Subject}  |
| `noNecessaryTruthIfAllContingent` | theorem | [L86](formal/Logos/Modal.lean#L86) | `theorem noNecessaryTruthIfAllContingent : (∀ e : Entity, Contingent e) → ∀ φ : F` | {AxGlobalGround, Ground, Subject} → C20 |
| `subject_nec_entity_nec` | theorem | [L103](formal/Logos/Modal.lean#L103) | `theorem subject_nec_entity_nec (s : Subject) : NecessarySubject s → NecessaryEnt` | {Subject} → C91 |
| `subject_nec_entity_nec_iff` | theorem | [L110](formal/Logos/Modal.lean#L110) | `theorem subject_nec_entity_nec_iff (s : Subject) : NecessarySubject s ↔ Necessar` | {Subject}  |

### `Logos.Necessity`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Dia` | def | [L69](formal/Logos/Necessity.lean#L69) | `def ◇(p : Prop) : Prop` | {}  |
| `Necessity` | def | [L51](formal/Logos/Necessity.lean#L51) | `def □(p : Prop) : Prop` | {}  |
| `NecessityPH` | def | [L94](formal/Logos/Necessity.lean#L94) | `def □ₚ(P : WProp) : Prop` | {}  |
| `WProp` | abbrev | [L86](formal/Logos/Necessity.lean#L86) | `abbrev WProp : Type` | {}  |
| `dia_def` | theorem | [L72](formal/Logos/Necessity.lean#L72) | `theorem dia_def {p : Prop} : ◇ p ↔ ¬ □(¬ p)` | {}  |
| `nec4` | theorem | [L64](formal/Logos/Necessity.lean#L64) | `theorem nec4 : ∀ {p : Prop}, □ p → □(□ p)` | {}  |
| `nec4PH` | theorem | [L108](formal/Logos/Necessity.lean#L108) | `theorem nec4PH {P : WProp} : □ₚ P → □ₚ(fun _ => □ₚ P)` | {}  |
| `necDistinction` | theorem | [L116](formal/Logos/Necessity.lean#L116) | `theorem necDistinction : □(¬ N_T ∧ ¬ N_F)` | {} → FAITH-1 |
| `necDistinction_content` | theorem | [L120](formal/Logos/Necessity.lean#L120) | `theorem necDistinction_content : ¬ N_T ∧ ¬ N_F` | {}  |
| `necK` | theorem | [L54](formal/Logos/Necessity.lean#L54) | `theorem necK : ∀ {p q : Prop}, □(p → q) → □ p → □ q` | {}  |
| `necKPH` | theorem | [L97](formal/Logos/Necessity.lean#L97) | `theorem necKPH {P Q : WProp} : □ₚ(fun w => P w → Q w) → □ₚ P → □ₚ Q` | {}  |
| `necMP` | theorem | [L78](formal/Logos/Necessity.lean#L78) | `theorem necMP {p q : Prop} (hpq : □(p → q)) (hp : □ p) : □ q` | {}  |
| `necT` | theorem | [L59](formal/Logos/Necessity.lean#L59) | `theorem necT : ∀ {p : Prop}, □ p → p` | {}  |
| `necTPH` | theorem | [L102](formal/Logos/Necessity.lean#L102) | `theorem necTPH {P : WProp} : □ₚ P → P someWorld` | {}  |
| `nec_apply` | theorem | [L75](formal/Logos/Necessity.lean#L75) | `theorem nec_apply {p : Prop} (hp : □ p) : p` | {}  |
| `someWorld` | def | [L45](formal/Logos/Necessity.lean#L45) | `def someWorld : World` | {}  |

### `Logos.Order`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Correct` | def | [L29](formal/Logos/Order.lean#L29) | `def Correct (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `Fallible` | def | [L74](formal/Logos/Order.lean#L74) | `def Fallible (_s : Subject) (p : Prop) : Prop` | {Subject}  |
| `Incorrect` | def | [L34](formal/Logos/Order.lean#L34) | `def Incorrect (s : Subject) (p : Prop) : Prop` | {Means, Subject}  |
| `NoAct` | def | [L155](formal/Logos/Order.lean#L155) | `def NoAct : Prop` | {Means, Subject}  |
| `T6_fallibility` | theorem | [L90](formal/Logos/Order.lean#L90) | `theorem T6_fallibility : ¬ (∀ s : Subject, ∀ p : Prop, Fallible s p → T p)` | {AxTwoSubjects, Means, Subject} → C28 |
| `T6_truthTranscendsWill` | theorem | [L99](formal/Logos/Order.lean#L99) | `theorem T6_truthTranscendsWill : ¬ (∀ s : Subject, ∀ p : Prop, Fallible s p ↔ T ` | {AxTwoSubjects, Means, Subject} → C29 |
| `consequence_preserves_truth` | theorem | [L150](formal/Logos/Order.lean#L150) | `theorem consequence_preserves_truth {p₁ p₂ q : Prop} (himp : p₁ → p₂ → q) (h1 : ` | {} → C31 |
| `correctness_distinct` | theorem | [L107](formal/Logos/Order.lean#L107) | `theorem correctness_distinct : ¬ (∀ s : Subject, ∀ p : Prop, Correct s p ↔ Incor` | {AxTwoSubjects, Means, Subject, CL} → C30 |
| `fallible_false` | theorem | [L82](formal/Logos/Order.lean#L82) | `theorem fallible_false : ∃ s : Subject, ∃ p : Prop, Fallible s p ∧ IsFalse p` | {AxTwoSubjects, Means, Subject}  |
| `judge_commits` | theorem | [L127](formal/Logos/Order.lean#L127) | `theorem judge_commits : ∃ s : Subject, ∃ p q : Prop, A s p ∧ (Correct s p ∨ Inco` | {AxTwoSubjects, Means, Subject, CL} → C55 |
| `judgment_implies_act` | theorem | [L173](formal/Logos/Order.lean#L173) | `theorem judgment_implies_act {s : Subject} {p : Prop} (h : Correct s p ∨ Incorre` | {Means, Subject}  |
| `judgment_implies_cogito` | theorem | [L185](formal/Logos/Order.lean#L185) | `theorem judgment_implies_cogito (h : (∃ s : Subject, ∃ p : Prop, Correct s p) ∨ ` | {Means, Subject}  |
| `judgment_of_no_act_is_incorrect` | theorem | [L166](formal/Logos/Order.lean#L166) | `theorem judgment_of_no_act_is_incorrect (s : Subject) (h : Correct s NoAct ∨ Inc` | {Means, Subject}  |
| `judgment_of_no_act_proves_act` | theorem | [L180](formal/Logos/Order.lean#L180) | `theorem judgment_of_no_act_proves_act (s : Subject) (h : Correct s NoAct ∨ Incor` | {Means, Subject} → C84 |
| `no_correct_judgment_of_no_act` | theorem | [L159](formal/Logos/Order.lean#L159) | `theorem no_correct_judgment_of_no_act (s : Subject) : ¬ Correct s NoAct` | {Means, Subject} → C83 |
| `rightDistinctWrong_implies_meaning` | theorem | [L62](formal/Logos/Order.lean#L62) | `theorem rightDistinctWrong_implies_meaning (h : (∃ s : Subject, ∃ p : Prop, Corr` | {Means, Subject}  |
| `rightWrongDistinction_implies_meaning` | theorem | [L138](formal/Logos/Order.lean#L138) | `theorem rightWrongDistinction_implies_meaning (_h : ¬ Logos.Core.N_T ∧ ¬ Logos.C` | {AxTwoSubjects, Means, Subject, CL}  |
| `rightWrong_implies_meaning` | theorem | [L46](formal/Logos/Order.lean#L46) | `theorem rightWrong_implies_meaning (h : (∃ s : Subject, ∃ p : Prop, Correct s p)` | {Means, Subject} → C62 |

### `Logos.Person`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `CarriesLogicalFeature` | def | [L138](formal/Logos/Person.lean#L138) | `def CarriesLogicalFeature (a : Prop) : Prop` | {}  |
| `CarriesPersonalFeature` | def | [L134](formal/Logos/Person.lean#L134) | `def CarriesPersonalFeature (a : Prop) : Prop` | {Means, Subject}  |
| `HasFeature` | def | [L131](formal/Logos/Person.lean#L131) | `def HasFeature (a f : Prop) : Prop` | {}  |
| `Intentional` | def | [L49](formal/Logos/Person.lean#L49) | `def Intentional (s : Subject) : Prop` | {Means, Subject}  |
| `Person` | def | [L52](formal/Logos/Person.lean#L52) | `def Person (s : Subject) : Prop` | {Means, Subject}  |
| `RationalAct` | def | [L128](formal/Logos/Person.lean#L128) | `def RationalAct (a : Prop) : Prop` | {Means, Subject}  |
| `act_implies_intentional` | theorem | [L58](formal/Logos/Person.lean#L58) | `theorem act_implies_intentional {s : Subject} {p : Prop} (h : Logos.Agency.Act s` | {Means, Subject}  |
| `inseparability_24b` | theorem | [L144](formal/Logos/Person.lean#L144) | `theorem inseparability_24b : ∀ a : Prop, RationalAct a → (CarriesPersonalFeature` | {Means, Subject, CL} → C25 |
| `intentional_implies_subjectExists` | theorem | [L70](formal/Logos/Person.lean#L70) | `theorem intentional_implies_subjectExists (h : Intentional s) : Logos.Agency.Sub` | {Means, Subject}  |
| `person_exists_of_act` | theorem | [L112](formal/Logos/Person.lean#L112) | `theorem person_exists_of_act (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s ` | {Means, Subject}  |
| `person_exists_of_assert` | theorem | [L119](formal/Logos/Person.lean#L119) | `theorem person_exists_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asser` | {Means, Subject}  |
| `person_intentional_iff` | theorem | [L78](formal/Logos/Person.lean#L78) | `theorem person_intentional_iff (s : Subject) : Person s ↔ Intentional s` | {Means, Subject}  |
| `person_of_act` | theorem | [L105](formal/Logos/Person.lean#L105) | `theorem person_of_act {s : Subject} {p : Prop} (h : Logos.Agency.Act s p) : Pers` | {Means, Subject}  |
| `person_of_subject` | theorem | [L98](formal/Logos/Person.lean#L98) | `theorem person_of_subject {s : Subject} (h : Logos.Agency.SubjectExists s) : Per` | {Means, Subject}  |
| `subjectExists_implies_intentional` | theorem | [L65](formal/Logos/Person.lean#L65) | `theorem subjectExists_implies_intentional (h : Logos.Agency.SubjectExists s) : I` | {Means, Subject}  |

### `Logos.Plurality`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `EntityOf` | def | [L34](formal/Logos/Plurality.lean#L34) | `def EntityOf : Subject → Entity` | {Subject}  |
| `NecessarySubject` | def | [L37](formal/Logos/Plurality.lean#L37) | `def NecessarySubject (s : Subject) : Prop` | {Subject}  |
| `T12_directedPair` | theorem | [L130](formal/Logos/Plurality.lean#L130) | `theorem T12_directedPair : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ ` | {AxTwoSubjects, Means, Subject} → C47 |
| `T12_twoPersons` | theorem | [L44](formal/Logos/Plurality.lean#L44) | `theorem T12_twoPersons : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | {AxTwoSubjects, Means, Subject} → C40 |
| `T1_of_assert` | theorem | [L95](formal/Logos/Plurality.lean#L95) | `theorem T1_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) : ∃` | {Means, Subject}  |
| `T1_subjectExists` | theorem | [L66](formal/Logos/Plurality.lean#L66) | `theorem T1_subjectExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) :` | {Means, Subject} → C21 |
| `T1_subjectExists_from_plurality` | theorem | [L110](formal/Logos/Plurality.lean#L110) | `theorem T1_subjectExists_from_plurality : ∃ s : Subject, Logos.Agency.SubjectExi` | {AxTwoSubjects, Means, Subject}  |
| `T4_agentExists` | theorem | [L74](formal/Logos/Plurality.lean#L74) | `theorem T4_agentExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) : ∃` | {Means, Subject} → C23 |
| `T4_agentExists_from_plurality` | theorem | [L115](formal/Logos/Plurality.lean#L115) | `theorem T4_agentExists_from_plurality : ∃ s : Subject, Logos.Agency.SubjectExist` | {AxTwoSubjects, Means, Subject}  |
| `T4_of_assert` | theorem | [L100](formal/Logos/Plurality.lean#L100) | `theorem T4_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) : ∃` | {Means, Subject}  |
| `T5_of_assert` | theorem | [L105](formal/Logos/Plurality.lean#L105) | `theorem T5_of_assert {s : Subject} {p : Prop} (h : Logos.Agency.Asserts s p) : ∃` | {Means, Subject}  |
| `T5_personExists` | theorem | [L90](formal/Logos/Plurality.lean#L90) | `theorem T5_personExists (h : ∃ s : Subject, ∃ p : Prop, Logos.Agency.Act s p) : ` | {Means, Subject} → C24 |
| `T5_personExists_from_plurality` | theorem | [L121](formal/Logos/Plurality.lean#L121) | `theorem T5_personExists_from_plurality : ∃ s : Subject, Person s` | {AxTwoSubjects, Means, Subject}  |
| `cogito_from_T12` | theorem | [L57](formal/Logos/Plurality.lean#L57) | `theorem cogito_from_T12 : ∃ s : Subject, ∃ p : Prop, Logos.Agency.A s p` | {AxTwoSubjects, Means, Subject} → C48 |
| `notAlone` | theorem | [L50](formal/Logos/Plurality.lean#L50) | `theorem notAlone : ∃ s₁ s₂ : Subject, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | {AxTwoSubjects, Means, Subject}  |

### `Logos.Semantics`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `FalseAt` | def | [L55](formal/Logos/Semantics.lean#L55) | `def FalseAt (w : World) (φ : Form) : Prop` | {}  |
| `Form` | inductive | [L22](formal/Logos/Semantics.lean#L22) | `inductive Form : Type` | —  |
| `NecessarilyFalse` | def | [L61](formal/Logos/Semantics.lean#L61) | `def ¬◇(φ : Form) : Prop` | {}  |
| `NecessarilyTrue` | def | [L58](formal/Logos/Semantics.lean#L58) | `def □(φ : Form) : Prop` | {}  |
| `Satisfies` | def | [L44](formal/Logos/Semantics.lean#L44) | `def Satisfies : World → Form → Prop | w, atom n => w n = TV.t` | {}  |
| `TV` | inductive | [L33](formal/Logos/Semantics.lean#L33) | `inductive TV : Type` | —  |
| `TrueAt` | def | [L52](formal/Logos/Semantics.lean#L52) | `def TrueAt (w : World) (φ : Form) : Prop` | {}  |
| `World` | abbrev | [L41](formal/Logos/Semantics.lean#L41) | `abbrev World : Type` | {}  |
| `atom_not_necessarily_false` | theorem | [L139](formal/Logos/Semantics.lean#L139) | `theorem atom_not_necessarily_false (n : Nat) : ¬ ¬◇atom n` | {}  |
| `atom_not_necessarily_true` | theorem | [L131](formal/Logos/Semantics.lean#L131) | `theorem atom_not_necessarily_true (n : Nat) : ¬ □atom n` | {}  |
| `atoms_are_modally_free` | theorem | [L146](formal/Logos/Semantics.lean#L146) | `theorem atoms_are_modally_free : ∀ n : Nat, ¬ □atom n ∧ ¬ ¬◇atom n` | {} → C95 |
| `bothNecessarilyTrueAndFalse` | theorem | [L102](formal/Logos/Semantics.lean#L102) | `theorem bothNecessarilyTrueAndFalse : (∃ τ : Form, □ τ) ∧ (∃ ρ : Form, ¬◇ ρ)` | {CL} → C37 |
| `lawExcludedMiddle` | theorem | [L76](formal/Logos/Semantics.lean#L76) | `theorem lawExcludedMiddle (φ : Form) : □(φ ∨ ¬φ)` | {CL} → C13 |
| `noStrongTruth_selfRefutes` | theorem | [L121](formal/Logos/Semantics.lean#L121) | `theorem noStrongTruth_selfRefutes : ¬ (¬ ∃ τ : Form, □ τ)` | {CL} → C93 |
| `nonContradiction` | theorem | [L85](formal/Logos/Semantics.lean#L85) | `theorem nonContradiction (φ : Form) : ¬◇(φ ∧ ¬φ)` | {CL} → C14 |
| `sat_and` | theorem | [L67](formal/Logos/Semantics.lean#L67) | `theorem sat_and : w ⊨ (φ ∧ ψ) ↔ w ⊨ φ ∧ w ⊨ ψ` | {}  |
| `sat_imp` | theorem | [L71](formal/Logos/Semantics.lean#L71) | `theorem sat_imp : w ⊨ (φ → ψ) ↔ (w ⊨ φ → w ⊨ ψ)` | {}  |
| `sat_not` | theorem | [L65](formal/Logos/Semantics.lean#L65) | `theorem sat_not : w ⊨ ¬φ ↔ ¬ w ⊨ φ` | {}  |
| `sat_or` | theorem | [L69](formal/Logos/Semantics.lean#L69) | `theorem sat_or : w ⊨ (φ ∨ ψ) ↔ w ⊨ φ ∨ w ⊨ ψ` | {}  |
| `some_formula_contingent` | theorem | [L160](formal/Logos/Semantics.lean#L160) | `theorem some_formula_contingent : ∃ τ : Form, ¬ □ τ ∧ ¬ ¬◇ τ` | {} → C96 |
| `strongTruthExists` | theorem | [L113](formal/Logos/Semantics.lean#L113) | `theorem strongTruthExists : ∃ τ : Form, □ τ` | {CL} → C59 |
| `strongTruth_and_contingent_content` | theorem | [L168](formal/Logos/Semantics.lean#L168) | `theorem strongTruth_and_contingent_content : ∃ τ : Form, □ τ ∧ ∃ σ : Form, ¬ □ σ` | {CL}  |
| `strongTruth_is_not_atomic` | theorem | [L152](formal/Logos/Semantics.lean#L152) | `theorem strongTruth_is_not_atomic : ∃ τ : Form, □ τ ∧ ∀ n : Nat, ¬ □atom n` | {CL}  |

### `Logos.Truthmaker`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Entity` | inductive | [L41](formal/Logos/Truthmaker.lean#L41) | `inductive Entity : Type` | —  |
| `EntityOf` | def | [L46](formal/Logos/Truthmaker.lean#L46) | `def EntityOf (s : Subject) : Entity` | {Subject}  |
| `ExistsAt` | def | [L62](formal/Logos/Truthmaker.lean#L62) | `def ExistsAt (w : World) : Entity → Prop | Entity.ofSubject _ => True` | {Subject}  |
| `Ground` | axiom | [L55](formal/Logos/Truthmaker.lean#L55) | `axiom Ground : Entity → Form → Prop` | {Ground, Subject}  |
| `NecessarilyFalse` | def | [L74](formal/Logos/Truthmaker.lean#L74) | `def ¬◇(φ : Form) : Prop` | {}  |
| `NecessarilyTrue` | def | [L71](formal/Logos/Truthmaker.lean#L71) | `def □(φ : Form) : Prop` | {}  |
| `TrueAt` | def | [L68](formal/Logos/Truthmaker.lean#L68) | `def TrueAt (w : World) (φ : Form) : Prop` | {}  |
| `Truthmaker` | axiom | [L87](formal/Logos/Truthmaker.lean#L87) | `axiom Truthmaker : ∀ (w : World) (φ : Form), w ⊨ φ → ∃ e : Entity, ExistsAt w e ` | {Truthmaker, Ground, Subject}  |
| `groundPrinciple_atom` | theorem | [L94](formal/Logos/Truthmaker.lean#L94) | `theorem groundPrinciple_atom (w : World) (n : Nat) : w ⊨ atom n → ∃ e : Entity, ` | {Truthmaker, Ground, Subject} → C15 |
| `lawExcludedMiddle` | theorem | [L129](formal/Logos/Truthmaker.lean#L129) | `theorem lawExcludedMiddle (φ : Form) : □(φ ∨ ¬φ)` | {CL} → C16 |
| `noGround_selfRefutes` | theorem | [L101](formal/Logos/Truthmaker.lean#L101) | `theorem noGround_selfRefutes : ¬ (∃ (w : World) (n : Nat), w ⊨ atom n ∧ ¬ (∃ e :` | {Truthmaker, Ground, Subject} → C60 |
| `nonContradiction` | theorem | [L137](formal/Logos/Truthmaker.lean#L137) | `theorem nonContradiction (φ : Form) : ¬◇(φ ∧ ¬φ)` | {} → C17 |
| `sat_ground_and` | theorem | [L114](formal/Logos/Truthmaker.lean#L114) | `theorem sat_ground_and {w : World} {φ ψ : Form} : w ⊨ (φ ∧ ψ) ↔ w ⊨ φ ∧ w ⊨ ψ` | {}  |
| `sat_ground_imp` | theorem | [L122](formal/Logos/Truthmaker.lean#L122) | `theorem sat_ground_imp {w : World} {φ ψ : Form} : w ⊨ (φ → ψ) ↔ (w ⊨ φ → w ⊨ ψ)` | {}  |
| `sat_ground_not` | theorem | [L118](formal/Logos/Truthmaker.lean#L118) | `theorem sat_ground_not {w : World} {φ : Form} : w ⊨ ¬φ ↔ ¬ w ⊨ φ` | {}  |
| `sat_ground_or` | theorem | [L110](formal/Logos/Truthmaker.lean#L110) | `theorem sat_ground_or {w : World} {φ ψ : Form} : w ⊨ (φ ∨ ψ) ↔ w ⊨ φ ∨ w ⊨ ψ` | {}  |

### `Logos.Value`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Affects` | def | [L51](formal/Logos/Value.lean#L51) | `def Affects (s t : Subject) : Prop` | {Subject}  |
| `Alone` | def | [L86](formal/Logos/Value.lean#L86) | `def Alone (s : Subject) : Prop` | {Subject}  |
| `AxPersonsAffect` | theorem | [L143](formal/Logos/Value.lean#L143) | `theorem AxPersonsAffect (s₁ s₂ : Subject) (_hs₁ : Person s₁) (_hs₂ : Person s₂) ` | {Means, Subject}  |
| `AxTwoSubjects` | axiom | [L119](formal/Logos/Value.lean#L119) | `axiom AxTwoSubjects : (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ s₁ s₂ : Subject,` | {AxTwoSubjects, Means, Subject} → FAITH-2 |
| `Harms` | def | [L63](formal/Logos/Value.lean#L63) | `def Harms (_s _t : Subject) : Prop` | {Subject}  |
| `Helps` | def | [L57](formal/Logos/Value.lean#L57) | `def Helps (s t : Subject) : Prop` | {Subject}  |
| `OtherAffects` | def | [L83](formal/Logos/Value.lean#L83) | `def OtherAffects (s : Subject) : Prop` | {Subject}  |
| `aloneExcluded` | theorem | [L128](formal/Logos/Value.lean#L128) | `theorem aloneExcluded : ¬ ∃ s : Subject, Person s ∧ Alone s` | {AxTwoSubjects, Means, Subject} → C74 |
| `alone_no_other_affects` | theorem | [L89](formal/Logos/Value.lean#L89) | `theorem alone_no_other_affects {s : Subject} (ha : Alone s) : ¬ OtherAffects s` | {Subject}  |
| `alone_no_other_help_harm` | theorem | [L97](formal/Logos/Value.lean#L97) | `theorem alone_no_other_help_harm {s : Subject} (ha : Alone s) : (¬ ∃ t : Subject` | {Subject} → C56 |
| `harm_affects` | theorem | [L71](formal/Logos/Value.lean#L71) | `theorem harm_affects : ∀ {s t : Subject}, Harms s t → Affects s t` | {Subject}  |
| `help_affects` | theorem | [L66](formal/Logos/Value.lean#L66) | `theorem help_affects : ∀ {s t : Subject}, Helps s t → Affects s t` | {Subject}  |
| `help_not_harm` | theorem | [L78](formal/Logos/Value.lean#L78) | `theorem help_not_harm : ∀ {s t : Subject}, Helps s t → ¬ Harms s t` | {Subject} → C85 |
| `valueInterpersonal_of_split` | theorem | [L151](formal/Logos/Value.lean#L151) | `theorem valueInterpersonal_of_split : (¬ Logos.Core.N_T ∧ ¬ Logos.Core.N_F) → ∃ ` | {AxTwoSubjects, Means, Subject} → C46 |

### `PropositionalPersonhood`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `TripartiteVerdict` | def | [L503](formal/Logos/HostileSemantics.lean#L503) | `def TripartiteVerdict : String` | —  |

### `PropositionalPersonhood.CountermodelContentWithoutPerson`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `Means` | def | [L491](formal/Logos/HostileSemantics.lean#L491) | `def Means : S → Prop → Prop` | —  |
| `Person` | def | [L492](formal/Logos/HostileSemantics.lean#L492) | `def Person : S → Prop` | —  |
| `S` | def | [L490](formal/Logos/HostileSemantics.lean#L490) | `def S : Type` | —  |
| `content_does_not_imply_personhood` | theorem | [L498](formal/Logos/HostileSemantics.lean#L498) | `theorem content_does_not_imply_personhood : (∃ _p : Prop, True) ∧ (∀ p : Prop, ∃` | —  |
| `content_exists` | theorem | [L494](formal/Logos/HostileSemantics.lean#L494) | `theorem content_exists : ∃ _p : Prop, True` | —  |
| `every_content_meant` | theorem | [L495](formal/Logos/HostileSemantics.lean#L495) | `theorem every_content_meant (p : Prop) : ∃ s : S, Means s p` | —  |
| `no_person` | theorem | [L496](formal/Logos/HostileSemantics.lean#L496) | `theorem no_person : ¬ ∃ s : S, Person s` | —  |

### `UnitPluralityCountermodel`

| Name | Kind | Line | Statement (logic) | Axioms |
|---|---|---|---|---|
| `A` | def | [L473](formal/Logos/HostileSemantics.lean#L473) | `def A : S → Prop → Prop` | —  |
| `Person` | def | [L474](formal/Logos/HostileSemantics.lean#L474) | `def Person : S → Prop` | —  |
| `S` | def | [L472](formal/Logos/HostileSemantics.lean#L472) | `def S : Type` | —  |
| `act_occurs` | theorem | [L476](formal/Logos/HostileSemantics.lean#L476) | `theorem act_occurs : ∃ s : S, ∃ p : Prop, A s p` | —  |
| `agency_does_not_imply_plurality` | theorem | [L483](formal/Logos/HostileSemantics.lean#L483) | `theorem agency_does_not_imply_plurality : (∃ s : S, ∃ p : Prop, A s p) ∧ (∃ s : ` | —  |
| `no_plurality` | theorem | [L478](formal/Logos/HostileSemantics.lean#L478) | `theorem no_plurality : ¬ ∃ s t : S, s ≠ t` | —  |
| `person_exists` | theorem | [L477](formal/Logos/HostileSemantics.lean#L477) | `theorem person_exists : ∃ s : S, Person s` | —  |

</details>

---
### D.6 Provenance and regeneration

Every statement, gloss and cost sentence consumed above lives in the Lean sources (docstrings, `String` constants, `Tag:` lines); the generated document transcribes nothing by hand.

- **Kernel:** `formal/Logos/*.lean` — `lake build` green, `sorryAx 0`.
- **Footprints:** `formal/axiom_audit.json` via `#print axioms` (transitive kernel axiom set, meta-logic `CL` included).
- **Dependency edges:** `formal/depgraph.json` (LeanDepViz).
- **Claim ledger (checked, not quoted):** `formal/GAPMAP.md`.
- **Regeneration order:**

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal && lake build
lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot
cd .. && python3 scripts/audit_footprints.py && python3 scripts/build_deduction.py
```

---
