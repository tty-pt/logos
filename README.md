# Γ — The Deduction

> **Γ is a machine-checked deduction.** Right and wrong are real — and satisfaction is free:
> `¬N_T ∧ ¬N_F` needs no one. But being *true* is being true **to** someone: nothing can be
> epistemologically right or wrong without a Free being **for which meaning can mean**
> (C553, the FACT — zero substantive axioms).
>
> Γ no longer needs the Right/Wrong → Meaning route to establish the existence of a Free Subject.
> The earlier route was demoted because it could leave open a vacuity/instantiation problem by
> reasoning about uninhabited concepts or merely stipulated semantic objects; the new primary
> proof starts from an instantiated `JudgmentDeterminationChain` (`Well-Foundedness ⇒
> Ultimate Source ⇒ Agential Ancestry ⇒ Accessible Alternative ⇒ Libertarian Choice ⇒
> Free Will ⇒ Free Subject`).
>
> The central theorem is `complete_libertarian_freedom_argument`, wrapped by
> `proof_exists_implies_existence_of_free_subject`: if this proof exists (`ProofExists C`), an
> anonymous `FreeSubject C s` exists — without claiming the author or reader is that subject.
> The personal grounding of Right/Wrong (`RightWrong ⇒ Person`) remains a separate established result,
> not a premise or step in the Free Subject existence proof.

**How to read a step.** Claim in words first, machine rendering beneath:
- `∴` introduces the symbolic rendering that follows. `≡` reads "by definition" (`📘`);
  `→` and `↔` mean implication and equivalence; `⇒` chains steps into one argument;
  `⇏` marks a demonstrated *non-consequence* (a countermodel frontier, `🧱`).
- a **backticked name** is the Lean declaration that verifies the line; footers like
  `✅ · File.lean#name` link to it under `formal/Logos/`.
- each section reads: claim → the skeptic's move → the reply → one theorem row.
- the chain `Well-Foundedness ⇒ Ultimate Source ⇒ Agential Ancestry ⇒ Accessible Alternative ⇒ Libertarian Choice ⇒ Free Will ⇒ Free Subject ⇒ Choice Bridge ⇒ Person ⇒ Grounds Right/Wrong` is the same argument the numbered
  sections build link by link; the earlier epistemic meaning and deontic routes are kept whole in the ledger.

**Badge legend.** Every icon on a formal consequence is machine-derived from
the Lean kernel (see `formal/GAPMAP.md` and the investigations) — never transcribed:

| icon | meaning |
|---|---|
| `✅` | PROVEN — verified by pure logic; footprint contains only classical meta-logic (`CL`) and the claim's own vocabulary (0 substantive axioms) |
| `⚠️ (AxName)` | AXIOMATIC — machine-verified, yet deliberately rests on the named declared axiom (`SEM` semantic choice / `META` metaphysical bridge) — **not unproved** |
| `📘` | DEFINITIONAL — true by definition of the term being introduced |
| `⚙️` | DERIVATION — machine-verified from its premises, 0 substantive axioms |
| `💰` | PRICED — the same, resting on a declared axiom, named on the PRICE line |
| `⏸` | DEFERRED — a claimed result whose Lean declaration is not in the live kernel; annotated surface only (see GAPMAP + source notes), **NOT a theorem in this repository** |
| `🧱 X ⇏ Y` | COUNTERMODEL — a model forces X nowhere near Y: an explicit boundary, not a failure |

Axioms appear as `◆` in the audit ledger. `AXIOM` (the claim *is itself* a declared
axiom) is distinct from `AXIOMATIC` (the claim is *derived under* an axiom).

<a id="sec-glossary-overloaded-terms"></a>
**Key terms: the three distinctions.** To prevent conflation across distinct formal layers, Γ distinguishes three senses for core terms:
- **Person** (`Subject` · `DivineHypostasis` · `Entity`): `Person s` (free agent) vs. `DivineHypostasis` (divine subsistent center) vs. `PersonCorrelate` (`EntityOf s`).
- **Necessary** (`Entity` · `Subject` genus · `Subject` world-rigid): `NecessaryEntity e` (all worlds) vs. `NecessarySubjectKind s` (modal genus) vs. `NecessarySubject s` (world-rigid).
- **Ground** (`Entity` · Predicate · Relation): `Entity.ofGround` (foundation) vs. `PersonalGround` (indwelling essence) vs. `UniversalModalGround` (universal grounding).

<a id="refutation-index"></a>
## The 21 denials, indexed

Every objection the deduction meets, and what is done to it: 17 deaths, 2 bounds, 2 instantiations. The derivations are worked in [Part III](#sec-part-iii-the-refutations-every-branch-of-the-denial-read); each names the step it makes impossible.

The rest name none, because they have none. 💥 kills a step, 🧱 bounds a reading, 🪞 places the critic inside it — roles and per-row prices are in `formal/GAPMAP.md`.

| The denial | Kind | Where it is answered | What it kills |
|---|---|---|---|
| No right or wrong at all | 💥 | [R1](#r1) | [step 1](#step-1) |
| No meaning | 💥 | [R2](#r2) | [step 3](#step-3) |
| No subject; the empty world | 💥 | [R3](#r3) | [step 4](#step-4) |
| No act — everything is mechanical | 💥 | [R4](#r4) | [step 6](#step-6) |
| No choice (eliminativism) | 💥 | [R5](#r5) | [step 6](#step-6) |
| No choice (determinism) | 💥 | [R6](#r6) | [step 6](#step-6) |
| Normativity is only stipulated | 💥 | [R7](#r7) | [step 5](#step-5) |
| Voluntarism (Euthyphro) | 💥 | [R8](#r8) | [step 8](#step-8) |
| Descriptivism (D3) | 💥 | [R9](#r9) | [step 2](#step-2) |
| No subject for normativity (D4) | 💥 | [R10](#r10) | [step 2](#step-2) |
| Monolithic command (D5) | 💥 | [R11](#r11) | [step 5](#step-5) |
| Ungraspable command (D6) | 💥 | [R12](#r12) | [step 6](#step-6) |
| The ground is just an atom | 💥 | [R13](#r13) | [step 8](#step-8) |
| The ground is a *single* Person | 🧱 | [R14](#r14) | — bound |
| Meaning is unrestricted | 🧱 | [R15](#r15) | — bound |
| That a free subject exists is unestablished | 🪞 | [R16](#r16) | — instantiation |
| The critic who presents the objection is himself a person | 🪞 | [R17](#r17) | — instantiation |
| A Single Person could only give to contingent beings, so its self-giving would depend on them | 💥 | [R18](#r18) | [step 8](#step-8) |
| Denying the donation of the Self | 💥 | [R19](#r19) | [step 8](#step-8) |
| A self-gift is impossible because the donor and the recipient are two things | 💥 | [R20](#r20) | [step 8](#step-8) |
| The Ground cannot give at all, because it is not a person who chooses | 💥 | [R21](#r21) | [step 8](#step-8) |

<a id="sec-part-i-the-deduction"></a>
## Part I — The deduction: a personal kind of ground is forced

Thirteen steps, contiguous and in order. Each one is a block: what it consumes, what it hands on, the premises and steps behind it, and its price. The running state under each step is what has been established *so far*, so the chain can be checked at any point rather than taken on trust at the end.

### The thirteen steps at a glance

One row per step, every status derived from the kernel — never transcribed. Click any name for its Lean source.

| # | Step | Core formula | Derived status |
|---|---|---|---|
| **1** | **WELL-FOUNDEDNESS** — Well-Foundedness of Constitutive Determination | `WellFounded D.Prior` | ✅ **PROVEN** · 0 substantive axioms · [CompleteLibertarianFreedomArgument.lean#well_foundedness](formal/Logos/CompleteLibertarianFreedomArgument.lean#L605), footprint {} |
| **2** | **ULTIMATE SOURCE** — Existence of an Ultimate Internal Source | `∃ a, UltimateInternalSource J.toDeterminationSystem a ∧ (a = x ∨ DeterminesAncestrally […]` | ✅ **PROVEN** · 0 substantive axioms · [CompleteLibertarianFreedomArgument.lean#exists_ultimate_source](formal/Logos/CompleteLibertarianFreedomArgument.lean#L612), footprint {CL} |
| **3** | **JUDGMENT ACT SOURCE** — The Judgment Act Reaches an Ultimate Internal Source | `∃ a, UltimateInternalSource J.toDeterminationSystem a ∧ (a = J.judgmentActNode ∨ […]` | ✅ **PROVEN** · 0 substantive axioms · [CompleteLibertarianFreedomArgument.lean#ultimate_source_reaches_judgment_act](formal/Logos/CompleteLibertarianFreedomArgument.lean#L623), footprint {CL} |
| **4** | **AGENTIAL ANCESTRY** — Agential Ancestry of Judgment Determination | `J.IsActOf s a` | ✅ **PROVEN** · 0 substantive axioms · [CompleteLibertarianFreedomArgument.lean#ultimate_source_is_agential](formal/Logos/CompleteLibertarianFreedomArgument.lean#L633), footprint {} |
| **5** | **NON-RECEIVED DETERMINATION** — Ultimate Act Source Is Not Determined by Prior State | `¬ DeterminationReceivedFromPriorState J a` | ✅ **PROVEN** · 0 substantive axioms · [CompleteLibertarianFreedomArgument.lean#ultimate_source_is_not_received_from_prior_state](formal/Logos/CompleteLibertarianFreedomArgument.lean#L644), footprint {} |
| **6** | **ACCESSIBLE ALTERNATIVE** — Accessible Alternative Under Same Complete Prior State | `∃ w', C.Accessible w w' ∧ C.SameCompletePriorState w w' ∧ J.OutcomeOf a w' ≠ J.OutcomeOf a w` | ✅ **PROVEN** · 0 substantive axioms · [CompleteLibertarianFreedomArgument.lean#accessible_same_past_alternative_exists](formal/Logos/CompleteLibertarianFreedomArgument.lean#L656), footprint {CL} |
| **7** | **VERDICT DIVERGENCE** — Divergence at Source Propagates to Judgment Verdict | `J.OutcomeOf J.verdictNode w' ≠ J.OutcomeOf J.verdictNode w` | ✅ **PROVEN** · 0 substantive axioms · [CompleteLibertarianFreedomArgument.lean#alternative_changes_verdict](formal/Logos/CompleteLibertarianFreedomArgument.lean#L674), footprint {} |
| **8** | **LIBERTARIAN CHOICE** — Verdict Divergence Yields Libertarian Free Choice | `LibertarianFreeChoiceAt C s w p` | ✅ **PROVEN** · 0 substantive axioms · [CompleteLibertarianFreedomArgument.lean#libertarian_free_choice](formal/Logos/CompleteLibertarianFreedomArgument.lean#L694), footprint {CL} |
| **9** | **FREE WILL** — Libertarian Choice Constitutes Free Will | `FreeWillAt C s w` | ✅ **PROVEN** · 0 substantive axioms · [CompleteLibertarianFreedomArgument.lean#free_will](formal/Logos/CompleteLibertarianFreedomArgument.lean#L712), footprint {CL} |
| **10** | **FREE SUBJECT** — Free Will Concludes the Free Subject | `FreeSubject C s` | ✅ **PROVEN** · 0 substantive axioms · [CompleteLibertarianFreedomArgument.lean#complete_libertarian_freedom_argument](formal/Logos/CompleteLibertarianFreedomArgument.lean#L2352), footprint {CL} |
| **11** | **CHOICE BRIDGE** — Canonical Bridge: Libertarian Freedom to Genuine Choice | `FreeSubject gammaSem s → Choice.FreeSubject s` | ✅ **PROVEN** · 0 substantive axioms · [LibertarianPersonhood.lean#gamma_freeSubject_is_choice](formal/Logos/LibertarianPersonhood.lean#L43), footprint {Means, Subject} |
| **12** | **PERSON** — The Free Subject Is an Authoritative Person | `Person s` | ✅ **PROVEN** · 0 substantive axioms · [LibertarianPersonhood.lean#person_exists_via_judgment_chain](formal/Logos/LibertarianPersonhood.lean#L85), footprint {demonstration_occurs, Means, Subject, Will, subjectWill, will_individuation, CL} |
| **13** | **GROUNDS RIGHT/WRONG** — Personal Agency Grounds Objective Right and Wrong | `Person s ∧ GroundsRightWrong s` | ✅ **PROVEN** · 0 substantive axioms · [LibertarianPersonhood.lean#person_grounds_right_wrong_via_judgment_chain](formal/Logos/LibertarianPersonhood.lean#L93), footprint {demonstration_occurs, Means, Subject, Will, subjectWill, will_individuation, CL} |

Edges are typed, and the two directions are not the same move: **[distinction]** separates levels, **[discovery]** carries the chain forward, and **[grounding]** is the person→pole dependence. Part III closes the argument by retorsion.

### The shared vocabulary of the thirteen steps

5 symbols are used by more than one step, so they are defined once here and cross-referenced below rather than restated under each step that uses them. A symbol only one step uses is defined in that step's own vocabulary block. Between them they run from step 1 to step 13.

▸ D The disconnection thesis: propositional correctness has nothing to do with reality.
        ∴ D ≡ ¬∀ s, p, Correct(s, p) → p
        ↳ used at steps 1, 2, 3 · 📘 [RealityHookAudit.lean#D](formal/Logos/RealityHookAudit.lean#L97)


▸ Subject Vocabulary: the pure sort of subjects — that which performs acts of reasoning.
        ↳ used at steps 6, 8, 13 · 📘 [Agency.lean#Subject](formal/Logos/Agency.lean#L49)


▸ FreeWillAt World-Slice Free Will: At world `w`, subject `s` exercises choice between some incompatible alternatives.
        ∴ FreeWillAt ≡ ∃ p, q, ChoosesAt World Subject(MeansAt) w s p q
        ↳ used at steps 9, 10 · 📘 [ModalCreationFrontiers.lean#FreeWillAt](formal/Logos/ModalCreationFrontiers.lean#L849)


▸ World A possible world is a valuation of all atoms.
        ↳ used at steps 5, 6 · 📘 [Semantics.lean#World](formal/Logos/Semantics.lean#L41)


▸ actualWorld The actual world valuation: all atoms true.
        ∴ actualWorld ≡ fun _ => t
        ↳ used at steps 6, 10 · 📘 [Entity.lean#actualWorld](formal/Logos/Entity.lean#L46)

---

<a id="step-1"></a>
### Step 1 — Well-Foundedness of Constitutive Determination

The priority relation in constitutive determination is well-founded (`well_foundedness`), precluding an infinite regress of prior determinants.

DEPENDS ON   — this is the first step
GIVES        well-founded priority yields an ultimate internal source, taken up by step 2
KILLS        [`R1`](#r1)

> ✅ **Price disclosed —** 0 substantive axioms. Core well-founded structural priority.

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

> **The skeptic tries —** "Well-foundedness is an ungrounded postulate; priority can be infinite."
> **The reply —** Strict priority is well-founded by definition; an infinite regress of determination is self-contradictory.

**Vocabulary of this step** — all defined above

↳ Already defined above — `D` in the shared vocabulary.

    DeterminationSystem → WellFounded D.Prior

✅ · [CompleteLibertarianFreedomArgument.lean#well_foundedness](formal/Logos/CompleteLibertarianFreedomArgument.lean#L605)

<a id="step-2"></a>
### Step 2 — Existence of an Ultimate Internal Source

By priority well-foundedness, any node in the determination chain possesses an ancestral ultimate internal source (`exists_ultimate_source`).

DEPENDS ON   step 1: well-founded priority yields an ultimate internal source
GIVES        the judgment act reaches an ultimate internal source, taken up by step 3
KILLS        [`R9`](#r9), [`R10`](#r10)

> ✅ **Price disclosed —** 0 substantive axioms (`{CL}`).

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

> **The skeptic tries —** "Every internal source might receive determination from outside."
> **The reply —** By well-foundedness, every node has an ancestral ultimate internal source.

**Vocabulary of this step** — all defined above

↳ Already defined above — `D` in the shared vocabulary.

    JudgmentDeterminationChain C s w p ∧ J.Node → ∃ a,.Node, UltimateInternalSource J.toDeterminationSystem a ∧ (a = x ∨ DeterminesAncestrally J.Determines a x)

✅ · [CompleteLibertarianFreedomArgument.lean#exists_ultimate_source](formal/Logos/CompleteLibertarianFreedomArgument.lean#L612)

<a id="step-3"></a>
### Step 3 — The Judgment Act Reaches an Ultimate Internal Source

The judgment act node itself reaches an ultimate internal source that determines it ancestral-wise (`ultimate_source_reaches_judgment_act`).

DEPENDS ON   step 2: the judgment act reaches an ultimate internal source
GIVES        ancestral determinants of judgment are acts of the subject, taken up by step 4
KILLS        [`R2`](#r2)

> ✅ **Price disclosed —** 0 substantive axioms (`{CL}`).

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

**Vocabulary of this step** — all defined above

↳ Already defined above — `D` in the shared vocabulary; `DeterminesAncestrally` at step 2.

    JudgmentDeterminationChain C s w p → ∃ a,.Node, UltimateInternalSource J.toDeterminationSystem a ∧ (a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode)

✅ · [CompleteLibertarianFreedomArgument.lean#ultimate_source_reaches_judgment_act](formal/Logos/CompleteLibertarianFreedomArgument.lean#L623)

<a id="step-4"></a>
### Step 4 — Agential Ancestry of Judgment Determination

Any ancestral determinant of the judgment act is constitutively an act of the subject (`ultimate_source_is_agential`).

DEPENDS ON   step 3: ancestral determinants of judgment are acts of the subject
GIVES        an ultimate act source does not receive prior determination, taken up by step 5
KILLS        [`R3`](#r3)

> ✅ **Price disclosed —** 0 substantive axioms.

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

    JudgmentDeterminationChain C s w p ∧ a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode → J.IsActOf s a

✅ · [CompleteLibertarianFreedomArgument.lean#ultimate_source_is_agential](formal/Logos/CompleteLibertarianFreedomArgument.lean#L633)

<a id="step-5"></a>
### Step 5 — Ultimate Act Source Is Not Determined by Prior State

An ultimate internal act source of the subject does not receive determination from the complete prior state (`ultimate_source_is_not_received_from_prior_state`).

DEPENDS ON   step 4: an ultimate act source does not receive prior determination
GIVES        failure of prior determination entails an accessible alternative world, taken up by step 6
KILLS        [`R7`](#r7), [`R11`](#r11)

> ✅ **Price disclosed —** 0 substantive axioms (`{}`).

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

> **The skeptic tries —** "Prior history exhaustively fixes the internal act source."
> **The reply —** An ultimate act source cannot receive determination from the complete prior state.

**Vocabulary of this step** — all defined above

↳ Already defined above — `World` in the shared vocabulary.

    JudgmentDeterminationChain C s w p ∧ UltimateInternalSource J.toDeterminationSystem a ∧ J.IsActOf s a → ¬DeterminationReceivedFromPriorState(J, a)

✅ · [CompleteLibertarianFreedomArgument.lean#ultimate_source_is_not_received_from_prior_state](formal/Logos/CompleteLibertarianFreedomArgument.lean#L644)

<a id="step-6"></a>
### Step 6 — Accessible Alternative Under Same Complete Prior State

Failure of received determination entails an accessible alternative world under the identical complete prior state (`accessible_same_past_alternative_exists`).

DEPENDS ON   step 5: failure of prior determination entails an accessible alternative world
GIVES        source outcome divergence propagates to final verdict, taken up by step 7
KILLS        [`R4`](#r4), [`R5`](#r5), [`R6`](#r6), [`R12`](#r12)

> ✅ **Price disclosed —** 0 substantive axioms (`{CL}`).

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

**Vocabulary of this step** — all defined above

↳ Already defined above — `Subject`, `World`, `actualWorld` in the shared vocabulary.

    JudgmentDeterminationChain C s w p ∧ ¬DeterminationReceivedFromPriorState(J, a) → ∃ w',.World, C.Accessible w w' ∧ C.SameCompletePriorState w w' ∧ J.OutcomeOf a w' ≠ J.OutcomeOf a w

✅ · [CompleteLibertarianFreedomArgument.lean#accessible_same_past_alternative_exists](formal/Logos/CompleteLibertarianFreedomArgument.lean#L656)

<a id="step-7"></a>
### Step 7 — Divergence at Source Propagates to Judgment Verdict

Divergence at the ancestral source propagates through the determination chain to the final judgment verdict (`alternative_changes_verdict`).

DEPENDS ON   step 6: source outcome divergence propagates to final verdict
GIVES        divergent verdict under same past yields libertarian choice, taken up by step 8

> ✅ **Price disclosed —** 0 substantive axioms (`{}`).

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

    JudgmentDeterminationChain C s w p ∧ a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode ∧ J.OutcomeOf a w' ≠ J.OutcomeOf a w → J.OutcomeOf J.verdictNode w' ≠ J.OutcomeOf J.verdictNode w

✅ · [CompleteLibertarianFreedomArgument.lean#alternative_changes_verdict](formal/Logos/CompleteLibertarianFreedomArgument.lean#L674)

<a id="step-8"></a>
### Step 8 — Verdict Divergence Yields Libertarian Free Choice

Opposite judicative verdicts under identical complete prior history construct positive libertarian free choice (`libertarian_free_choice`).

DEPENDS ON   step 7: divergent verdict under same past yields libertarian choice
GIVES        libertarian choice constitutes free will, taken up by step 9
KILLS        [`R8`](#r8), [`R13`](#r13), [`R18`](#r18), [`R19`](#r19), [`R20`](#r20), [`R21`](#r21)

> ✅ **Price disclosed —** 0 substantive axioms (`{CL}`).

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

> **The skeptic tries —** "Indeterminacy is mere luck, not rational libertarian choice."
> **The reply —** Libertarian choice is constructed positively from opposite judicative verdicts under identical prior history.

**Vocabulary of this step** — all defined above

↳ Already defined above — `Subject` in the shared vocabulary.

    JudgmentDeterminationChain C s w p ∧ a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode ∧ ¬DeterminationReceivedFromPriorState(J, a) → LibertarianFreeChoiceAt C s w p

✅ · [CompleteLibertarianFreedomArgument.lean#libertarian_free_choice](formal/Logos/CompleteLibertarianFreedomArgument.lean#L694)

<a id="step-9"></a>
### Step 9 — Libertarian Choice Constitutes Free Will

Exercising libertarian free choice over an alternative in judgment constitutes free will (`free_will`).

DEPENDS ON   step 8: libertarian choice constitutes free will
GIVES        free will in the actual world concludes the Free Subject, taken up by step 10

> ✅ **Price disclosed —** 0 substantive axioms (`{CL}`).

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

**Vocabulary of this step** — all defined above

↳ Already defined above — `FreeWillAt` in the shared vocabulary.

    JudgmentDeterminationChain C s w p ∧ a = J.judgmentActNode ∨ DeterminesAncestrally J.Determines a J.judgmentActNode ∧ ¬DeterminationReceivedFromPriorState(J, a) → FreeWillAt C s w

✅ · [CompleteLibertarianFreedomArgument.lean#free_will](formal/Logos/CompleteLibertarianFreedomArgument.lean#L712)

<a id="step-10"></a>
### Step 10 — Free Will Concludes the Free Subject

Free will in the actual world concludes that the subject is a Free Subject (`free_subject`, `complete_libertarian_freedom_argument`).

DEPENDS ON   step 9: free will in the actual world concludes the Free Subject
GIVES        libertarian freedom bridges to genuine choice, taken up by step 11

> ✅ **Price disclosed —** 0 substantive axioms (`{CL}`). If this proof exists, a Free Subject exists.

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

> **The skeptic tries —** "A proof in logic cannot establish the real existence of a Free Subject."
> **The reply —** The concrete existence of this proof instance strictly derives an anonymous Free Subject.

**Vocabulary of this step** — 1 defined here, 3 above

▸ FreeSubject A subject is a free subject iff it possesses free will (definitionally, genuinely chooses).
        ∴ FreeSubject ≡ FreeWill(s)
        📘 [Choice.lean#FreeSubject](formal/Logos/Choice.lean#L196)

↳ Already defined above — `FreeWillAt`, `actualWorld` in the shared vocabulary; `LibertarianFreeChoiceAt` at step 8.

Complete libertarian freedom argument: the well-founded constitutive determination chain of judgment directly entails a Free Subject.

    JudgmentDeterminationChain C s C.actualWorld p → FreeSubject(C) s

✅ · [CompleteLibertarianFreedomArgument.lean#complete_libertarian_freedom_argument](formal/Logos/CompleteLibertarianFreedomArgument.lean#L2352)

<a id="step-11"></a>
### Step 11 — Canonical Bridge: Libertarian Freedom to Genuine Choice

Libertarian freedom in the canonical semantics strictly derives genuine choice (`gamma_freeSubject_is_choice`).

DEPENDS ON   step 10: libertarian freedom bridges to genuine choice
GIVES        the free subject is constitutively a person, taken up by step 12

> ✅ **Price disclosed —** 0 substantive axioms. Pure logic.

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

> **The skeptic tries —** "Modal divergence across worlds does not yield genuine cognitive choice."
> **The reply —** Divergence under the canonical semantics yields co-meaning of incompatible horns, which definitionally constitutes Choice.

**Vocabulary of this step** — 2 defined here

▸ FreeWill [the definitions census in the ledger](#sec-where-the-rest-of-the-ledger-lives) — freedom (DEFINITION; freedom/choice fix, 2026-09-18): a subject is free iff it genuinely chooses between some incompatible pair.
        ∴ FreeWill ≡ ∃ p, q, Chooses(s, p, q)
        📘 [Choice.lean#FreeWill](formal/Logos/Choice.lean#L188)

▸ Means Vocabulary: the meaning-act relation — a subject means a proposition.
        📘 [Agency.lean#Means](formal/Logos/Agency.lean#L92)

Bridge theorem: Libertarian freedom in the canonical semantics gammaSem strictly derives the genuine choice and Free Subject of Choice.lean.

    CompleteLibertarianFreedomArgument.FreeSubject(gammaSem) s → FreeSubject(s)

✅ · [LibertarianPersonhood.lean#gamma_freeSubject_is_choice](formal/Logos/LibertarianPersonhood.lean#L43)

<a id="step-12"></a>
### Step 12 — The Free Subject Is an Authoritative Person

The Free Subject is constitutively an authoritative Person (`person_exists_via_judgment_chain`).

DEPENDS ON   step 11: the free subject is constitutively a person
GIVES        the person grounds objective right and wrong, taken up by step 13

> ✅ **Price disclosed —** 0 substantive axioms; 1 TRANS (`demonstration_occurs`).

*(Detailed technical proof & model analysis: [investigations/divine-personhood.md](investigations/divine-personhood.md))*

> **The skeptic tries —** "A choosing agent is an epistemic operator, not an individual person."
> **The reply —** Dominion over acts with individuated will strictly constitutes Personhood (`free_subject_is_person`).

**Vocabulary of this step** — 1 defined here

▸ ThomisticPersonCore Thomistic person core: the Boethius–Aquinas conditions of personhood — "individual substance of a rational nature" possessed of dominion over its own acts — formalized through their operative distinguishing features.
        ∴ ThomisticPersonCore ≡ IndividualSubstance(s) ∧ RationalNature(s) ∧ DominionOverActs(s)
        📘 [Person.lean#ThomisticPersonCore](formal/Logos/Person.lean#L93)

Master personhood theorem: The Free Subject delivered by the judgment-determination chain is constitutively an authoritative Person in the Boethian-Thomistic sense.

    ∴ ∃ s, Person(s)

✅ · [LibertarianPersonhood.lean#person_exists_via_judgment_chain](formal/Logos/LibertarianPersonhood.lean#L85)

<a id="step-13"></a>
### Step 13 — Personal Agency Grounds Objective Right and Wrong

The Person established by judgment determination grounds objective Right/Wrong (`person_grounds_right_wrong_via_judgment_chain`).

DEPENDS ON   step 12: the person grounds objective right and wrong
GIVES        — this is the last step

> ✅ **Price disclosed —** 0 substantive axioms; 1 TRANS (`demonstration_occurs`).

*(Detailed technical proof & model analysis: [investigations/grounding.md](investigations/grounding.md))*

> **The skeptic tries —** "Objective correctness might remain grounded in an impersonal structure."
> **The reply —** Normative grounding is transparently forced by personhood (`person_grounds_normative_polarity`).

**Vocabulary of this step** — all defined above

↳ Already defined above — `Person` at step 12; `Subject` in the shared vocabulary.

Master personal-ground theorem: The Person established by the judgment-determination chain grounds objective Right and Wrong. One single witness `s` satisfies all three conditions.

    ∴ ∃ s, Person(s) ∧ GroundsRightWrong s

✅ · [LibertarianPersonhood.lean#person_grounds_right_wrong_via_judgment_chain](formal/Logos/LibertarianPersonhood.lean#L93)

### What the same route also establishes of the person

Eight attributes of a *person* rather than of the ground as such. The census classifies them as `Personal ground / person-type`, and each is a proved theorem, so each gets its price like everything else on this page.

**One thing stated plainly, because it is the easy thing to get wrong:** the spine itself delivers an inhabited person (steps 11–13); these eight are that person's further properties.

The depgraph says so — none of the eight has a spine theorem in its dependency closure. They are reached by parallel personal-grounding lemmas under the same vocabulary, printed here because Part II is for `Entity.ofGround`.

Attaching each one to a numbered step would have been tidier, and false.

<a id="personal_ground_of_right_wrong"></a>
    ▸ **Personal**  ·  Premises: 0 · 0 steps
        ⚙️ DERIVATION — discharged directly, with no intermediate step
        ∴ RightWrong(s) → Person(s)
        PRICE      ✅ **PROVEN** · 0 substantive axioms · `{Means, Subject, Will, subjectWill, will_individuation}`
        SOURCE  ✅ · [PersonalGroundOfReality.lean#personal_ground_of_right_wrong](formal/Logos/PersonalGroundOfReality.lean#L100) (+1 co-route at the same price — see ledger)
        ↑ a personal-scope attribute; reached in parallel with the spine, not by it

<a id="epistemic_ground_is_personal"></a>
    ▸ **Personal**  ·  Premises: 0 · 0 steps
        ⚙️ DERIVATION — discharged directly, with no intermediate step
        ∴ GroundsRightWrongAt s (Correct(s, p)) (Incorrect(s, p)) → Person(s)
        PRICE      ✅ **PROVEN** · 0 substantive axioms · `{Initiates, Means, State, Subject, Will, subjectWill, will_individuation}`
        SOURCE  ✅ · [EpistemicPersonalGround.lean#epistemic_ground_is_personal](formal/Logos/EpistemicPersonalGround.lean#L133)
        ↑ a personal-scope attribute; reached in parallel with the spine, not by it

<a id="person_iff_thomisticCore"></a>
    ▸ **Rational**  ·  Premises: 0 · 1 step
        📘 DEFINITIONAL — 1 step, an identity
          1. definitional equality / reflection
        ∴ Person(s) ↔ ThomisticPersonCore(s)
        PRICE      ✅ **PROVEN** · 0 substantive axioms · `{Means, Subject, Will, subjectWill}`
        SOURCE  ✅ · [Person.lean#person_iff_thomisticCore](formal/Logos/Person.lean#L183)
        ↑ a personal-scope attribute; reached in parallel with the spine, not by it

<a id="indubitable_normative_free_will"></a>
    ▸ **Free**  ·  Premises: 1 · 7 steps
        ⚙️ DERIVATION — 7 compiled steps
        Assume GenuineNormativity s p q
          1. Means(s, p)  (elimination of 1 from h.address)
          2. Means(s, q)  (elimination of 2 from h.address)
          3. Incompatible(p, q)  (elimination of 1 from h.opposition)
          4. Chooses(s, p, q)  (instantiation of Chooses from hMeansP, hMeansQ, hIncomp)
          5. FreeWill(s)  (instantiation of FreeWill from p, q, hChooses)
          6. hChooses  (conjunction conjunct 1: hChooses)
          7. hFreeWill  (conjunction conjunct 2: hFreeWill)
        ∴ Chooses(s, p, q) ∧ FreeWill(s)
        PRICE      ✅ **PROVEN** _(conditional on GenuineNormativity s p q)_ · 0 substantive axioms · `{Means, Subject}`
        SOURCE  ✅ · [IndubitableNormativeFreeWill.lean#indubitable_normative_free_will](formal/Logos/IndubitableNormativeFreeWill.lean#L114) (+2 co-routes at the same price — see ledger)
        ↑ a personal-scope attribute; reached in parallel with the spine, not by it

<a id="asietic_summary"></a>
<a id="weakChoice_implies_asiety"></a>
    ▸ **Asiety**  ·  Premises: 1 · 1 step
        ⚙️ DERIVATION — one step, a constructor
        Assume GenuineNormativity s p q
          1. constructor  (existential constructor introduction)
        ∴ Asiety(EntityOf(s))
        PRICE      ✅ **PROVEN** _(conditional on GenuineNormativity s p q)_ · 0 substantive axioms · `{Means, Subject}`
        SOURCE  ✅ · [AsietyFreedom.lean#weakChoice_implies_asiety](formal/Logos/AsietyFreedom.lean#L172)
        ↑ a personal-scope attribute; reached in parallel with the spine, not by it

<a id="person_iff_freeIndependentWill"></a>
    ▸ **Independent will**  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a constructor
          1. constructor  (existential constructor introduction)
        ∴ Person(s) ↔ FreeIndependentWill(s)
        PRICE      ✅ **PROVEN** · 0 substantive axioms · `{Means, Subject, Will, subjectWill}`
        SOURCE  ✅ · [Person.lean#person_iff_freeIndependentWill](formal/Logos/Person.lean#L166)
        ↑ a personal-scope attribute; reached in parallel with the spine, not by it

<a id="DominionOverActs"></a>
    ▸ **Dominion over acts** / authoritative personhood  ·  Premises: 0 · 0 steps
        📘 DEFINITIONAL — a definition, with no step to show
        ∴ DominionOverActs ≡ FreeWill(s)
        PRICE      📘 **DEFINITIONAL** · 0 substantive axioms · `{Means, Subject}`
        SOURCE  📘 · [Person.lean#DominionOverActs](formal/Logos/Person.lean#L56)
        ↑ a personal-scope attribute; reached in parallel with the spine, not by it

<a id="person_grounds_normative_polarity"></a>
    ▸ **Ground of objective normativity (Right and Wrong)**  ·  Premises: 1 · 0 steps
        ⚙️ DERIVATION — discharged directly, with no intermediate step
        Assume Person(s)
        ∴ GroundsRightWrong s
        PRICE      ✅ **PROVEN** _(conditional on Person(s))_ · 0 substantive axioms · `{Means, Subject, Will, subjectWill}`
        SOURCE  ✅ · [PersonalNormativeGround.lean#person_grounds_normative_polarity](formal/Logos/PersonalNormativeGround.lean#L543)
        ↑ a personal-scope attribute; reached in parallel with the spine, not by it

*8 attribute theorems, each priced above. The rows with no `decl` check — and the two countermodels that cut against this reading — are in Part II's honest list and in the ledger's attribute table.*

**31 formal frontiers** — every unproved step, every countermodel separation and every open bridge, with its exact missing lemma — are listed in [investigations/ledger.md](investigations/ledger.md). Nothing in that list is established; nothing in this file claims otherwise.

## Part II — The characteristics of the ground

19 characteristics, each with the deduction that establishes it. A headline that is a *record* is not one conclusion but a set of them, so each component is expanded in place under its own name; nothing here is asserted without the steps behind it.

<a id="characteristic-index"></a>
### The 19 characteristics at a glance

One row per characteristic, every status derived from the kernel — never transcribed. Click any name to reach its derivation.

| # | Characteristic | Derived status | Price | Components |
|---|---|---|---|---|
| **1** | [The ground is necessary](#ofGround_necessary_ground_of_reality) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | — |
| **2** | [The ground has aseity](#conditional_canonical_aseity) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | — |
| **3** | [Foundational unicity](#ofGround_foundational_unicity) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | 4 sub-derivations (3 a term, not a theorem) |
| **4** | [Sole universal grounding](#ofGround_sole_universal_grounding) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | 4 sub-derivations (3 a term, not a theorem) |
| **5** | [One God](#exactly_one_universal_modal_ground) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | — |
| **6** | [The ground is eternal — ever-present](#the_ground_everlasting) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | — |
| **7** | [The ground is atemporal](#the_ground_atemporal) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | — |
| **8** | [The ground precedes right and wrong](#ofGround_precedes_the_right_wrong_distinction) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | 3 sub-derivations (1 a term, not a theorem) |
| **9** | [The ground is not the universe](#the_ground_is_not_the_universe) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | — |
| **10** | [The ground is not a person-correlate](#ofGround_not_a_person_correlate) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | — |
| **11** | [The ground is simple](#divine_simplicity_sole_bearer) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | — |
| **12** | [The ground is transcendent](#ofGround_sole_transcendent_ground) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | — |
| **13** | [The ground is immutable](#ofGround_divine_immutability) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | 4 sub-derivations |
| **14** | [The ground is omnipresent](#ofGround_foundational_omnipresence) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | 4 sub-derivations |
| **15** | [The ground is pure actuality](#ofGround_divine_pure_actuality) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | 5 sub-derivations |
| **16** | [The ground is omniscient (foundational)](#ofGround_foundational_omniscience) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | 5 sub-derivations |
| **17** | [The ground can do all it can (foundational)](#ofGround_foundational_omnipotence) | ✅ **PROVEN** · 0 substantive axioms | 0 substantive axioms | 4 sub-derivations |
| **18** | [The ground can bring about the satisfiable (causal)](#ground_produces_every_satisfiable_form) | ⚠️ **AXIOMATIC (ground_produces_every_satisfiable_form)** | 1 substantive axiom: ground_produces_every_satisfiable_form | — |
| **19** | [One God in three Persons](#agape_entails_tripersonality) | ⚠️ **AXIOMATIC (AxAgapeEssence, AxProcessionSpirit, AxProcessionWord)** | 3 substantive axioms: AxAgapeEssence, AxProcessionSpirit, AxProcessionWord | — |

**The seam, stated once and not hidden.** Part I established a *person* who grounds the right/wrong poles. These characteristics are about `Entity.ofGround` — the ground *as such*.
The personhood of the ground is confirmed (C228, PROVEN; `PersonalGround` in C590), while hypostatic identity and person-count are distinct (unicity entails neither one nor many; positive plural is C600/C604 free, bridge-free Subject plurality is C73 blocked).

So a characteristic proved here is a characteristic of the ground, and the claim that it is a characteristic of *the person Part I reached* is open. Every block below states which object it is about.

One instantiation is settled: for `g := Entity.ofGround`, `ofGround_not_a_person_correlate` (C564) proves `¬ PersonCorrelate Entity.ofGround` outright — the ground is personal (indwelt by the three Persons), but is not an individual Person-correlate or fourth chooser.

<a id="ofGround_necessary_ground_of_reality"></a>
### The ground is necessary — existence that does not depend on anything else.

DEPENDS ON   no premises — a closed theorem
GIVES        used by `the_ground_grounds_a_contingent_true_chooser`, `claimE`, `singlePersonDenial_summary` (+2 more)

PROOF
    ⚙️ DERIVATION — one step, a constructor
      1. constructor  (existential constructor introduction)
    ∴ NecessaryGroundOfReality Entity.ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#ofGround_necessary_ground_of_reality](formal/Logos/DivineClassicalAttributes.lean#L183)

<a id="conditional_canonical_aseity"></a>
### The ground has aseity — non-derived, non-dependent — and, read conditionally, priced.

DEPENDS ON   ∀ s, ∃ p, ¬Means(s, p)
GIVES        used by `ground_is_canonically_aseitous_but_not_asietic`, `ofGround_modal_aseity_conditional`, `ofGround_no_grounding_potency` (+1 more)

PROOF
    ⚙️ DERIVATION — 2 compiled steps
    Assume ∀ s, ∃ p, ¬Means(s, p)
      1. assume ⟨g, hExt⟩  (hypothesis assumption for conditional/reductio proof)
      2. vacuous contradiction on empty g  (elimination of empty type g (→ ⊥))
    ∴ CanonicalAseity(Entity).ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#conditional_canonical_aseity](formal/Logos/DivineClassicalAttributes.lean#L605)

<a id="ofGround_foundational_unicity"></a>
### Foundational unicity — what unicity means before it is read as one God.

DEPENDS ON   no premises — a closed theorem
GIVES        the established attribute; nothing downstream in the corpus consumes it

PROOF
    ⚙️ DERIVATION — discharged directly, with no intermediate step
    ∴ FoundationalUnicity Entity.ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject, choice, propext, sound}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#ofGround_foundational_unicity](formal/Logos/DivineClassicalAttributes.lean#L2103)

<a id="ofGround_universal_modal_ground"></a>
    ▸ universal_ground  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume _w _e _hExists  (hypothesis assumption for conditional/reductio proof)
        ∴ UniversalModalGround(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_universal_modal_ground](formal/Logos/DivineClassicalAttributes.lean#L1746)
        ↑ a component of ofGround_foundational_unicity

    ▸ atom_exclusion  ·  a term of the record (`fun`), not a named theorem — no separate derivation

    ▸ subject_transcendence  ·  a term of the record (`fun`), not a named theorem — no separate derivation

    ▸ unicity  ·  a term of the record (`fun`), not a named theorem — no separate derivation

<a id="ofGround_sole_universal_grounding"></a>
### Sole universal grounding — one ground bears the modal structure, not several.

DEPENDS ON   ∀ s, ∃ p, ¬Means(s, p)
GIVES        the established attribute; nothing downstream in the corpus consumes it

PROOF
    ⚙️ DERIVATION — discharged directly, with no intermediate step
    Assume ∀ s, ∃ p, ¬Means(s, p)
    ∴ SoleUniversalGrounding Entity.ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#ofGround_sole_universal_grounding](formal/Logos/DivineClassicalAttributes.lean#L2172)

<a id="ofGround_sole_universal_grounding__ofGround_universal_modal_ground"></a>
    ▸ universal_ground  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume _w _e _hExists  (hypothesis assumption for conditional/reductio proof)
        ∴ UniversalModalGround(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_universal_modal_ground](formal/Logos/DivineClassicalAttributes.lean#L1746)
        ↑ a component of ofGround_sole_universal_grounding

    ▸ atom_exclusion  ·  a term of the record (`fun`), not a named theorem — no separate derivation

    ▸ subject_transcendence  ·  a term of the record (`fun`), not a named theorem — no separate derivation

    ▸ unicity  ·  a term of the record (`fun`), not a named theorem — no separate derivation

<a id="exactly_one_universal_modal_ground"></a>
### One God — unity of the Divine Being, with the multi-ground countermodel beside it.

DEPENDS ON   ∀ s, ∃ p, ¬Means(s, p)
GIVES        the established attribute; nothing downstream in the corpus consumes it

PROOF
    ⚙️ DERIVATION — one step, a constructor
    Assume ∀ s, ∃ p, ¬Means(s, p)
      1. constructor  (conjunction constructor introduction)
    ∴ ∃ g, UniversalModalGround(g) ∧ (∀ g', UniversalModalGround(g') → g' = g)

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#exactly_one_universal_modal_ground](formal/Logos/DivineClassicalAttributes.lean#L2196)

<a id="the_ground_everlasting"></a>
### The ground is eternal — ever-present — existence outside the whole of time, not merely endless in it.

DEPENDS ON   no premises — a closed theorem
GIVES        used by `everlasting_and_atemporal_ground`

PROOF
    ⚙️ DERIVATION — discharged directly, with no intermediate step
    ∴ Everlasting(Entity).ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{NecessarySubjectKind, Subject}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#the_ground_everlasting](formal/Logos/DivineClassicalAttributes.lean#L217)

<a id="the_ground_atemporal"></a>
### The ground is atemporal — existence is not time-modulated at all.

DEPENDS ON   no premises — a closed theorem
GIVES        used by `ofGround_stage_invariance`, `everlasting_and_atemporal_ground`

PROOF
    ⚙️ DERIVATION — discharged directly, with no intermediate step
    ∴ Atemporal(Entity).ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{NecessarySubjectKind, Subject}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#the_ground_atemporal](formal/Logos/DivineClassicalAttributes.lean#L221)

<a id="ofGround_precedes_the_right_wrong_distinction"></a>
### The ground precedes right and wrong — the ordering claim Part I needs, stated about the ground.

DEPENDS ON   no premises — a closed theorem
GIVES        the established attribute; nothing downstream in the corpus consumes it

PROOF
    ⚙️ DERIVATION — discharged directly, with no intermediate step
    ∴ PrecedesRightWrong Entity.ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}`
SOURCE     ✅ · [DivineTrinitarianAttributes.lean#ofGround_precedes_the_right_wrong_distinction](formal/Logos/DivineTrinitarianAttributes.lean#L953)

<a id="ofGround_obtains_where_no_atom_is_true"></a>
    ▸ obtains_where_no_atom_is_true  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a constructor
          1. constructor  (conjunction constructor introduction)
        ∴ ∃ w, (∀ n, ¬w ⊨ atom(n)) ∧ ExistsAt(w, Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{NecessarySubjectKind, Subject}`
        SOURCE  ✅ · [DivineTrinitarianAttributes.lean#ofGround_obtains_where_no_atom_is_true](formal/Logos/DivineTrinitarianAttributes.lean#L812)
        ↑ a component of ofGround_precedes_the_right_wrong_distinction

    ▸ conditions_every_bearer  ·  a term of the record (`fun`), not a named theorem — no separate derivation

<a id="ground_scope_is_not_the_truth_set"></a>
    ▸ not_evaluated_by_it  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume h  (hypothesis assumption for conditional/reductio proof)
        ∴ ¬(∀ p, EntityMeans Entity.ofGround p ↔ T(p))
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
        SOURCE  ✅ · [DivineTrinitarianAttributes.lean#ground_scope_is_not_the_truth_set](formal/Logos/DivineTrinitarianAttributes.lean#L885)
        ↑ a component of ofGround_precedes_the_right_wrong_distinction

<a id="the_ground_is_not_the_universe"></a>
### The ground is not the universe — exclusion of pantheism: not identical with the totality.

DEPENDS ON   no premises — a closed theorem
GIVES        the established attribute; nothing downstream in the corpus consumes it

PROOF
    ⚙️ DERIVATION — 2 compiled steps
      1. assume h  (hypothesis assumption for conditional/reductio proof)
      2. witness components ⟨w, x, hxw, hne⟩  (existential elimination from no_entity_is_identical_to_the_whole Entity.ofGround)
    ∴ ¬Universe(Entity).ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{NecessarySubjectKind, Subject}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#the_ground_is_not_the_universe](formal/Logos/DivineClassicalAttributes.lean#L4751)

<a id="ofGround_not_a_person_correlate"></a>
### The ground is not a person-correlate — exclusion of personhood: not an individual Person-correlate (personal ground, not a fourth Person).

DEPENDS ON   no premises — a closed theorem
GIVES        the established attribute; nothing downstream in the corpus consumes it

PROOF
    ⚙️ DERIVATION — discharged directly, with no intermediate step
    ∴ ¬PersonCorrelate(Entity).ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject, Will, subjectWill}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#ofGround_not_a_person_correlate](formal/Logos/DivineClassicalAttributes.lean#L4685)

<a id="divine_simplicity_sole_bearer"></a>
### The ground is simple — simplicity as the sole bearer of the attribute.

DEPENDS ON   ∀ s, ∃ p, ¬Means(s, p)
GIVES        the established attribute; nothing downstream in the corpus consumes it

PROOF
    ⚙️ DERIVATION — one step, a constructor
    Assume ∀ s, ∃ p, ¬Means(s, p)
      1. constructor  (conjunction constructor introduction)
    ∴ DivineSimplicity Entity.ofGround ∧ (∀ e, DivineSimplicity e → e = Entity.ofGround)

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject, propext}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#divine_simplicity_sole_bearer](formal/Logos/DivineClassicalAttributes.lean#L900)

<a id="ofGround_sole_transcendent_ground"></a>
### The ground is transcendent — neither an atom nor a member of the totality.

DEPENDS ON   TranscendentGround(e)
GIVES        used by `the_ground_is_sole_bearer_of_the_footprint_characteristics`

PROOF
    ⚙️ DERIVATION — one step, a projection
    Assume TranscendentGround(e)
      1. vacuous contradiction on empty e  (elimination of empty type e (→ ⊥))
    ∴ e = Entity.ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Subject}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#ofGround_sole_transcendent_ground](formal/Logos/DivineClassicalAttributes.lean#L1583)

<a id="ofGround_divine_immutability"></a>
### The ground is immutable — four invariances, each its own derivation.

DEPENDS ON   no premises — a closed theorem
GIVES        used by `producing_coexists_with_immutability`

PROOF
    ⚙️ DERIVATION — discharged directly, with no intermediate step
    ∴ DivineImmutability Entity.ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, NecessarySubjectKind, State, Subject}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#ofGround_divine_immutability](formal/Logos/DivineClassicalAttributes.lean#L1154)

<a id="ofGround_modal_invariance"></a>
    ▸ modal_invariance  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume w₁ w₂  (hypothesis assumption for conditional/reductio proof)
        ∴ ModalInvariance(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{NecessarySubjectKind, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_modal_invariance](formal/Logos/DivineClassicalAttributes.lean#L1014)
        ↑ a component of ofGround_divine_immutability

<a id="ofGround_stage_invariance"></a>
    ▸ stage_invariance  ·  Premises: 0 · 1 step
        📘 DEFINITIONAL — 1 step, an identity
          1. definitional identity via the_ground_atemporal
        ∴ StageInvariance(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{NecessarySubjectKind, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_stage_invariance](formal/Logos/DivineClassicalAttributes.lean#L1033)
        ↑ a component of ofGround_divine_immutability

<a id="ofGround_transition_invariance"></a>
    ▸ transition_invariance  ·  Premises: 0 · 1 step
        📘 DEFINITIONAL — 1 step, an identity
          1. definitional identity via the_ground_not_in_succession
        ∴ TransitionInvariance(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Initiates, State, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_transition_invariance](formal/Logos/DivineClassicalAttributes.lean#L1060)
        ↑ a component of ofGround_divine_immutability

<a id="ofGround_capacity_invariance"></a>
    ▸ capacity_invariance  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume p _w₁ _w₂  (hypothesis assumption for conditional/reductio proof)
        ∴ CapacityInvariance(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_capacity_invariance](formal/Logos/DivineClassicalAttributes.lean#L1088)
        ↑ a component of ofGround_divine_immutability

<a id="ofGround_foundational_omnipresence"></a>
### The ground is omnipresent — sustaining presence, derived from the ground's own operation.

DEPENDS ON   no premises — a closed theorem
GIVES        the established attribute; nothing downstream in the corpus consumes it

PROOF
    ⚙️ DERIVATION — discharged directly, with no intermediate step
    ∴ FoundationalOmnipresence Entity.ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#ofGround_foundational_omnipresence](formal/Logos/DivineClassicalAttributes.lean#L1830)

<a id="ofGround_world_rigid_presence"></a>
    ▸ presence  ·  Premises: 0 · 2 steps
        ⚙️ DERIVATION — 2 compiled steps
          1. assume _w  (hypothesis assumption for conditional/reductio proof)
          2. definitional identity via trivial
        ∴ WorldRigidPresence(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{NecessarySubjectKind, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_world_rigid_presence](formal/Logos/DivineClassicalAttributes.lean#L1764)
        ↑ a component of ofGround_foundational_omnipresence

<a id="ofGround_foundational_omnipresence__ofGround_universal_modal_ground"></a>
    ▸ universal_ground  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume _w _e _hExists  (hypothesis assumption for conditional/reductio proof)
        ∴ UniversalModalGround(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_universal_modal_ground](formal/Logos/DivineClassicalAttributes.lean#L1746)
        ↑ a component of ofGround_foundational_omnipresence

<a id="ofGround_non_reciprocal_ground"></a>
    ▸ non_reciprocal  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a constructor
          1. constructor  (existential constructor introduction)
        ∴ NonReciprocalGround(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_non_reciprocal_ground](formal/Logos/DivineClassicalAttributes.lean#L1784)
        ↑ a component of ofGround_foundational_omnipresence

<a id="ofGround_maximal_capacity"></a>
    ▸ maximal_capacity  ·  Premises: 0 · 2 steps
        ⚙️ DERIVATION — 2 compiled steps
          1. assume _p  (hypothesis assumption for conditional/reductio proof)
          2. definitional identity via trivial
        ∴ MaximalCapacity(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_maximal_capacity](formal/Logos/DivineClassicalAttributes.lean#L1801)
        ↑ a component of ofGround_foundational_omnipresence

<a id="ofGround_divine_pure_actuality"></a>
### The ground is pure actuality — *Actus Purus*: no potentiality in it.

DEPENDS ON   ∀ s, ∃ p, ¬Means(s, p)
GIVES        the established attribute; nothing downstream in the corpus consumes it

PROOF
    ⚙️ DERIVATION — discharged directly, with no intermediate step
    Assume ∀ s, ∃ p, ¬Means(s, p)
    ∴ DivinePureActuality Entity.ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, NecessarySubjectKind, State, Subject}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#ofGround_divine_pure_actuality](formal/Logos/DivineClassicalAttributes.lean#L2477)

<a id="ofGround_no_existential_potency"></a>
    ▸ no_existential_potency  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume ⟨w, hw⟩  (hypothesis assumption for conditional/reductio proof)
        ∴ ¬PassiveExistentialPotency(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{NecessarySubjectKind, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_no_existential_potency](formal/Logos/DivineClassicalAttributes.lean#L2356)
        ↑ a component of ofGround_divine_pure_actuality

<a id="ofGround_no_grounding_potency"></a>
    ▸ no_grounding_potency  ·  Premises: 1 · 0 steps
        ⚙️ DERIVATION — discharged directly, with no intermediate step
        Assume ∀ s, ∃ p, ¬Means(s, p)
        ∴ ¬PassiveGroundingPotency(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_no_grounding_potency](formal/Logos/DivineClassicalAttributes.lean#L2370)
        ↑ a component of ofGround_divine_pure_actuality

<a id="ofGround_no_transition_potency"></a>
    ▸ no_transition_potency  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume h  (hypothesis assumption for conditional/reductio proof)
        ∴ ¬PassiveTransitionPotency(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Initiates, State, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_no_transition_potency](formal/Logos/DivineClassicalAttributes.lean#L2423)
        ↑ a component of ofGround_divine_pure_actuality

<a id="ofGround_no_intentional_potency"></a>
    ▸ no_intentional_potency  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume ⟨p, hp⟩  (hypothesis assumption for conditional/reductio proof)
        ∴ ¬PassiveIntentionalPotency(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_no_intentional_potency](formal/Logos/DivineClassicalAttributes.lean#L2437)
        ↑ a component of ofGround_divine_pure_actuality

<a id="ofGround_divine_pure_actuality__ofGround_universal_modal_ground"></a>
    ▸ universal_ground  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume _w _e _hExists  (hypothesis assumption for conditional/reductio proof)
        ∴ UniversalModalGround(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_universal_modal_ground](formal/Logos/DivineClassicalAttributes.lean#L1746)
        ↑ a component of ofGround_divine_pure_actuality

<a id="ofGround_foundational_omniscience"></a>
### The ground is omniscient (foundational) — truth-exhausting, and — read at once — *not* truth-tracking.

DEPENDS ON   no premises — a closed theorem
GIVES        the established attribute; nothing downstream in the corpus consumes it

PROOF
    ⚙️ DERIVATION — discharged directly, with no intermediate step
    ∴ FoundationalOmniscience Entity.ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#ofGround_foundational_omniscience](formal/Logos/DivineClassicalAttributes.lean#L3245)

<a id="ofGround_truth_exhaustive"></a>
    ▸ truth_exhaustive  ·  Premises: 0 · 2 steps
        ⚙️ DERIVATION — 2 compiled steps
          1. assume p _  (hypothesis assumption for conditional/reductio proof)
          2. definitional identity via trivial
        ∴ TruthExhaustive(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_truth_exhaustive](formal/Logos/DivineClassicalAttributes.lean#L3167)
        ↑ a component of ofGround_foundational_omniscience

<a id="ofGround_world_truth_exhaustive"></a>
    ▸ world_truth_exhaustive  ·  Premises: 0 · 2 steps
        ⚙️ DERIVATION — 2 compiled steps
          1. assume w φ _  (hypothesis assumption for conditional/reductio proof)
          2. definitional identity via trivial
        ∴ WorldTruthExhaustive(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_world_truth_exhaustive](formal/Logos/DivineClassicalAttributes.lean#L3174)
        ↑ a component of ofGround_foundational_omniscience

<a id="ofGround_undivided_meaning"></a>
    ▸ undivided_scope  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume p q  (hypothesis assumption for conditional/reductio proof)
        ∴ UndividedMeaning(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_undivided_meaning](formal/Logos/DivineClassicalAttributes.lean#L772)
        ↑ a component of ofGround_foundational_omniscience

<a id="ofGround_not_truth_tracking"></a>
    ▸ not_truth_tracking  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume h  (hypothesis assumption for conditional/reductio proof)
        ∴ ¬TruthTracking(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_not_truth_tracking](formal/Logos/DivineClassicalAttributes.lean#L3189)
        ↑ a component of ofGround_foundational_omniscience

<a id="ofGround_foundational_omniscience__ofGround_universal_modal_ground"></a>
    ▸ universal_ground  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume _w _e _hExists  (hypothesis assumption for conditional/reductio proof)
        ∴ UniversalModalGround(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_universal_modal_ground](formal/Logos/DivineClassicalAttributes.lean#L1746)
        ↑ a component of ofGround_foundational_omniscience

<a id="ofGround_foundational_omnipotence"></a>
### The ground can do all it can (foundational) — operative scope: what it can do is what actually obtains.

DEPENDS ON   no premises — a closed theorem
GIVES        the established attribute; nothing downstream in the corpus consumes it

PROOF
    ⚙️ DERIVATION — discharged directly, with no intermediate step
    ∴ FoundationalOmnipotence Entity.ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject, propext}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#ofGround_foundational_omnipotence](formal/Logos/DivineClassicalAttributes.lean#L2929)

<a id="ofGround_gapless_operative_scope"></a>
    ▸ gapless_operate  ·  Premises: 0 · 5 steps
        ⚙️ DERIVATION — 5 compiled steps
          1. assume w P ⟨v, hRv, hPv⟩  (hypothesis assumption for conditional/reductio proof)
          2. v  (conjunction conjunct 1: v)
          3. hRv  (conjunction conjunct 2: hRv)
          4. trivial  (conjunction conjunct 3: trivial)
          5. hPv  (conjunction conjunct 4: hPv)
        ∴ GaplessOperate(UniversalFrame(World), OperatesAt, Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{NecessarySubjectKind, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_gapless_operative_scope](formal/Logos/DivineClassicalAttributes.lean#L2800)
        ↑ a component of ofGround_foundational_omnipotence

<a id="ofGround_operates_only_what_obtains"></a>
    ▸ operates_only_obtaining  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume v P h  (hypothesis assumption for conditional/reductio proof)
        ∴ ∀ v, P, OperatesAt v Entity.ofGround P → P(v)
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{NecessarySubjectKind, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_operates_only_what_obtains](formal/Logos/DivineClassicalAttributes.lean#L2810)
        ↑ a component of ofGround_foundational_omnipotence

<a id="ofGround_does_not_operate_contradictions"></a>
    ▸ operates_no_contradiction  ·  Premises: 0 · 3 steps
        ⚙️ DERIVATION — 3 compiled steps
          1. assume h  (hypothesis assumption for conditional/reductio proof)
          2. v ⊨ (φ ∧ ¬φ)  (elimination of 2 from h)
          3. ¬v ⊨ (φ ∧ ¬φ)
        ∴ ¬OperatesAt v Entity.ofGround (fun u => u ⊨ (φ ∧ ¬φ))
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{NecessarySubjectKind, Subject, propext}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_does_not_operate_contradictions](formal/Logos/DivineClassicalAttributes.lean#L2824)
        ↑ a component of ofGround_foundational_omnipotence

<a id="ofGround_foundational_omnipotence__ofGround_universal_modal_ground"></a>
    ▸ universal_ground  ·  Premises: 0 · 1 step
        ⚙️ DERIVATION — one step, a projection
          1. assume _w _e _hExists  (hypothesis assumption for conditional/reductio proof)
        ∴ UniversalModalGround(Entity).ofGround
        PRICE      ✅ **PROVEN** — 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}`
        SOURCE  ✅ · [DivineClassicalAttributes.lean#ofGround_universal_modal_ground](formal/Logos/DivineClassicalAttributes.lean#L1746)
        ↑ a component of ofGround_foundational_omnipotence

<a id="ground_produces_every_satisfiable_form"></a>
### The ground can bring about the satisfiable (causal) — declared, not derived: C493, and the reason is C483.

DEPENDS ON   no premises — a closed theorem
GIVES        the established attribute; nothing downstream in the corpus consumes it
KILLS        —

DECLARED      ⚠️ **AXIOMATIC (ground_produces_every_satisfiable_form)** — 1 substantive axiom: ground_produces_every_satisfiable_form · `{Produces, Subject, ground_produces_every_satisfiable_form}`
SOURCE     ⚠️ ground_produces_every_satisfiable_form · [DivineThomisticProduction.lean#ground_produces_every_satisfiable_form](formal/Logos/DivineThomisticProduction.lean#L268)

<a id="agape_entails_tripersonality"></a>
### One God in three Persons — Trinity, from the ground's love of the contingent.

DEPENDS ON   no premises — a closed theorem
GIVES        the established attribute; nothing downstream in the corpus consumes it

PROOF
    💰 PRICED — one step, a constructor
      1. constructor  (conjunction constructor introduction)
    ∴ ∃ t,DivineHypostasis Entity, t.P1 = the_father ∧ t.P2 = the_beloved ∧ t.P3 = the_spirit ∧ IsWord the_beloved ∧ IsSpirit the_spirit

PRICE            ⚠️ **AXIOMATIC (AxAgapeEssence, AxProcessionSpirit, AxProcessionWord)** — 3 substantive axioms: AxAgapeEssence, AxProcessionSpirit, AxProcessionWord · `{AxAgapeEssence, AxProcessionSpirit, AxProcessionWord, Subject, choice}`
SOURCE     ⚠️ AxAgapeEssence, AxProcessionSpirit, AxProcessionWord · [DivineTrinitarianAttributes.lean#agape_entails_tripersonality](formal/Logos/DivineTrinitarianAttributes.lean#L2158)

### What is not established about the ground

Eleven of the thirty-nine classical rows have no headline theorem in the kernel. Each gets one line and no section — the honest form of the answer.

| Not established | Declared kind | What is actually the case |
|---|---|---|
| **Psychological personality** | 🧱 COUNTERMODEL | countermodel — the claim is separated, not established |
| **Numerical unitarianism** | 🧱 COUNTERMODEL | countermodel — separation model; unicity does not entail a single Person (see [Part IV's necessary-persons table](#sec-necessary-persons-the-count-at-each-sort): C600/C604 is the free hypostasis-level result; C73 is blocked) |
| **Perfect (moral) goodness** | ⏸ DEFERRED | no kernel declaration at all |
| **Scholastic simplicity** | ❌ NOT ESTABLISHED | not established — strict identity of essence is not proved |
| **Psychological impassibility** | ❌ NOT ESTABLISHED | not established — no kernel declaration |
| **Physical omnipresence** | ❌ NOT ESTABLISHED | not established — spatial presence is a different claim |
| **Quantitative metric infinity** | ❌ NOT ESTABLISHED | not established — an infinite *magnitude* is not derived |
| **Physical / kinetic energy** | ❌ NOT ESTABLISHED | not established — thermodynamic scope is outside the vocabulary |
| **Infallible / counterfactual omniscience** | ❌ NOT ESTABLISHED | **refuted** — it is a field of the proved omniscience, where `ofGround_not_truth_tracking` denies it |
| **Creator of contingent reality** | 🧱 COUNTERMODEL | countermodel — `Produces` is not `Creates` (C110 stands) |
| **Incarnation** | 🧱 COUNTERMODEL | countermodel — the C112 frontier, one God in three Persons with no human instance |

*Part II: 19 characteristics, 26 component sub-derivations expanded in place, 7 record fields holding a term rather than a named theorem, and 11 rows honestly not established.*

<a id="sec-necessity-and-exactly-what-it-costs"></a>
### Necessity, and Exactly What It Costs

8 rows, each a different fact. **The order is necessary with no premise at all.** A free subject and an authoritative Person both exist on the **free main route** (1 TRANS `demonstration_occurs`, 0 substantive axioms).

World-rigid modal necessity (`NecessarySubject s := ∀ w, ExistsAt w (EntityOf s)`) across all possible worlds is a separate modal predicate, priced at the declared bridge `necessaryPersonalSubjectExists` (C404/C409).

The price attaches to the route, never to the name: `FreeSubject` is *defined* as `FreeWill` (`Choice.lean:185`, `freeSubject_iff_freeWill` is `Iff.rfl`), so `freeSubject_exists` and `freeWill_exists` carry the same footprint.

Before 2026-09-30 the surface priced the Free Subject dearer than free will for one identical predicate.

Necessity is the ground's, and the ground is not a subject-correlate: `ofGround_ne_ofSubject` (`{}`).

So "the Person is necessarily true" is true of the *order* and of the *person's agential existence* (0 substantive axioms) — and the world-rigid row is the one that needs C404. Say which, and the sentence is true.

| What it costs | What it settles | Derived status · footprint · source |
|---|---|---|
| The normative order is **necessary** | ∀ w, NormativeOrderAt w — at every world, unconditionally. | ✅ **PROVEN** · 0 substantive axioms · `{Initiates, Means, State, Subject}` · [NecessaryPersonalGround.lean#necessary_normative_order](formal/Logos/NecessaryPersonalGround.lean#L126) {Initiates, Means, State, Subject} |
| The ground is **necessary** | `Entity.ofGround` is modal-fragile-free; a `def` bridge (`NecessarySubjectKind`) is disclosed in [the declared-`def` census in the ledger](#sec-where-the-rest-of-the-ledger-lives) | ✅ **PROVEN** · 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}` · [DivineClassicalAttributes.lean#ofGround_necessary_ground_of_reality](formal/Logos/DivineClassicalAttributes.lean#L183) {Means, NecessarySubjectKind, Subject} |
| A **free subject exists** | Unconditional existence under the stipulated proof, via `free_subject_exists_via_judgment_chain`. 0 substantive axioms, 1 TRANS (`demonstration_occurs`). | ✅ **PROVEN** · 0 substantive axioms · `{Means, Subject, demonstration_occurs, CL}` · [LibertarianPersonhood.lean#free_subject_exists_via_judgment_chain](formal/Logos/LibertarianPersonhood.lean#L68) {demonstration_occurs, Means, Subject, CL} |
| **Free will** exists | The same predicate under the other name; identical 1 TRANS footprint by construction (`free_will_exists_via_judgment_chain`). | ✅ **PROVEN** · 0 substantive axioms · `{Means, Subject, demonstration_occurs, CL}` · [LibertarianPersonhood.lean#free_will_exists_via_judgment_chain](formal/Logos/LibertarianPersonhood.lean#L78) {demonstration_occurs, Means, Subject, CL} |
| An authoritative **person exists** | Unconditional existence under the stipulated proof, via `person_exists_via_judgment_chain`. 0 substantive axioms, 1 TRANS (`demonstration_occurs`). | ✅ **PROVEN** · 0 substantive axioms · `{Means, Subject, Will, subjectWill, will_individuation, demonstration_occurs, CL}` · [LibertarianPersonhood.lean#person_exists_via_judgment_chain](formal/Logos/LibertarianPersonhood.lean#L85) {demonstration_occurs, Means, Subject, Will, subjectWill, will_individuation, CL} |
| A **person** has free will | `Person s → FreeWill s`: 0 substantive axioms. Dominion over acts *is* free will (`Person.lean:56`). | ✅ **PROVEN** · 0 substantive axioms · `{Means, Subject, Will, subjectWill}` · [Person.lean#person_has_free_will](formal/Logos/Person.lean#L157) {Means, Subject, Will, subjectWill} |
| A **necessary person** exists (world-rigid) | C404/C409: derived under the declared META bridge `necessaryPersonalSubjectExists` via `necessary_person_derived_from_bridge`. World-rigid persistence across all possible worlds. | ⚠️ **AXIOMATIC (necessaryPersonalSubjectExists)** · `{Means, NecessarySubjectKind, Subject, Will, subjectWill, necessaryPersonalSubjectExists}` · [NecessaryPersonalGround.lean#necessary_person_derived_from_bridge](formal/Logos/NecessaryPersonalGround.lean#L161) {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} |
| The ground is **not** a subject-correlate | `Entity.ofGround ≠ EntityOf s` for every `s`. The two necessities above are not identified. | ✅ **PROVEN** · 0 substantive axioms · `{Subject}` · [DivineClassicalAttributes.lean#ofGround_ne_ofSubject](formal/Logos/DivineClassicalAttributes.lean#L190) {Subject} |

| Claim | Derived status | What it settles |
|---|---|---|
| `C404` | ◆ **AXIOM** — rests on `necessaryPersonalSubjectExists` · [Plurality.lean#necessaryPersonalSubjectExists](formal/Logos/Plurality.lean#L188), footprint {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} | Metaphysical bridge: the necessary kind of subject is inhabited by a person. |
| `C407` | ⚠️ **AXIOMATIC** — rests on `necessaryPersonalSubjectExists` · [Plurality.lean#necessarySubject_exists](formal/Logos/Plurality.lean#L192), footprint {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} | A necessary subject exists, from the bridge. Footprint: `{Means, NecessarySubjectKind, Subject, Will, necessaryPersonalSubjectExists, subjectWill}`. |
| `C494` | ⚠️ **AXIOMATIC** — rests on `necessaryPersonalSubjectExists` · [DivineThomisticProduction.lean#the_ground_is_not_the_only_necessary_being](formal/Logos/DivineThomisticProduction.lean#L562), footprint {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} | **The ground is not the only necessary being (C494)** — the refutation of *ST* I q.19 a.4 in its extensional reading. |
| `C495` | ⚠️ **AXIOMATIC** — rests on `necessaryPersonalSubjectExists` · [DivineThomisticProduction.lean#necessity_is_not_sole_bearer_of_the_ground](formal/Logos/DivineThomisticProduction.lean#L544), footprint {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} | **Necessity is not sole-bearer of the ground (C495).** No other characteristic in the corpus has this shape: `∀ e, NecessaryEntity e → e = Entity.ofGround` is **false**, because the META bridge […] |

<a id="sec-one-god-in-three-persons"></a>
### One God, in Three Persons

**One God; three Persons; one nature.** Γ's result is not a unitarian monad and not a trinity of three gods: it is one ground, of one nature, in which there are three distinct divine Persons.

All three are divine of the *same* `divineReality` (`the_father_is_divine`, `the_beloved_is_divine`, `the_spirit_is_divine`). Distinctness is personal, not substantial: the Persons are separated, while one ground and one nature carry the unity.

This is the Catholic and Nicene reading — *unus Deus, tres Personae*: one divine being in three persons, consubstantial, distinguished by procession and not by essence. The author is a **Catholic**; this is the reading he reads Γ as supporting.

Read *consubstantial* here as **faith, not a Γ result**. Three things it is not:

the `Consubstantial` anchor was deleted — it was `True` of arbitrary entities, and G9 in `test_personal_ground_kind.py` refuses its return; C573's `MutualIndwelling` was never declared; and C572, the nearest kernel-shaped attempt at the formula, was **withdrawn as Modalism**.

What Γ carries is the *homoousios* half, at a price: one ground that `indwells` every Person, three Persons distinct by role, and the shared **personal property** now derived for free (`two_subsisting_share_one_location`, `{Subject}`).

The shared **nature** is still not in the vocabulary of the sort. C519 and C520 say so in those words.

**What this is not.** Not three Gods: one ground (C320/C389), one nature (C440, *actus purus*, aseity), one shared `divineReality`. And not that Γ *proves* the Trinity — it proves the three Persons on declared premises, and proves that the premises are needed.

| What it costs | What it settles | Derived status · footprint · source |
|---|---|---|
| **One ground** of reality | C320/C389: `∃! g, UniversalModalGround g` (conditional form) / unicity modulo the Persons via `TrinitarianPersonalBridge` (META) and creaturely `SemanticFinitude` (VOCAB). | ✅ **PROVEN** · 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}` · [DivineClassicalAttributes.lean#exactly_one_universal_modal_ground](formal/Logos/DivineClassicalAttributes.lean#L2196) {Means, NecessarySubjectKind, Subject} |
| **One nature** (una natura, *actus purus*) | C440 divine simplicity as the sole bearer; aseity non-derived. 0 substantive axioms. | ✅ **PROVEN** · 0 substantive axioms · `{Means, Subject, CL}` · [DivineClassicalAttributes.lean#divine_simplicity_sole_bearer](formal/Logos/DivineClassicalAttributes.lean#L900) {Means, Subject, CL} · [DivineClassicalAttributes.lean#conditional_canonical_aseity](formal/Logos/DivineClassicalAttributes.lean#L605) {Means, Subject} |
| **Three distinct Persons** | C510: `t.P1 = the_father ∧ t.P2 = the_beloved ∧ t.P3 = the_spirit ∧ IsWord the_beloved ∧ IsSpirit the_spirit`. **Priced on three declared META premises.** | ⚠️ **AXIOMATIC (AxAgapeEssence, AxProcessionSpirit, AxProcessionWord)** · `{Subject, AxAgapeEssence, AxProcessionSpirit, AxProcessionWord, CL}` · [DivineTrinitarianAttributes.lean#agape_entails_tripersonality](formal/Logos/DivineTrinitarianAttributes.lean#L2158) {AxAgapeEssence, AxProcessionSpirit, AxProcessionWord, Subject, CL} |
| All three are **God** (one `divineReality`) | The anti-tritheism half: `is_divine the_father divineReality ∧ is_divine the_beloved divineReality ∧ is_divine the_spirit divineReality`. **Not the price of C510, and cheaper than it** — `the_father_is_divine` and `the_beloved_is_divine` rest on `{Subject, AxAgapeEssence, CL}` (one META), `the_spirit_is_divine` on `{Subject, AxAgapeEssence, AxProcessionSpirit, CL}` (two META), so this row's union is two META axioms where C510 needs three. The word *consubstantial* is not used for this row: the `Consubstantial` anchor was deleted because `Consubstantial Entity.ofGround e f` is `True` of arbitrary entities including atoms — a `{}` price on a `True` proposition is a null result, which is why G9 in `test_personal_ground_kind.py` refuses its re-declaration. The one-ness Γ actually carries is `indwells`, and the shared *nature* is still not in the vocabulary of the sort. | ⚠️ **AXIOMATIC (AxAgapeEssence, AxProcessionSpirit)** · `{Subject, AxAgapeEssence, AxProcessionSpirit, CL}` · [DivineTrinitarianAttributes.lean#the_father_is_divine](formal/Logos/DivineTrinitarianAttributes.lean#L2101) {AxAgapeEssence, Subject, CL} · [DivineTrinitarianAttributes.lean#the_beloved_is_divine](formal/Logos/DivineTrinitarianAttributes.lean#L2106) {AxAgapeEssence, Subject, CL} · [DivineTrinitarianAttributes.lean#the_spirit_is_divine](formal/Logos/DivineTrinitarianAttributes.lean#L2111) {AxAgapeEssence, AxProcessionSpirit, Subject, CL} |
| The Persons are **distinct** (not three gods) | Personal distinctness by personal property, not by essence: `≠` in every pair, and the Spirit is no word. | ⚠️ **AXIOMATIC (AxAgapeEssence, AxProcessionSpirit, AxProcessionWord)** · `{Subject, AxAgapeEssence, AxProcessionSpirit, AxProcessionWord, CL}` · [DivineTrinitarianAttributes.lean#the_beloved_distinct](formal/Logos/DivineTrinitarianAttributes.lean#L1978) {AxAgapeEssence, Subject, CL} · [DivineTrinitarianAttributes.lean#the_spirit_ne_father](formal/Logos/DivineTrinitarianAttributes.lean#L2037) {AxAgapeEssence, AxProcessionSpirit, Subject, CL} · [DivineTrinitarianAttributes.lean#the_spirit_ne_beloved](formal/Logos/DivineTrinitarianAttributes.lean#L2045) {AxAgapeEssence, AxProcessionSpirit, AxProcessionWord, Subject, CL} · [DivineTrinitarianAttributes.lean#the_spirit_ne_any_word](formal/Logos/DivineTrinitarianAttributes.lean#L2041) {AxAgapeEssence, AxProcessionSpirit, Subject, CL} |
| **A single-Person reading is not entailed** | Separation model, not a refutation: one ground, and a model in which that ground bears two distinct persons. Ground-unicity therefore does not entail a single-Person ground — the person-count is left open by unicity. The Godhead is personal (sustaining being and indwelling every Person), but is not an individual Person-correlate among the three. | 🧱 **COUNTERMODEL | unicity_does_not_force_unitarian_monad ⇏ Independence** · `{}` · [DivineClassicalAttributes.lean#unicity_does_not_force_unitarian_monad](formal/Logos/DivineClassicalAttributes.lean#L2224) {} |
| The Trinity is **not free** | C109: the preceding theory does not entail three Persons. This is the price, stated as a countermodel. | 🧱 **COUNTERMODEL | preceding_theory ⇏ trinity** · `{}` · [ConditionalTheology.lean#preceding_theory_not_entails_trinity](formal/Logos/ConditionalTheology.lean#L336) {} |
| The **Incarnation** is open | C112: the preceding theory is consistent with an unincarnate ground. The frontier, named. | 🧱 **COUNTERMODEL | preceding_theory ⇏ incarnation** · `{}` · [ConditionalTheology.lean#preceding_theory_not_entails_incarnation](formal/Logos/ConditionalTheology.lean#L380) {} |

<a id="sec-part-iii-the-refutations-every-branch-of-the-denial-read"></a>
## Part III — The refutations: every branch of the denial, read

Twenty-one entries, R1–R21. Each names the step it makes impossible (`KILLS`) and then shows the derivation: the premises it needs, the steps, the `⊥` — or the negation of its own thesis.

Every line below is compiled from the Lean proof term; the branch, the objection, and which premise is *the thesis* are the only authored strings. Each block's price and kind are derived, and where a priced second route to the same death exists it is shown and priced separately.

A death is classified by derivation, never typed: `⊥` when the goal is `False`; `⊘` when the derivation returns the denial's own negation; 💥 **COLLAPSE** when the denial, followed, destroys the normativity it claims to keep.

🧱 R14 and R15 are **BOUNDARIES**; 🪞 R16 and R17 are the pillar retorsions; 💥 the other 17 are **DERIVATIONS**.

A boundary is not a refutation: a `{}` countermodel bounds the reading, it does not contradict it, so those blocks print no `KILLS`. Where unicity does not force a single person, “the ground is one person” is a consequence, not an absence — that is the boundary's own note, not a gap in the chain.

One former row is gone: “objectivity in a meaningless world”. Its theorem is `{}`, but its premises are `NegativeRetorsionSignature`, `S.NoI`, `S.EO` — a **free-signature artifact**, not a claim about a world (AGENTS.md, 2026-09-29).

The three-axes reading of each model — attack / model / world-datum, with the WRONG-outright vs WRONG-only-if-an-axiom verdict — is with the catalogue: [investigations/catalogues.md](investigations/catalogues.md).

| Pillar of the Seven | Where it is answered |
|---|---|
| 1. Normative Nihilism | 💥 [R1 — No right or wrong at all](#r1) |
| 2. Eliminativism of Choice | 💥 [R5 — No choice (eliminativism)](#r5) |
| 3. Determinism / Incompatibilism | 💥 [R6 — No choice (determinism)](#r6) |
| 4. Theological Smuggling | 🪞 [R16 — That a free subject exists is unestablished](#r16) |
| 5. Euthyphro / Voluntarism | 💥 [R8 — Voluntarism (Euthyphro)](#r8) |
| 6. Physicalist / Atomic Ground | 💥 [R13 — The ground is just an atom](#r13) |
| 7. Origin of Normativity (The Proof-Self Retorsion) | 🪞 [R17 — The critic who presents the objection is himself a person](#r17) |

<a id="r1"></a>
### R1. No right or wrong at all

**💥 DERIVATION** — “There is no objective right and wrong.” **Pillar 1** of the Seven.

<a id="claims_correct_no_right_self_refuting"></a>
**⊥ CONTRADICTION** — The Fundamental Diagonal Retorsion Theorem: Claiming NoRight as correct while NoRight is true produces a strict, constructive contradiction.

DEPENDS ON   the denial: `NoRight`
GIVES        ⊥ — the denial, refuted
KILLS        [step 1](#step-1) — Well-Foundedness of Constitutive Determination

PROOF
    Assume ClaimsCorrect(s, NoRight)  ← voicing the denial as correct
    Assume NoRight  ← the denial's own thesis
      1. Act s NoRight  (elimination of 1 from hClaim)
      2. Correct(s, NoRight)  (instantiation of Logos.Order.Correct from hAct, hTrue)
      3. NormativeRightExists  (existential introduction with witness s)
    ⊥

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, State, Subject}`
SOURCE     ✅ · [DirectNormativeRetorsion.lean#claims_correct_no_right_self_refuting](formal/Logos/DirectNormativeRetorsion.lean#L60)

<a id="r2"></a>
### R2. No meaning

**💥 DERIVATION** — “Reality is brute; nothing is meant.”

<a id="proof_criticism_nihilism_self_refuting"></a>
**⊥ CONTRADICTION** — Dialectical Retorsion: Any skeptic attempting to deny objective correctness in formal derivations by claiming normative nihilism (`NoRight`) refutes itself constructively.

DEPENDS ON   the denial: `NoRight`
GIVES        ⊥ — the denial, refuted
KILLS        [step 3](#step-3) — The Judgment Act Reaches an Ultimate Internal Source

PROOF
    Assume ClaimsCorrect(s, NoRight)  ← voicing the denial as correct
    Assume NoRight  ← the denial's own thesis
    ⊥

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, State, Subject}`
SOURCE     ✅ · [ProofPresentationRetorsion.lean#proof_criticism_nihilism_self_refuting](formal/Logos/ProofPresentationRetorsion.lean#L199)

> A free-signature model is a separate, secondary result: it is a statement about an uninterpreted field, not about a state of affairs.

<a id="r3"></a>
### R3. No subject; the empty world

**💥 DERIVATION** — “There is no one here.”

<a id="noSubject_performative_selfRefutes"></a>
**⊥ CONTRADICTION** — C57: Retorsion — asserting that no subject exists refutes itself.

DEPENDS ON   the denial: `Asserts speaker NoSubject`
GIVES        ⊥ — the denial, refuted
KILLS        [step 4](#step-4) — Agential Ancestry of Judgment Determination

PROOF
    Assume Asserts speaker NoSubject  ← the denial's own thesis
      1. Act speaker NoSubject  (modus ponens via assertion_is_act)
      2. SubjectExists(speaker)  (modus ponens via act_requires_subject)
    ⊥

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, State, Subject}`
SOURCE     ✅ · [Agency.lean#noSubject_performative_selfRefutes](formal/Logos/Agency.lean#L465)

<a id="r4"></a>
### R4. No act — everything is mechanical

**💥 DERIVATION** — “No one acts; there are only events.”

<a id="noAct_conditional_selfRefutes"></a>
**⊥ CONTRADICTION** — Asserting NoAct refutes itself under a weak assertion ONLY given the bridge from weak act to strong Act.

DEPENDS ON   the denial: `asserts speaker NoAct`
GIVES        ⊥ — the denial, refuted
KILLS        [step 6](#step-6) — Accessible Alternative Under Same Complete Prior State

PROOF
    Assume weak_act_implies_strong_act
    Assume asserts speaker NoAct  ← the denial's own thesis
    ⊥

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, State, Subject, act}`
SOURCE     ✅ · [Agency.lean#noAct_conditional_selfRefutes](formal/Logos/Agency.lean#L406)

<a id="r5"></a>
### R5. No choice (eliminativism)

**💥 DERIVATION** — “Normative address does not imply genuine choice.” **Pillar 2** of the Seven.

<a id="d7_co_grasp_is_definitionally_choice"></a>
**⊥ CONTRADICTION** — D7: Denial of Choice from Co-Grasp — denying Chooses when incompatible alternatives are co-grasped is a direct formal contradiction.

DEPENDS ON   the denial: `¬Chooses s p q`
GIVES        ⊥ — the denial, refuted
KILLS        [step 6](#step-6) — Accessible Alternative Under Same Complete Prior State

PROOF
    Assume Means(s, p)
    Assume Means(s, q)
    Assume Incompatible(p, q)
    Assume ¬Chooses(s, p, q)  ← the denial's own thesis
    ⊥

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
SOURCE     ✅ · [UndeniableNormativeDerivation.lean#d7_co_grasp_is_definitionally_choice](formal/Logos/UndeniableNormativeDerivation.lean#L267)

<a id="r6"></a>
### R6. No choice (determinism)

**💥 DERIVATION** — “Freedom requires physical indeterminism.” **Pillar 3** of the Seven.

<a id="d8_choice_is_definitionally_free_will"></a>
**⊥ CONTRADICTION** — D8: Denial of Free Will from Choice — denying FreeWill when Chooses obtains is a direct formal contradiction.

DEPENDS ON   the denial: `¬FreeWill s`
GIVES        ⊥ — the denial, refuted
KILLS        [step 6](#step-6) — Accessible Alternative Under Same Complete Prior State

PROOF
    Assume Chooses(s, p, q)
    Assume ¬FreeWill(s)  ← the denial's own thesis
    ⊥

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
SOURCE     ✅ · [UndeniableNormativeDerivation.lean#d8_choice_is_definitionally_free_will](formal/Logos/UndeniableNormativeDerivation.lean#L275)

<a id="r7"></a>
### R7. Normativity is only stipulated

**💥 DERIVATION** — “Moral norms are just stipulations.”

<a id="normative_denial_of_normativity_is_self_refuting"></a>
**⊥ CONTRADICTION** — Non-vacuous self-refutation of the denial of GenuineNormativity under the normative correctness stance.

DEPENDS ON   the denial: `NoGN`
GIVES        ⊥ — the denial, refuted
KILLS        [step 5](#step-5) — Ultimate Act Source Is Not Determined by Prior State

PROOF
    Assume ClaimsNormativeCorrectness(s, NoGN)  ← voicing the denial as correct
    Assume NoGN  ← the denial's own thesis
      1. GenuineNormativityExists  (existential introduction with witness s)
    ⊥

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, State, Subject, choice, propext, sound}`
SOURCE     ✅ · [RetorsiveNormativity.lean#normative_denial_of_normativity_is_self_refuting](formal/Logos/RetorsiveNormativity.lean#L193)

<a id="denial_of_genuine_normativity_is_self_refuting"></a>
### a second, priced route

**⚠️ PRICED — the denial refuted, at a declared price** — Non-vacuous self-refutation of the denial of GenuineNormativity.

DEPENDS ON   the denial: `NoGN`
GIVES        the denial is refuted, at the price named below
KILLS        [step 5](#step-5) — Ultimate Act Source Is Not Determined by Prior State

PROOF
    Assume ClaimsCorrect(s, NoGN)
    Assume NoGN  ← the denial's own thesis
      1. GenuineNormativity s NoGN (¬NoGN)  ()
      2. GenuineNormativityExists  (existential introduction with witness s)
    False  — refuted, at the declared price on the PRICE line

PRICE            ⚠️ **AXIOMATIC (AxJudicativeBipolarity)** — 1 substantive axiom: AxJudicativeBipolarity · `{AxJudicativeBipolarity, Initiates, Means, State, Subject}`
> A second, independently sufficient refutation — but priced on one SEM choice (`AxJudicativeBipolarity`), so the free route is the one read above.
SOURCE     ⚠️ AxJudicativeBipolarity · [RetorsiveNormativity.lean#denial_of_genuine_normativity_is_self_refuting](formal/Logos/RetorsiveNormativity.lean#L138)

<a id="r8"></a>
### R8. Voluntarism (Euthyphro)

**💥 DERIVATION** — “Ought is just will; the person invents morality.” **Pillar 5** of the Seven.

<a id="self_grounded_assertion_incoherent"></a>
**⊥ CONTRADICTION** — Performative Incoherence of Asserting Self-Legislation.

DEPENDS ON   the denial: `Ought s s a`
GIVES        ⊥ — the denial, refuted
KILLS        [step 8](#step-8) — Verdict Divergence Yields Libertarian Free Choice

PROOF
    Assume Ought(s, s, a)  ← the denial's own thesis
    Assume SelfLegislation(s)
    Assume SubjectWills(s, a).neg
    Assume SubjectWills(s, a).neg → ¬SubjectWills(s, a)
    ⊥

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Ought, Subject, Wills}`
SOURCE     ✅ · [OughtRetorsion.lean#self_grounded_assertion_incoherent](formal/Logos/OughtRetorsion.lean#L129)

<a id="will_identity_collapses_normativity"></a>
### the collapse itself

**⊥ CONTRADICTION** — Volition Is Not Normative Ground by Identity: Identifying practical obligation with the subject's own current willing (`SelfLegislation s`) destroys the logical possibility of normative violation, collapsing normativity.

DEPENDS ON   the denial: `∀ r, Ought r s a → r = s`
GIVES        ⊥ — the denial, refuted
KILLS        [step 8](#step-8) — Verdict Divergence Yields Libertarian Free Choice

PROOF
    Assume SelfLegislation(s)
    Assume PracticalAction
    Assume ∀ r, Ought(r, s, a) → r = s  ← the denial's own thesis
    Assume SubjectWills(s, a).neg → ¬SubjectWills(s, a)
    ⊥

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Ought, Subject, Wills}`
SOURCE     ✅ · [PersonalNormativeGround.lean#will_identity_collapses_normativity](formal/Logos/PersonalNormativeGround.lean#L361)

<a id="r9"></a>
### R9. Descriptivism (D3)

**💥 DERIVATION** — “Truth is only descriptive; there is no deontic guidance at all.”

<a id="d3_descriptive_truth_lacks_deontic_guidance"></a>
**⊘ DENIAL REFUTED** — D3: Denial of Prescriptivity — asserting that Right/Wrong is merely descriptive truth lacks deontic guidance and is refuted by genuine normativity.

DEPENDS ON   the denial: `hDescriptiveOnly → ∀ s, ¬AgentialDeonticAddress s p q`
GIVES        ⊘ — the denial, refuted
KILLS        [step 2](#step-2) — Existence of an Ultimate Internal Source

PROOF
    Assume hDescriptiveOnly → ∀ s, ¬AgentialDeonticAddress(s, p, q)  ← the denial's own thesis
    Assume ∃ s, GenuineNormativity s p q
      1. assume hDesc  (hypothesis assumption for conditional/reductio proof)
      2. witness components ⟨s, hNormInst⟩  (existential elimination from hNorm)
    ⊘ ¬hDescriptiveOnly  — the denial's own negation

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
SOURCE     ✅ · [UndeniableNormativeDerivation.lean#d3_descriptive_truth_lacks_deontic_guidance](formal/Logos/UndeniableNormativeDerivation.lean#L233)

<a id="r10"></a>
### R10. No subject for normativity (D4)

**💥 DERIVATION** — “An ought can bind no one; normativity needs no subject.”

<a id="d4_impersonal_normativity_fails_relationality"></a>
**COLLAPSE — INCOHERENT** — D4: Denial of Agential Address — impersonal ought without an addressed subject fails relationality.

DEPENDS ON   the denial: `∀ s, ¬AgentialDeonticAddress s p q`
GIVES        ⊥ — the order cannot be kept, and collapses
KILLS        [step 2](#step-2) — Existence of an Ultimate Internal Source

PROOF
    Assume ∀ s, ¬AgentialDeonticAddress(s, p, q)  ← the denial's own thesis
    ¬∃ s, GenuineNormativity s p q  — the denial, followed, destroys what it claims to keep

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
SOURCE     ✅ · [UndeniableNormativeDerivation.lean#d4_impersonal_normativity_fails_relationality](formal/Logos/UndeniableNormativeDerivation.lean#L244)

<a id="r11"></a>
### R11. Monolithic command (D5)

**💥 DERIVATION** — “A command with no alternative is still a command.”

<a id="d5_monolithic_command_lacks_opposition"></a>
**COLLAPSE — INCOHERENT** — D5: Denial of Incompatible Alternatives — a monolithic command without opposition lacks choice.

DEPENDS ON   the denial: `∀ q, ¬Incompatible p q`
GIVES        ⊥ — the order cannot be kept, and collapses
KILLS        [step 5](#step-5) — Ultimate Act Source Is Not Determined by Prior State

PROOF
    Assume ∀ q, ¬Incompatible(p, q)  ← the denial's own thesis
    ¬∃ s, q, GenuineNormativity s p q  — the denial, followed, destroys what it claims to keep

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Subject}`
SOURCE     ✅ · [UndeniableNormativeDerivation.lean#d5_monolithic_command_lacks_opposition](formal/Logos/UndeniableNormativeDerivation.lean#L252)

<a id="r12"></a>
### R12. Ungraspable command (D6)

**💥 DERIVATION** — “A command nobody can grasp is still a command.”

<a id="d6_ungraspable_command_fails_agential_address"></a>
**COLLAPSE — INCOHERENT** — D6: Denial of Cognitive Grasp — an ungraspable command fails agential address.

DEPENDS ON   the denial: `¬(Means s p ∧ Means s q)`
GIVES        ⊥ — the order cannot be kept, and collapses
KILLS        [step 6](#step-6) — Accessible Alternative Under Same Complete Prior State

PROOF
    Assume ¬(Means(s, p) ∧ Means(s, q))  ← the denial's own thesis
      1. ¬AgentialDeonticAddress(s, p, q)  (definitional identity via hUngraspable)
    ¬AgentialDeonticAddress(s, p, q)  — the denial, followed, destroys what it claims to keep

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
SOURCE     ✅ · [UndeniableNormativeDerivation.lean#d6_ungraspable_command_fails_agential_address](formal/Logos/UndeniableNormativeDerivation.lean#L259)

<a id="r13"></a>
### R13. The ground is just an atom

**💥 DERIVATION** — “The ultimate ground is a particle.” **Pillar 6** of the Seven.

<a id="atom_grounding_the_ground_yields_contradiction"></a>
**⊥ CONTRADICTION** — Direct refutation: assuming an atom ontologically grounds the ground derives False.

DEPENDS ON   the denial: `OneEssence (Entity.ofAtom n) Entity.ofGround`
GIVES        ⊥ — the denial, refuted
KILLS        [step 8](#step-8) — Verdict Divergence Yields Libertarian Free Choice

PROOF
    Assume OneEssence(Entity.ofAtom n, Entity).ofGround  ← the denial's own thesis
    ⊥

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
SOURCE     ✅ · [DivineClassicalAttributes.lean#atom_grounding_the_ground_yields_contradiction](formal/Logos/DivineClassicalAttributes.lean#L571)

> An entity with no meaning capacity cannot ground one that has: `EntityMeans Entity.ofGround False` against `EntityMeans (ofAtom n) False`.

<a id="r14"></a>
### R14. The ground is a *single* Person

**🧱 BOUNDARY** — “One God = one person, full stop.”

> **COUNTERMODEL · ⇏** — a countermodel **bounds** the reading; it does not contradict it. What follows is the compiled statement, not a `⊥`.

<a id="unicity_does_not_force_unitarian_monad"></a>
DEPENDS ON   — the modelled denial
GIVES        🧱 a bound on the reading, not a death

PROOF
    🧱 COUNTERMODEL — a hostile model, not a proved claim
      1. witness tuple ⟨Unit, fun _ => Bool, (proof of this field, from the next line), fun _ => ⟨true, false, Bool.noConfusion⟩⟩  (existential/conjunction refinement with Unit, fun _ => Bool, (proof of this field, from the next line), fun _ => ⟨true, false, Bool.noConfusion⟩)
      2. ()  (conjunction conjunct 1: ())
      3. fun y => Subsingleton.elim y ()  (conjunction conjunct 2: fun y => Subsingleton.elim y ())
    ∴ ∃ Ground, Persons, (∃ g, ∀ g', g' = g) ∧ (∀ g, ∃ (p1 p2 : Persons g), p1 ≠ p2)

PRICE            🧱 **COUNTERMODEL** — a hostile model, not a price
PRICE            refutes: unicity_does_not_force_unitarian_monad ⇏ Independence
PRICE            0 substantive axioms · `{}`
SOURCE     🧱 unicity_does_not_force_unitarian_monad ⇏ Independence · [DivineClassicalAttributes.lean#unicity_does_not_force_unitarian_monad](formal/Logos/DivineClassicalAttributes.lean#L2224)


> Not entailed **by unicity**: `unicity_does_not_force_unitarian_monad` (`{}`) is a separation model — one ground, and a model in which that ground bears two distinct persons. Unicity alone leaves the person-count open; the positive plural reading at the divine-hypostasis level is C600/C604 (free, PROVEN), while bridge-free Subject plurality is C73 (BLOCKED); and the priced META datum `AxAgapeEssence` (C504) provides the Trinity ([Part IV](#sec-part-iv-the-seam-where-the-deduction-stops)).

<a id="r15"></a>
### R15. Meaning is unrestricted

**🧱 BOUNDARY** — “Whatever means anything is a free subject.”

> **COUNTERMODEL · ⇏** — a countermodel **bounds** the reading; it does not contradict it. What follows is the compiled statement, not a `⊥`.

<a id="unrestricted_meaning_thesis_is_refuted"></a>
DEPENDS ON   — the modelled denial
GIVES        🧱 a bound on the reading, not a death

PROOF
    ⚙️ DERIVATION — 2 compiled steps
      1. assume h  (hypothesis assumption for conditional/reductio proof)
      2. witness components ⟨s, hs, _⟩  (existential elimination from h Entity.ofGround True trivial)
    ∴ ¬(∀ e, p, EntityMeans(e, p) → ∃ s, e = EntityOf(s) ∧ FreeWill(s))

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
SOURCE     ✅ · [BoundedMeaning.lean#unrestricted_meaning_thesis_is_refuted](formal/Logos/BoundedMeaning.lean#L179)


> Not an incoherence to repair, but a thesis that **overclaims**: without the `PassiveIntentionalPotency` guard the antecedent holds of the ground itself (`EntityMeans Entity.ofGround p := True`), and injectivity kills it. What a free subject is required for is therefore **bounded** meaning, not meaning as such (plan step S3, D-3, `Tag: TRANS`). The guarded form is consistent on a signature that *instantiates* signification — `boundedMeaningModel` grants a subject two incompatible contents, so `boundedMeaningRequiresFreeSubject_is_consistent_and_nonVacuous` (`{}`) proves the axiom holds there with the guard's antecedent witnessed, and the consistency is not an artefact of an inert meaning field (`AGENTS.md`, 2026-09-29).

<a id="r16"></a>
### R16. That a free subject exists is unestablished

**🪞 PILLAR RETORSION** — “No one has shown a free subject exists.” **Pillar 4** of the Seven.

> **🪞 INSTANTIATION — not a death** — this row **instantiates** a case rather than refuting anything: the compiled witness below is a world in which the two properties coexist, which is enough to show the objection's inference does not go through. It is not counted as a death, and nothing here says a step is impossible.

<a id="proof_exists_implies_existence_of_free_subject"></a>
DEPENDS ON   — the modelled denial
GIVES        🧱 a bound on the reading, not a death

PROOF
    ⚙️ DERIVATION — discharged directly, with no intermediate step
    Assume ProofExists.{u_s, u_w, u_o} C
    ∴ ∃ s, FreeSubject(C) s

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{choice, propext, sound}`
SOURCE     ✅ · [CompleteLibertarianFreedomArgument.lean#proof_exists_implies_existence_of_free_subject](formal/Logos/CompleteLibertarianFreedomArgument.lean#L2441)


<a id="a_genuine_free_person_exists"></a>
DEPENDS ON   — the modelled denial
GIVES        💰 the objection answered — the claim it doubts obtains, at the price below

PROOF
    💰 PRICED — 3 steps, on a declared axiom
      1. witness components ⟨s, hfw⟩  (existential elimination from a_free_will_exists_derived)
      2. s  (conjunction conjunct 1: s)
      3. freeWill_implies_person s hfw  (conjunction conjunct 2: freeWill_implies_person s hfw)
    ∴ ∃ s, Person(s)

PRICE            ⚠️ **AXIOMATIC (AxActPolarity)** — 2 substantive axioms: AxActPolarity, performative_act_datum · `{AxActPolarity, Initiates, Means, State, Subject, Will, performative_act_datum, subjectWill, will_individuation}`
SOURCE     ⚠️ AxActPolarity · [NoMeanerNoFalsity.lean#a_genuine_free_person_exists](formal/Logos/NoMeanerNoFalsity.lean#L94)


<a id="freeWill_exists"></a>
DEPENDS ON   — the modelled denial
GIVES        💰 the objection answered — the claim it doubts obtains, at the price below

PROOF
    💰 PRICED — 3 steps, on a declared axiom
      1. witness components ⟨s, hPerson⟩  (existential elimination from T5_personExists_from_plurality)
      2. s  (conjunction conjunct 1: s)
      3. hPerson.2.2  (conjunction conjunct 2: hPerson.2.2)
    ∴ ∃ s, FreeWill(s)

PRICE            ⚠️ **AXIOMATIC (AxTwoNecessaryPersonalCentres)** — 1 substantive axiom: AxTwoNecessaryPersonalCentres · `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`
SOURCE     ⚠️ AxTwoNecessaryPersonalCentres · [AsieticChoice.lean#freeWill_exists](formal/Logos/AsieticChoice.lean#L613)


<a id="epistemic_order_makes_the_act_datum_necessary"></a>
DEPENDS ON   — the modelled denial
GIVES        🧱 a bound on the reading, not a death

PROOF
    ⚙️ DERIVATION — 4 compiled steps
    Assume ∃ s, p, ClaimsNormativeCorrectness(s, p)
      1. witness components ⟨s, p, hClaims⟩  (existential elimination from h)
      2. s  (conjunction conjunct 1: s)
      3. p  (conjunction conjunct 2: p)
      4. claims_normative_correctness_is_act s p hClaims  (conjunction conjunct 3: claims_normative_correctness_is_act s p hClaims)
    ∴ ∃ s, p, Act s p

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, State, Subject}`
SOURCE     ✅ · [EpistemicNecessity.lean#epistemic_order_makes_the_act_datum_necessary](formal/Logos/EpistemicNecessity.lean#L235)


> CLEARER.md §8. The objection doubts the existence of a free subject. Pillar 4 of the Seven. The objection is answered conclusively with 0 substantive axioms by the master proof of the Free Subject (`proof_exists_implies_existence_of_free_subject`), demonstrating that the concrete occurrence of this proof instance strictly derives the existence of an anonymous Free Subject.

<a id="r17"></a>
### R17. The critic who presents the objection is himself a person

**🪞 PILLAR RETORSION** — “This objection is a sound argument, so it carries no personal stance.” **Pillar 7** of the Seven.

<a id="critic_presenting_objection_is_person"></a>
**🪞 INSTANTIATION — not a death** — An adversarial critic who presents an objection argumentatively as sound themselves instantiates the normative stance and is therefore a Free Person.

DEPENDS ON   the denial: `PresentsAsSound critic objection`
GIVES        🪞 the critic is an instance of the person — not a death

PROOF
    Assume Derivation
    Assume PresentsAsSound(critic, objection)  ← the denial's own thesis
      1. hRes.2.2.2.2  (conjunction conjunct 1: hRes.2.2.2.2)
      2. hRes.2.2.1  (conjunction conjunct 2: hRes.2.2.1)
    Person(critic) ∧ FreeWill(critic)  — the objection, made by a critic, is an instance of the person; nothing is refuted

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, State, Subject, Will, choice, propext, sound, subjectWill, will_individuation}`
SOURCE     ✅ · [ProofPresentationRetorsion.lean#critic_presenting_objection_is_person](formal/Logos/ProofPresentationRetorsion.lean#L206)

> Pillar 7. The kernel anchor is `ProofPresentationRetorsion.lean:206`; the footprint is free, so the critic's own stance is derived at the same price as every other entry here.

<a id="r18"></a>
### R18. A Single Person could only give to contingent beings, so its self-giving would depend on them

**💥 DERIVATION** — “If the Ground were one Person, it could only give to contingent (temporal) beings — so its self-giving would depend on them, and it would thereby become contingent too.”

<a id="self_gift_cannot_depend_on_a_contingent_person"></a>
**⊥ CONTRADICTION** — **Step 3 — the dependence — is refuted (C579, PROVEN, free).** This is the row the objection dies on. The claim was: *a Single Person can only give to contingent beings, so its self-giving is dependent on the contingent beings.* The hypothesis is that claim…

DEPENDS ON   the denial: `∃ f, o, ∃ s, SelfDonation(f, o) ∧ o.deiformEntity = EntityOf(s)`
GIVES        ⊥ — the denial, refuted
KILLS        [step 8](#step-8) — Verdict Divergence Yields Libertarian Free Choice

PROOF
    Assume ∃ f, o, ∃ s, SelfDonation(f, o) ∧ o.deiformEntity = EntityOf(s)  ← the denial's own thesis
      1. witness components ⟨_f, o, s, hSD, hEq⟩  (existential elimination from dependence)
      2. witness components ⟨_hne, _hf, ho, _hlove, _hloc⟩  (existential elimination from hSD)
    ⊥

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Subject}`
SOURCE     ✅ · [DivineTrinitarianAttributes.lean#self_gift_cannot_depend_on_a_contingent_person](formal/Logos/DivineTrinitarianAttributes.lean#L3611)

> **The hinge, and the row the previous batch never had.** The objection is a four-step chain — (1) one Person, (2) therefore only contingent recipients, (3) therefore the self-giving *depends on* the contingent, (4) therefore contingent — against a Ground already determined Eternal, Necessary, Free and Immutable. **Step 3 is where it dies**, and it dies free: `SelfDonation` puts the recipient at `divineReality := Entity.ofGround`, so no `Subject` can be the recipient of a donation.

> The hypothesis here is that dependence as a proposition and the compiled derivation is C579 (`{Subject}`), whose primary is the premise step itself (`single_person_denial_is_refuted`, also `{Subject}`): assume the author's step 1 and `False` follows, because `Entity.ofGround` is no `Subject`'s entity. **No `AxAgapeEssence` appears on this row.** The donation's *existence* is priced on its own row below and is deliberately not used to refute an objection that grants it; a row that refuted the objection by way of the datum it also prices would be the datum. What the free rows say is that the gift's terminus is the necessary ground (`donation_terminus_is_as_necessary_as_the_donor`, `{NecessarySubjectKind, Subject}`), so the contingency conclusion has no premise (`donation_makes_contingency_is_refuted`).

> “It cannot be only one” is a *separate* paid row — `Plurality.notAlone` (T12) costs `AxTwoSubjects` — and is not folded into this row's price. The terminology the earlier batch collapsed is restored here: the ground **is personal** (C362, `PersonalGround`, whose `indwells` is `OneEssence` for *every* `Subject`), it **is** the nature those Persons are OneEssence in, and it is **no Person among them** (C519). “The ground is not a person” is the third of those, not a denial of the first. Moreover, whether the ground requires more than one person is settled at each sort in [Part IV's necessary-persons table](#sec-necessary-persons-the-count-at-each-sort).

<a id="r19"></a>
### R19. Denying the donation of the Self

**💥 DERIVATION** — “So the Ground does not donate the Self to itself.”

<a id="denying_self_donation_is_absurd"></a>
**⚠️ PRICED — the denial refuted, at a declared price** — **Denying that the donation of the Self occurs is a declared, not derived, absurdity (C576, PROVEN↑).** Read the claim narrowly: assume there is *no* donation at all and `False` follows.

DEPENDS ON   the denial: `¬∃ f, o, SelfDonation(f, o)`
GIVES        the denial is refuted, at the price named below
KILLS        [step 8](#step-8) — Verdict Divergence Yields Libertarian Free Choice

PROOF
    Assume ¬∃ f, o, SelfDonation(f, o)  ← the denial's own thesis
    False  — refuted, at the declared price on the PRICE line

PRICE            ⚠️ **AXIOMATIC (AxAgapeEssence)** — 1 substantive axiom: AxAgapeEssence · `{AxAgapeEssence, Subject, choice}`
SOURCE     ⚠️ AxAgapeEssence · [DivineTrinitarianAttributes.lean#denying_self_donation_is_absurd](formal/Logos/DivineTrinitarianAttributes.lean#L2326)

> The denial is a **real premise** of the compiled theorem — `denying_self_donation_is_absurd`, C576 — which is what makes this row a derivation and not a badge asserted over it. **Its kind is `⚠️ PRICED`, not `⊥ CONTRADICTION`, and the difference is not cosmetic.** `AxAgapeEssence` is priced, so a world exists in which the denial holds (the Narcissus world, C511, where the source loves only itself): the denial is *available* and is contradicted only by what is **declared**. Γ does not claim the donation is a theorem of logic. This row is mounted for that reason and not as the answer to the author — the answer is the free row above, which does not mention the donation.

<a id="r20"></a>
### R20. A self-gift is impossible because the donor and the recipient are two things

**💥 DERIVATION** — “A gift of the Self is a category mistake: it needs two relata, and two relata cannot be one thing.”

> **⊘ DENIAL REFUTED** — the objection is **refuted**, not merely bounded: the block below is the compiled derivation, and its terminator is derived from the audited goal. The price, if any, is named on its own PRICE line.

<a id="denying_shared_location_is_absurd"></a>
DEPENDS ON   — the modelled denial
GIVES        💰 a priced result — the objection dies, and the price is named
KILLS        [step 8](#step-8) — Verdict Divergence Yields Libertarian Free Choice

PROOF
    💰 PRICED — one step, a projection
      1. witness components ⟨f, o, _, hf, ho, hlove, hloc⟩  (existential elimination from agape_is_self_donation)
    ∴ ¬∀ f, o, Subsists(f) → Subsists(o) → DivineLove f o → f.deiformEntity ≠ o.deiformEntity

PRICE            ⚠️ **AXIOMATIC (AxAgapeEssence)** — 1 substantive axiom: AxAgapeEssence · `{AxAgapeEssence, Subject, choice}`
SOURCE     ⚠️ AxAgapeEssence · [DivineTrinitarianAttributes.lean#denying_shared_location_is_absurd](formal/Logos/DivineTrinitarianAttributes.lean#L2337)


<a id="two_subsisting_share_one_location"></a>
DEPENDS ON   — the modelled denial
GIVES        🧱 a bound on the reading, not a death
KILLS        [step 8](#step-8) — Verdict Divergence Yields Libertarian Free Choice

PROOF
    ⚙️ DERIVATION — discharged directly, with no intermediate step
    Assume DivineHypostasis
    Assume Subsists(f)
    Assume Subsists(o)
    ∴ f.deiformEntity = o.deiformEntity

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Subject}`
SOURCE     ✅ · [DivineTrinitarianAttributes.lean#two_subsisting_share_one_location](formal/Logos/DivineTrinitarianAttributes.lean#L1878)


> The stronger form, and the part that costs nothing extra: grant a donor and a recipient, grant that both subsist, grant that the love holds — and the denial *still* has to deny that they share one location-entity, which is `{}`. So the two-relata objection is refuted by arithmetic, not by a purchase. Same footprint as the row above ({Subject, AxAgapeEssence, Classical.choice}, one META): the price buys the gift, and the gift is not two things. This row has no thesis premise to label because the theorem's whole conclusion is the denial — so it prints the compiled statement and the derived kind rather than transcribing one.

<a id="r21"></a>
### R21. The Ground cannot give at all, because it is not a person who chooses

**💥 DERIVATION** — “Only a chooser gives. The Ground is not a chooser, so the donation is empty.”

> **⚠️ PRICED — the objection answered, at a price** — the objection is **answered**, not merely bounded: the claim it doubts obtains, and the price of that is named below. This row is a **result at a price**, not a gap in the deduction.

<a id="self_donation_needs_no_personhood_of_the_ground"></a>
DEPENDS ON   — the modelled denial
GIVES        💰 the objection answered — the claim it doubts obtains, at the price below
KILLS        [step 8](#step-8) — Verdict Divergence Yields Libertarian Free Choice

PROOF
    💰 PRICED — one step, a constructor
      1. constructor  (conjunction constructor introduction)
    ∴ ¬Asiety(Entity).ofGround ∧ (∃ f, o, SelfDonation(f, o))

PRICE            ⚠️ **AXIOMATIC (AxAgapeEssence)** — 1 substantive axiom: AxAgapeEssence · `{AxAgapeEssence, Means, Subject, choice}`
SOURCE     ⚠️ AxAgapeEssence · [DivineTrinitarianAttributes.lean#self_donation_needs_no_personhood_of_the_ground](formal/Logos/DivineTrinitarianAttributes.lean#L2797)


<a id="ground_is_not_a_fourth_chooser"></a>
DEPENDS ON   — the modelled denial
GIVES        🤝 the objection's premise is **granted** — 0 substantive axioms. This is the limit of the row, not an answer to it

PROOF
    ⚙️ DERIVATION — 2 compiled steps
      1. assume h  (hypothesis assumption for conditional/reductio proof)
      2. witness components ⟨s, _p, _q, hs, _⟩  (existential elimination from h)
    ∴ ¬Asiety(Entity).ofGround

PRICE            ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
SOURCE     ✅ · [DivineTrinitarianAttributes.lean#ground_is_not_a_fourth_chooser](formal/Logos/DivineTrinitarianAttributes.lean#L2759)


<a id="agape_is_self_donation"></a>
DEPENDS ON   — the modelled denial
GIVES        💰 the objection answered — the claim it doubts obtains, at the price below

PROOF
    💰 PRICED — one step, a constructor
      1. constructor  (existential constructor introduction)
    ∴ ∃ f, o, SelfDonation(f, o)

PRICE            ⚠️ **AXIOMATIC (AxAgapeEssence)** — 1 substantive axiom: AxAgapeEssence · `{AxAgapeEssence, Subject, choice}`
SOURCE     ⚠️ AxAgapeEssence · [DivineTrinitarianAttributes.lean#agape_is_self_donation](formal/Logos/DivineTrinitarianAttributes.lean#L2290)


> **The row that restores what a laundering sentence had removed.** The corpus answered this with a label — “the one essence is not a fourth chooser; its freedom is their freedom, shared rather than duplicated” — and commit `4a59173` then claimed the label was an absent predicate presented as an argument, deleted the ground’s freedom from the doctrine, and rebuilt the reading on that. The predicate is **not** absent: `AsietyFreedom.asietyFreedomOfGround` (`AsietyFreedom.lean:141`) is the ◈ `def` that states the sharing, `asietyFreedom_summary` (`:357`) consumes it, and three docstrings in that module say the vacuity of `OneEssence` is *load-bearing* because it marks the ground’s freedom as **transferred** rather than **exercised**.

> A `def` premise is invisible to `#print axioms`, and from that invisibility the commit inferred that nothing was there. `LOVE-2.md` D1 withdraws that inference. So this row is a **conjunction, both halves machine-checked**, plus a granted premise: the ground is **not** a fourth chooser (free at `{Means, Subject}`, and marked role=premise — it is the *objection’s* premise, so it is printed as granted and kills nothing), **and** the donation of the Self stands anyway (C575, one META axiom). What the price buys is the gift and nothing more: it does not buy a fourth chooser, while the ground's personhood is confirmed by C228 and C590 without making the ground a fourth chooser. The ground **is** personal — C362, C140 — and `¬ Asiety Entity.ofGround` is `ofGround_ne_ofSubject`, i.e. C519: the nature is not one of its instances.

<a id="sec-part-iv-the-seam-where-the-deduction-stops"></a>
## Part IV — the seam: where the deduction stops

The primary proof of a Free Subject is the concrete, instantiated well-foundedness argument (`complete_libertarian_freedom_argument`, `proof_exists_implies_existence_of_free_subject`).

The older Right/Wrong → Meaning route was demoted because it could leave open an instantiation/vacuity problem; the previous deontic route is kept whole in [the ledger](investigations/ledger.md).

The personal grounding of Right/Wrong (C228) remains a distinct, parallel established result. The seam is where the formal deduction stops and unproved extensions begin; three lines carry it in GAPMAP.

**C228 — personhood of the ground, confirmed at two anchors: PROVEN.**

`normative_ground_is_personal (g) (hGr : GenericGroundsRightWrong g) : PersonCorrelate g` is proved (0 substantive axioms) alongside `TrinitarianPersonalGround.the_ground_is_not_void_of_personhood` (`PersonalGround Entity.ofGround`).

Personhood in Γ is a three-step field projection through D1′: `grounds_normativity` gives the `GenericGroundingRelation`, `explanatory` forces `g = EntityOf s`, `personal_ground` gives `Person s`.

Coexistence with C564 (`¬ PersonCorrelate Entity.ofGround`) is machine-checked by C591 (`¬ GenericGroundsRightWrong Entity.ofGround`), and `PersonalGround` is distinct from `PersonCorrelate`.

**What remains open is hypostasis and Subject person-count, not personhood.** Whether the ground is *one* person is answered by `unicity_does_not_force_unitarian_monad` (R14): unicity leaves person-count open.

The positive plural result at the divine-hypostasis level is C600/C604 (PROVEN, free); bridge-free Subject plurality is C73 (BLOCKED).

**C110 — a necessary ground does not entail contingent creation: countermodel, `{}`.** `¬ (∀ Subj Ent World, GroundEntailsCreation Subj Ent World)` — nothing in the deduction produces a world or a creation event.

**C112 — the preceding theory does not entail the incarnation: countermodel, `{}`.** Nothing in the deduction requires the ground to enter a body.

**C109 — preceding theory ⇏ Trinity: DEMOTED.** Its `Bool` countermodel is a truncated signature — an artifact, not evidence about Γ. Not superseded by `monotheism_compatible_with_trinity`, which is not a kernel declaration. Γ omits the Trinity because hypostasis→subject is unasserted.

The 31 formal frontiers — every unproved step, every countermodel separation, every open bridge, each with its exact missing lemma — are in [the ledger](investigations/ledger.md). Nothing there is established.

| Claim | Derived status | What it settles |
|---|---|---|
| `C228` | ✅ **PROVEN** · [PersonalNormativeGround.lean#normative_ground_is_personal](formal/Logos/PersonalNormativeGround.lean#L261), footprint {Means, Subject, Will, subjectWill} | PROVEN (0 substantive axioms, C228): any entity that grounds Right/Wrong is a Personal Entity — the personalness is a THREE-STEP FIELD PROJECTION: `grounds_normativity` supplies the `GenericGroundingRelation` […] |
| `C110` | 🧱 **COUNTERMODEL** · [ConditionalTheology.lean#necessary_ground_not_entails_contingent_creation](formal/Logos/ConditionalTheology.lean#L616), footprint {} | **Separation Model (rebuilt on a populated world).** A necessary divine ground exists, grounds every content, and coexists with a contingent subject that is not *its* creation: necessary reality does NOT entail creation. |
| `C112` | 🧱 **COUNTERMODEL** · [ConditionalTheology.lean#preceding_theory_not_entails_incarnation](formal/Logos/ConditionalTheology.lean#L380), footprint {} | Unincarnate Hostile Model: The existing theory (necessary divine ground, human agency, free will) is completely consistent with God remaining purely transcendent and unincarnate. |
| `C109` | DEMOTED **DEMOTED** · [ConditionalTheology.lean#preceding_theory_not_entails_trinity](formal/Logos/ConditionalTheology.lean#L336), footprint {} | Binitarian Separation Model (Toy Cardinality Model over Bool): Demonstrates that an unconstrained 2-element domain (`Subj := Bool`) cannot accommodate three distinct personal centers by pure cardinality (Pigeonhole […] |

<a id="sec-necessary-persons-the-count-at-each-sort"></a>
### Necessary persons: the count, at each sort

Whether the ground requires more than one person is settled conditionally or by sort:

| Object / Level | Syntactic sort | Derived status & anchor | Ontological content & price |
|---|---|---|---|
| **Divine Persons** | `DivineHypostasis` | ✅ **PROVEN** · 0 substantive axioms · [DivineAgape.another_divine_person_is_necessary](formal/Logos/DivineTrinitarianAttributes.lean#L2225) | Two distinct necessary divine Persons exist in the divine reality (`C600` / `C604`). |
| **Foundational unicity** | `Entity` · boundary | 🧱 **COUNTERMODEL** · `{}` · [FoundationalUnicity.unicity_does_not_force_unitarian_monad](formal/Logos/FoundationalUnicity.lean#L201) | Unicity entrains neither one nor many: `unicity_does_not_force_unitarian_monad` (`C212` / `R14`). |
| **Bridge-free plural subjects** | `Subject` · unproved | ✖ **BLOCKED** | Plurality of `Subject` without a bridge is underivable (`C73`, in ledger). |
| **Plurality bridge** | `Subject` · priced | ⚠️ **AXIOMATIC (AxTwoNecessaryPersonalCentres)** · 1 substantive axiom | Subject-level `Plurality.two_necessary_persons` (`C585`, 1 META) is in the ledger, not the reading path. |

One pointer line: the Subject-level result `Plurality.two_necessary_persons` (C585, 1 META) is in the ledger, not the reading path.

<a id="sec-what-the-instrument-cannot-see"></a>
### What the Instrument Cannot See

`#print axioms` reads the kernel's dependency graph. It cannot see a **`def` used as a premise by name** — so the census below counts every such inherited bridge, the theorems it underwrites, and how many have been reviewed.

A `✅` therefore means *kernel-verified conditional on a bridge the kernel does not charge*.

This is disclosure, not payment: nothing is promoted to a declared axiom, and the three-way decision (promote / declare / retire) is still open.

`EntityMeans Entity.ofGround := True` — the irrelevance of causal contact to [Part I](#sec-part-i-the-deduction) — is tracked by the separate, machine-audited `Stipulations.lean` registry (`scripts/audit_stipulations.py`), not by the 28-entry allowlist above.

| Declared-`def` bridges | Theorems they underwrite | Reviewed | Promoted to a declared axiom |
|---|---|---|---|
| **28** | **53** (largest: 7) | **0** | **0** |

Full census with each bridge, its dependents and its justification: [investigations/ledger.md](investigations/ledger.md); the open three-way decision is tracked by `scripts/census_stipulated_defs.py`.

<a id="sec-what-is-not-established"></a>
### What Is Not Established

**Monotheism — one God — is not on this list, because it is PROVEN** ([the Trinity table](#sec-one-god-in-three-persons)): C320 proves one universal modal ground exists, C440 one nature.

The *person-count* of that one God is a different, unsettled question: C212 shows unicity does not entail a single Person.

The positive plural reading is priced, not free: the declared META datum `AxAgapeEssence` (C504) → C510 ([the Trinity table](#sec-one-god-in-three-persons)).

Personhood of the ground is confirmed under both anchors (C228, PROVEN; PersonalGround in C590), while hypostatic identity and person-count remain open.

One instantiation is settled: for `g := Entity.ofGround`, `ofGround_not_a_person_correlate` (C564) proves `¬ PersonCorrelate Entity.ofGround` outright — the ground is personal (indwelt by the three Persons), but is not an individual Person-correlate or fourth chooser (C591).

**Trinity is priced, not free** ([the Trinity table](#sec-one-god-in-three-persons)): three Persons on three declared META premises, with C109 at `{}`. **Incarnation is open** (C112, `{}`).

**The three divine Persons' semantic fullness is affirmed** — `NecessaryKindAudit.necessary_kind_subject_has_maximal_capacity`, priced at `DivinePersonsTotalMeaning` (META), while creaturely finitude is restricted to contingent subjects (`SemanticFinitude`, VOCAB).

**The Incarnation is the open frontier.** C112 (`preceding_theory_not_entails_incarnation`, `{}`): the preceding theory is consistent with an unincarnate ground. C111 shows the *structure* is available; the *entailment* is not.

Contingent creation *as existence* is a free theorem (C350, `{}`); only the realm's content is priced (C367). Nothing above should be read as claiming any of it.

| Claim | Derived status | What it settles |
|---|---|---|
| `C109` | DEMOTED **DEMOTED** · [ConditionalTheology.lean#preceding_theory_not_entails_trinity](formal/Logos/ConditionalTheology.lean#L336), footprint {} | Binitarian Separation Model (Toy Cardinality Model over Bool): Demonstrates that an unconstrained 2-element domain (`Subj := Bool`) cannot accommodate three distinct personal centers by pure cardinality (Pigeonhole […] |
| `C112` | 🧱 **COUNTERMODEL** · [ConditionalTheology.lean#preceding_theory_not_entails_incarnation](formal/Logos/ConditionalTheology.lean#L380), footprint {} | Unincarnate Hostile Model: The existing theory (necessary divine ground, human agency, free will) is completely consistent with God remaining purely transcendent and unincarnate. |
| `C151` | ✅ **PROVEN** · [PersonalGroundOfReality.lean#the_person_supports_the_reality_of_right](formal/Logos/PersonalGroundOfReality.lean#L153), footprint {Initiates, Means, State, Subject, Will, subjectWill, will_individuation, CL} | HEADLINE — THE PERSON SUPPORTS THE REALITY OF RIGHT. |
| `C228` | ✅ **PROVEN** · [PersonalNormativeGround.lean#normative_ground_is_personal](formal/Logos/PersonalNormativeGround.lean#L261), footprint {Means, Subject, Will, subjectWill} | PROVEN (0 substantive axioms, C228): any entity that grounds Right/Wrong is a Personal Entity — the personalness is a THREE-STEP FIELD PROJECTION: `grounds_normativity` supplies the `GenericGroundingRelation` […] |
| `C320` | ✅ **PROVEN** · [DivineClassicalAttributes.lean#exactly_one_universal_modal_ground](formal/Logos/DivineClassicalAttributes.lean#L2196), footprint {Means, NecessarySubjectKind, Subject} | Master Synthesis (existential form): exactly one universal modal ground exists. |
| `C350` | ✅ **PROVEN** · [DivineClassicalAttributes.lean#contingent_realm_obtains](formal/Logos/DivineClassicalAttributes.lean#L4280), footprint {NecessarySubjectKind, Subject, CL} | Contingency-overflow: something obtains, is modal-fragile, and is not the necessary ground — and Γ derives it outright, resting on nothing substantive. |
| `C367` | ✅ **PROVEN** · [DivineClassicalAttributes.lean#cosmos_obtains](formal/Logos/DivineClassicalAttributes.lean#L4427), footprint {Means, NecessarySubjectKind, Subject, Will, subjectWill, CL} | **The cosmos exists** — a contingent created realm, not the necessary ground, actually obtains and bears content of its own — given a *contingent* person. |
| `C440` | ✅ **PROVEN** · [DivineClassicalAttributes.lean#divine_simplicity_sole_bearer](formal/Logos/DivineClassicalAttributes.lean#L900), footprint {Means, Subject, CL} | C440 — the attributes-table form: the ground is the sole bearer of Divine Simplicity, stated together with the existence half so a reader-facing row can cite a single declaration. |
| `C510` | ⚠️ **AXIOMATIC** — rests on `AxAgapeEssence`, `AxProcessionSpirit`, `AxProcessionWord` · [DivineTrinitarianAttributes.lean#agape_entails_tripersonality](formal/Logos/DivineTrinitarianAttributes.lean#L2158), footprint {AxAgapeEssence, AxProcessionSpirit, AxProcessionWord, Subject, CL} | Agape entails tripersonality (C510, PROVEN↑): under the three disclosed Agape axioms — the datum, the procession of the Word, the procession of the Spirit — there is a `TrinitarianStructure` (C108) on the divine […] |

## The score: what Γ has won, and what is still open

Every figure in this table is **derived from the Lean kernel** at generation
time — each badge from (node kind, audited `#print axioms` footprint, declared
axiom `Tag:`), never transcribed. The same computation prints the audit counters
in [`investigations/kernel-audit.md`](../investigations/kernel-audit.md); the two
cannot disagree, because both read the one derived table. A claim's status here
is exactly its status in the ledger — this block only counts, and the columns
below are built by joining those counts, not by judgement.

**One thing these figures do not cover.** The axiom-free counts below are
footprints from `#print axioms`, which cannot see a **`def` used as a premise**
by name. There are **28** such inherited bridges, carrying
**53** theorems (the largest underwrites 7). They are
now enumerated in the ledger's `def`-as-bridge section, which is *disclosure*,
not payment: **0** have been reviewed and **0** have been promoted
to a declared axiom. So a ✅ badge means the theorem is kernel-verified *conditional
on a bridge the kernel does not charge*. Full census and the open three-way
decision: `scripts/census_stipulated_defs.py`.

| **Won** | **Still open** |
|---|---|
| **453 affirmative claims derived** out of **595** ledger claims — 350 ✅ kernel-verified, 103 ⚠️ derived under a substantive (`SEM`/`META`) axiom, each ⚠️ row naming the bridge it rests on. | **12 blocked** ✖ — named individually |
| **61 countermodel boundaries** 🧱 — a hostile model in which the claim *fails*. These are won results about the limit of the theory, not gaps. | &nbsp;&nbsp;· **C462** — BLOCKED, with no declaration, and deliberately so: the ground does not initiate is not refutable in Gamma and is not evidence of non-agency either |
| **1020 of 1939 theorems in `formal/Logos/` rest on no Γ axiom at all** (53%) — counted from `formal/axiom_audit.json`, not claimed. | &nbsp;&nbsp;· **C503** — A love-lane step for deriving the Good from a second person is BLOCKED, with no declaration (lote OTHER, 2026-09-29; plan OTHER.md): the step 'the… |
| **The whole price is 40 declared axioms**: 18 are `VOCAB` (the vocabulary the statements need in order to be sayable) and 22 are substantive. Only the 22 are philosophical commitments; the rest are the theory's definitions of its own words, which is a different thing from a premise. | &nbsp;&nbsp;· **C73** — Plurality without bridges is blocked: unit countermodel settles that 1 act does not entail plurality; requires AxTwoNecessaryPersonalCentres |
| **10 attribute corollaries became unconditional theorems** (C389–C398) — they were conditional on a `def` until F15 was declared, so this is a *strengthening*: fewer hidden premises, same conclusions. | &nbsp;&nbsp;· **C75** — Propositional personhood is blocked: content existence does not entail personhood |
|  | &nbsp;&nbsp;· **C79** — Ultimate ground existence is blocked: infinite descending chains have no ultimate element without a well-foundedness axiom |
|  | &nbsp;&nbsp;· **C89** — Ultimate ground by initiation is blocked: non-entailed without well-foundedness |
|  | &nbsp;&nbsp;· **C90** — Personal ultimate ground is blocked: ultimate grounding does not entail personal nature |
|  | &nbsp;&nbsp;· **F12** — The justification for the ASIETY-FREEDOM stipulation is BLOCKED, in two halves that must both be closed |
|  | &nbsp;&nbsp;· **F13** — The Creator-sharing existence claim is BLOCKED, and refuted as derivable rather than open |
|  | &nbsp;&nbsp;· **F14** — Axiomatic diagonal specification for self-referential entertainment |
|  | &nbsp;&nbsp;· **F16** — Divine Immutability - the substantive reading of capacity invariance, that a subject's meaning capacity is constant ACROSS WORLDS - is BLOCKED, and… |
|  | &nbsp;&nbsp;· **OpenBridgeNormativity** — The positive bivalence→normativity bridge (∀ s p, Judge s p → GenuineNormativity s p (¬p), or stand-antecedent variant) is BLOCKED: bivalence alone… |
|  | **3 deferred** ➖ — named individually |
|  | &nbsp;&nbsp;· **C77** — Conditional necessary-person claim is deferred: the theorem Love.necessaryPersonExists_conditional was removed from the live kernel (commit ae7f4bd)… |
|  | &nbsp;&nbsp;· **C92** — Conditional necessary-entity claim is deferred: the theorem Love.necessary_entity_exists_conditional was removed from the live kernel (commit… |
|  | &nbsp;&nbsp;· **F2** — Deontic teleology is deferred: how norms point at goals is not yet derived |
|  | **15 retired routes** — settled *negatively*, not pending: each step was destroyed by a hostile model, so the question is closed against it (see *Appendix C*): `C64`, `C65`, `C66`, `C67`, `C69`, `C70`, `C71`, `C72`, `C76`, `C78`, `C80`, `C81`, `C82`, `C87`, `C88` |

**Read the two columns together and the shape is precise: Γ won the metaphysics
of the ground and lost the soteriology.** Established, as two separate objects,
never merged: genuine normativity has a personal ground (a `Subject` satisfying
`Person`) — and Γ's distinct metaphysical ground of reality, `Entity.ofGround`, is
unique and necessary, and possesses canonical aseity, simplicity, and pure
actuality. The two are kept apart on purpose: `Entity.ofGround` is itself provably
**not** an individual person-correlate (C564, `ofGround_not_a_person_correlate`; the
ground is personal as the Godhead, but not a fourth Person or fourth chooser), so a reader
who takes "the ground" above to be the same object both times already has the
wrong reading. The personhood of the ground is confirmed (C228 PROVEN, and C590
`PersonalGround`), without collapsing into a fourth chooser. What is *not* free: the three divine
Persons of the Trinity (three declared META premises, C510), and what is still
open: the Incarnation, contingent creation as such, and hypostasis. A *single-person*
reading of the personal ground is not entailed by
unicity: `unicity_does_not_force_unitarian_monad` ({}) is a separation model, so
unicity leaves the person-count open. The positive plural result at the divine-hypostasis
level is C600/C604 (PROVEN, free); bridge-free Subject plurality is C73 (BLOCKED).
Each open row is named above with its missing lemma rather than absorbed into an average,
and the left column is larger because the ground-theory was proved, not because the
open rows were rounded down.

Four qualifications, stated rather than hidden:

1. **A ✅ means "kernel-verified on declared vocabulary", not "free of metaphysical assumption".** The vocabulary axioms are real axioms; they are merely the ones the statements need in order to be said at all. The substantive ones are the 22 `SEM`/`META` bridges.
2. **The 40 declared axioms are inputs, not wins.** Counting them as results would be the same error as counting a hypothesis as a proof. They are listed so the reader can price Γ exactly, and `VOCAB` is separated from `SEM`/`META` because only the latter are commitments.
3. **A 🧱 is a win about a boundary, not about the claim.** Γ building a model in which monotheism fails is a real theorem — and a theorem *against* monotheism. The columns keep those apart on purpose.
4. **The 15 retired routes are counted as neither won nor open.** Their ledger notes say the step was destroyed under hostile semantics; that is a settled negative. Filing them under "still open" would overstate the debt, and filing them as won would overstate the theory, so they get their own line.

<a id="sec-where-the-rest-of-the-ledger-lives"></a>
## Where the Rest of the Ledger Lives

| What was moved out of the reading path | Where it lives |
|---|---|
| Every natural-deduction proof (40 blocks), the 14 step-by-step chain blocks (206 rows) — including the **Adversarial Denial Normal Forms (D1–D8)**, the exhaustive proof of inevitability that the chain diagram abbreviates — the 39 classical-attribute rows with full prose, the ASCII flowchart, and the full per-step prose | [investigations/ledger.md](investigations/ledger.md) |
| 100 retorsion theorems, the independence-frontier catalogue, the countermodel catalogue and the investigation index | [investigations/catalogues.md](investigations/catalogues.md) |
| The complete kernel audit, the axiom inventory (all 40, with tags and dependents), the dependency ledger, the consistency checks and the code annex | [investigations/kernel-audit.md](investigations/kernel-audit.md) |

Generated, not editorial: one pass over the kernel emits both files, and the superset check fails the build if anything is missing from their union. Plan of record: [READINGPATH.md](READINGPATH.md).
