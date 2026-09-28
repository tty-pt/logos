# Γ — The Deduction

> **Γ is a machine-checked deduction**: genuine normativity — an objective right/wrong
> binding our judgments — forces a *personal* ground. Free will is *derived, never
> assumed* (`GenuineNormativity ⇒ Chooses ⇒ FreeWill ⇒ FreeSubject ⇒ Person`);
> wherever right/wrong is real, its ground-type is personal (`RightWrong ⇒ Person`).
> A necessary Divine Being/Ground is **proven** (✅): it exists unconditionally as the sole
> universal modal grounding ground (`ofGround_universal_modal_ground` C319,
> `exactly_one_universal_modal_ground` C320) and possesses Canonical Aseity
> (`conditional_canonical_aseity`). A **necessary Person** is likewise derived (⚠️) on the
> single declared `META` bridge `necessaryPersonalSubjectExists` (C404 → Claim D, C409).
> What is **not** established is monotheism *at the level of the Person*: C212 proves
> ground-unicity does not force a unitary monad, and the personal-identification bridge C228
> remains `BLOCKED`. Every other claim is definitional, derived, or a declared axiom.

Every section below answers the same question — *what is the status of this claim?*

> **The Dialectical Inevitability Architecture** — Why every rational attack fails:
> 1. **Performative Retorsion (The Trap):** Any attempt to deny objective correctness must claim that its denial is *correct* (`ClaimsCorrect s NoRight`). In the Lean kernel, claiming denial as correct while true yields a direct constructive contradiction (`claims_correct_no_right_self_refuting` → ⊥, 0 substantive axioms). The skeptic cannot even enter the debate without triggering the normative partition.
> 2. **Constitutive Semantics (The Deduction):** Rational address between incompatible alternatives is *definitionally* Choice (`Chooses`), having choice is *definitionally* Free Will (`FreeWill`), and a free choosing subject is a Person in the classical Boethian-Thomistic sense by priced theorem (`freeWill_implies_person`, 0 substantive axioms, via the declared law `will_individuation`).
> 3. **Airtight Epistemic Boundaries:** Where logic ends, Γ never fakes a proof. Unproved theological extensions (Trinity, Creation, Incarnation, Monotheism) are isolated by machine-checked mathematical countermodels (`⇏`).

**Two directions, not one.** The chart distinguishes *epistemic discovery* (▲ — what
the argument must prove upward: no free subject precedes free will) from *ontological
grounding* (▼ — what the established order then entails downward: a personal free
agency grounds Right/Wrong). The kernel proves the one dependence
`RightWrong ⇒ Person`; the downward `▼` ontological-grounding arrow is the
interpretive reading of that same proved subjunction, not an additional theorem —
the direction is not machine-decidable.

> **What this proof does and does not show**
>
> 1. The machine-verified chain above — established **under** the
>    normative-judicative stance via two mutually reinforcing routes (0 substantive axioms):
>    • **Route A (Performative Datum):** Rational judgment presupposes correctness (`ClaimsNormativeCorrectness s p`).
>    • **Route B (Proof Presentation):** Presenting or evaluating Γ argumentatively instantiates the stance (`PresentsAsSound s d`), deriving Free Will and Personhood (`ProofPresentationRetorsion.lean`). Even an adversarial attack on Γ instantiates personhood (`critic_presenting_objection_is_person`).
>    Zero-input free will from bare syntax is rejected: `M_inanimate_checker` verifies syntax with 0 subjects.
> 2. That same dependence — *wherever the normative order is real, its ground-type
>    is personal* — is machine-proved with 0 substantive axioms. Reading the
>    subjunction as a direction of ontology is interpretive, as 'Two directions, not
>    one.' above explains.
> 3. Divine Personhood and Strict Monotheism — **DEFERRED** (⏸), not proved here; a necessary
>    Divine Being/Ground (world-rigid, everlasting, atemporal) is its entity-level **PROVEN** claim (✅).
> 4. Moral good/evil — machine-separated from epistemic normativity (permanent 
>    countermodel frontier 🧱, C175): the faithful model `M_amoral` satisfies the whole epistemic 
>    agential reality-hook with zero practical obligation. The positive pole is then obtained 
>    honestly: `Good` is a *fair definition* (helping another person, vocabulary-only, 
>    `{Means, Subject}`) and `moral_good_obtains` (C178) is PROVEN↑ under the single declared 
>    META bridge `AxBenevolentBearingObtains` (C177, "some person is actually helped"), whose 
>    price is machine-visible (the bare value layer is empty, C176). The negative pole `Evil` 
>    remains a declared SEM datum. The epistemic reality-hook itself is 
>    unconditional and vocabulary-only (`correct_tracks_reality`, C173/C174).

**Badge legend.** Every icon on a formal consequence is machine-derived from
the Lean kernel (see `formal/GAPMAP.md` and the investigations) — never transcribed:

| icon | meaning |
|---|---|
| `✅` | PROVEN — verified by pure logic; footprint contains only classical meta-logic (`CL`) and the claim's own vocabulary (0 substantive axioms) |
| `⚠️ (AxName)` | AXIOMATIC — machine-verified, yet deliberately rests on the named declared axiom (`SEM` semantic choice / `META` metaphysical bridge) — **not unproved** |
| `📘` | DEFINITIONAL — true by definition of the term being introduced |
| `⏸` | DEFERRED — a claimed result whose Lean declaration is not in the live kernel; annotated surface only (see GAPMAP + source notes), **NOT a theorem in this repository** |
| `🧱 X ⇏ Y` | COUNTERMODEL — a model forces X nowhere near Y: an explicit boundary, not a failure |

Axioms appear as `◆` in the audit ledger. `AXIOM` (the claim *is itself* a declared
axiom) is distinct from `AXIOMATIC` (the claim is *derived under* an axiom).

The badge marks that **step's own** axiom cost, recomputed per declaration from
`#print axioms` — it is never inherited from a neighbouring step. A `✅` that
immediately follows a `⚠️` step is provably axiom-free on its own; badges do not
"propagate" down the chain — the kernel footprint is the transitive closure, so
a `✅` after a `⚠️` means the two share no proof edge: the marker between them is
narration, not inference.

> `✅ · File.lean#name`-style footers point at the exact Lean declaration behind each
> consequence: the anchor is the declaration name, and the link jumps to its line under
> `formal/Logos/`. Follow the `investigations` links for the deeper countermodel and
> retorsion analyses.

**How to read a step.** Claim in words first, machine rendering beneath:
- `∴` introduces the symbolic rendering that follows. `≡` reads "by definition" (`📘`);
  `→` and `↔` mean implication and equivalence; `⇒` chains steps into one argument;
  `⇏` marks a demonstrated *non-consequence* (a countermodel frontier, `🧱`).
- a **backticked name** is the Lean declaration that verifies the line; footers like
  `✅ · File.lean#name` link to it under `formal/Logos/`.
- each section reads: summary → the skeptic's attack & the reply → definitions used
  → the steps. §4–§6 are the gentlest introduction.
- the chain `GenuineNormativity ⇒ Chooses ⇒ FreeWill ⇒ FreeSubject ⇒ Person` is the
  same argument the numbered sections build link by link.

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
| **312 affirmative claims derived** out of **410** ledger claims — 272 ✅ kernel-verified, 40 ⚠️ derived under a substantive (`SEM`/`META`) axiom, each ⚠️ row naming the bridge it rests on. | **14 blocked** ✖ — named individually |
| **44 countermodel boundaries** 🧱 — a hostile model in which the claim *fails*. These are won results about the limit of the theory, not gaps. | &nbsp;&nbsp;· **C228** — any entity that grounds Right/Wrong is a Personal Entity |
| **943 of 1667 theorems in `formal/Logos/` rest on no Γ axiom at all** (57%) — counted from `formal/axiom_audit.json`, not claimed. | &nbsp;&nbsp;· **C73** — Plurality without bridges is blocked: unit countermodel settles that 1 act does not entail plurality; requires AxTwoSubjects |
| **The whole price is 27 declared axioms**: 16 are `VOCAB` (the vocabulary the statements need in order to be sayable) and 11 are substantive. Only the 11 are philosophical commitments; the rest are the theory's definitions of its own words, which is a different thing from a premise. | &nbsp;&nbsp;· **C75** — Propositional personhood is blocked: content existence does not entail personhood |
| **10 attribute corollaries became unconditional theorems** (C389–C398) — they were conditional on a `def` until F15 was declared, so this is a *strengthening*: fewer hidden premises, same conclusions. | &nbsp;&nbsp;· **C79** — Ultimate ground existence is blocked: infinite descending chains have no ultimate element without a well-foundedness axiom |
|  | &nbsp;&nbsp;· **C89** — Ultimate ground by initiation is blocked: non-entailed without well-foundedness |
|  | &nbsp;&nbsp;· **C90** — Personal ultimate ground is blocked: ultimate grounding does not entail personal nature |
|  | &nbsp;&nbsp;· **F10** — Causal (creative) omnipotence |
|  | &nbsp;&nbsp;· **F11** — The bare rejected horn is BLOCKED, and now nameable: Logos.AsieticChoice.bareRejectedHornCoMeant : (∃ s : Subject, ∃ p : Prop, Means s p) → ∃ s… |
|  | &nbsp;&nbsp;· **F12** — The justification for the ASIETY-FREEDOM stipulation is BLOCKED, in two halves that must both be closed |
|  | &nbsp;&nbsp;· **F13** — The Creator-sharing existence claim is BLOCKED, and refuted as derivable rather than open |
|  | &nbsp;&nbsp;· **F14** — Axiomatic diagonal specification for self-referential entertainment |
|  | &nbsp;&nbsp;· **F16** — Divine Immutability - the substantive reading of capacity invariance, that a subject's meaning capacity is constant ACROSS WORLDS - is BLOCKED, and… |
|  | &nbsp;&nbsp;· **F1bUncond** — The precise missing resource (F1b, BLOCKED): one subject co-meaning a content and its negation — the same-subject dual meaning-act |
|  | &nbsp;&nbsp;· **OpenBridgeNormativity** — The positive bivalence→normativity bridge (∀ s p, Judge s p → GenuineNormativity s p (¬p), or stand-antecedent variant) is BLOCKED: bivalence alone… |
|  | **5 deferred** ➖ — named individually |
|  | &nbsp;&nbsp;· **C77** — Conditional necessary-person claim is deferred: the theorem Love.necessaryPersonExists_conditional was removed from the live kernel (commit ae7f4bd)… |
|  | &nbsp;&nbsp;· **C92** — Conditional necessary-entity claim is deferred: the theorem Love.necessary_entity_exists_conditional was removed from the live kernel (commit… |
|  | &nbsp;&nbsp;· **F2** — Deontic teleology is deferred: how norms point at goals is not yet derived |
|  | &nbsp;&nbsp;· **F6** — The Trinity is deferred: no argument exists yet |
|  | &nbsp;&nbsp;· **F8** — The Trinity is not attempted |
|  | **15 retired routes** — settled *negatively*, not pending: each step was destroyed by a hostile model, so the question is closed against it (see *Appendix C*): `C64`, `C65`, `C66`, `C67`, `C69`, `C70`, `C71`, `C72`, `C76`, `C78`, `C80`, `C81`, `C82`, `C87`, `C88` |

**Read the two columns together and the shape is precise: Γ won the metaphysics
of the ground and lost the soteriology.** Established: genuine normativity has a
personal ground; that ground is unique and necessary; it possesses canonical
aseity, simplicity, and pure actuality. Not established: that the person of that
ground is *one*. Strict monotheism, the Trinity, the Incarnation, and creation
each remain open, and each is named above with its missing lemma rather than
absorbed into an average. That is the honest ledger, and the left column is
larger because the ground-theory was proved, not because the open rows were
rounded down.

Four qualifications, stated rather than hidden:

1. **A ✅ means "kernel-verified on declared vocabulary", not "free of metaphysical assumption".** The vocabulary axioms are real axioms; they are merely the ones the statements need in order to be said at all. The substantive ones are the 11 `SEM`/`META` bridges.
2. **The 27 declared axioms are inputs, not wins.** Counting them as results would be the same error as counting a hypothesis as a proof. They are listed so the reader can price Γ exactly, and `VOCAB` is separated from `SEM`/`META` because only the latter are commitments.
3. **A 🧱 is a win about a boundary, not about the claim.** Γ building a model in which monotheism fails is a real theorem — and a theorem *against* monotheism. The columns keep those apart on purpose.
4. **The 15 retired routes are counted as neither won nor open.** Their ledger notes say the step was destroyed under hostile semantics; that is a settled negative. Filing them under "still open" would overstate the debt, and filing them as won would overstate the theory, so they get their own line.

<sub>Declaration count excludes 3 parsed names with no `#print axioms` footprint; they are `parse_lean_sources` artefacts and are excluded from the denominator rather than scored axiom-free.</sub>

## The Argument at a Glance

This chart is the whole argument in one map. Each box is a claim; each arrow shows a forced consequence; each icon states the claim's machine-derived status. Read it, then walk the numbered sections below.

Central Distinction: the upward arrows are *discovery* (from the datum to its ground);
the downward arrows are *ontological grounding* (from the ground to the datum) — the
same proved dependence, read in two directions (see the note above).

<details>
<summary><b>Linear Deductive Roadmap (Steps 1–10 at a glance)</b></summary>

| Step | Milestone | Core Formula | Epistemic Status |
|---|---|---|---|
| **§1** | Objective Right/Wrong | `¬N_T ∧ ¬N_F` | `✅` PROVEN · 0 substantive axioms |
| **§2** | Agential Ought | `Ought TruthNorm ⟨s, p⟩` | `✅` PROVEN · 0 substantive axioms |
| **§3** | Genuine Choice | `Chooses s p q ∧ CommittedChoice s p q r` | `✅` PROVEN (Route A / Route B) |
| **§4** | Free Will | `FreeWill(s)` | `✅` PROVEN · 0 substantive axioms |
| **§5** | Free Subject | `FreeSubject(s) ≡ FreeWill(s)` | `📖` DEFINITIONAL |
| **§6** | Person | `Person(s) ↔ Boethian-Thomistic Core` | `✅` PROVEN · 0 substantive axioms |
| **§7** | Personal Will | `FreeIndependentWill(s)` | `✅` PROVEN · 0 substantive axioms |
| **§8** | Ground of Right/Wrong | `GroundsRightWrong(s)` | `✅` PROVEN · 0 substantive axioms |
| **§9** | Necessary Truth | `□ τ ∧ GroundOfReality Entity.ofGround` | `✅` PROVEN · 0 substantive axioms |
| **§10** | Constructive Ground | `PersonalGroundOfReality Entity.ofGround` | `✅` PROVEN · 0 substantive axioms |

</details>

```text
RIGHT / WRONG
  Right and wrong both obtain: the binary normative distinction is real. The 'Right'/'Wrong' polarity is the objective truth/correctness standard — some propositions are true, some false; affirming a truth is correct, affirming a falsehood is incorrect.
  ⊢ Right ≠ Wrong ∧ EstablishedRightWrong : Prop := ¬N_T ∧ ¬N_F
  *[✅]*
        ▲
        │ [Retorsive Defense Against Skeptical Denial]
        │ ⊢ ClaimsCorrect(s, NoRight) ∧ NoRight → ⊥ [NoRight ≡ ¬NormativeRightExists]
        │
        │ [discovery · normative standard specification]
        ▼
OUGHT / OUGHT-NOT
  Objective correctness determines agential standards: Ought vs. Ought-Not — the epistemic objective standard (a proposition ought to be affirmed because it is true).
  ⊢ Ought TruthNorm ⟨s, p⟩ ∧ OughtNot TruthNorm ⟨s, q⟩
  *[✅]*
        │
        │ [discovery · apprehension of incompatible alternatives]
        ▼
CHOICE
  Apprehending incompatible alternatives within a committed stance constitutes Choice: the agent co-means both horns (`Chooses s p q`) while committing to one (`Act s p` in the stance-bundle `CommittedChoice`).
  ⊢ Chooses s p q : Prop := Means s p ∧ Means s q ∧ Incompatible p q
CommittedChoice s p q r : Prop := Act s p ∧ Chooses s q r
  *[✅]*
        ▲
        │ [Retorsion Against 'Genuine Normativity Is Stipulative']
        │ ⊢ (∃ s, ∃ p, ClaimsNormativeCorrectness s p) → GenuineNormativity s (Correct s NoGN) (Incorrect s NoGN) ∧ ¬ NoGN ∧ (∃ s, FreeWill s)
        ▲
        │ [Committed Choice — the stance carries settlement (2026-09-24)]
        │ ⊢ CommittedChoice s p q r : Prop := Act s p ∧ Chooses s q r
ClaimsNormativeCorrectness s p → CommittedChoice s p (Correct s p) (Incorrect s p)
        ▲
        │ [The Proof-Presentation Alternate Route — Argumentative Engagement Forces Personhood (2026-09-25)]
        │ ⊢ PresentsAsSound s d → CommittedChoice s d (Correct s d) (Incorrect s d) ∧ FreeWill s ∧ Person s
        │
        │ [discovery · PURE LOGIC · 0 substantive axioms]
        ▼
FREE WILL
  Freedom is derived by pure logic from genuine normativity and choice.
  ⊢ Chooses s p q ∧ FreeWill(s)
  *[✅]*
        ▲
        │ [Adversarial Denial Normal Forms (D1–D8) — Exhaustive Proof of Inevitability]
        │ ⊢ ¬ Chooses s p q ∧ CoGrasp → ⊥ | ¬ FreeWill s ∧ Chooses → ⊥
        │
        │ [discovery · definitional equivalence [FreeSubject(s) ≡ FreeWill(s)]]
        ▼
FREE SUBJECT
  A subject is recognized as free in virtue of possessing Free Will.
  ⊢ FreeSubject(s) ≡ FreeWill(s)
  *[✅]*
        │
        │ [discovery · priced theorem [Person := ThomisticPersonCore; via will_individuation]]
        ▼
PERSON
  A free subject is constitutively an authoritative Person.
  ⊢ Person s : Prop := ThomisticPersonCore s
  *[✅]*
        │
        │ [discovery · numerical individuation [will_individuation]]
        ▼
INDEPENDENT PERSONAL WILL
  Distinct persons have numerically distinct wills (subjectWill s₁ ≠ subjectWill s₂).
  ⊢ Person(s) ↔ FreeIndependentWill(s)
  *[✅]*
        │
        │ [GROUNDING · ONTOLOGICAL GROUNDING ARROW [Grounding ≠ Identity]]
        ▼
ONTOLOGICAL GROUND OF RIGHT / WRONG
  Personal free agency ontologically grounds the normative order: the ground of objective normativity is personal in kind/type (Grounding ≠ Id; Grounding ≠ Individual Causation).
  ⊢ RightWrongAt s p q ⇒ ... ⇒ Person s ⇒ GroundsRightWrong s
  *[✅]*
  *[Anti-Self-Legislation: identifying Ought with current will collapses normativity (NORMATIVE COLLAPSE). Hostile Impersonal Model confirms bare ought consistent without a second person (SURVIVING PLATONIST MODEL). Under second-personal address and plurality (AxSecondPersonalAddress META / AxTwoSubjects META), objective ought derives distinct persons.]*
        │
        │ [continuation · modal continuation from normative truth]
        ▼
NECESSARY TRUTH
  The objective logical and normative order entails necessary truth.
  ⊢ □ τ : Prop
  *[✅]*
        │
        │ [discovery · constructive discovery [ObjectiveNormativity ⇒ Person]]
        ▼
CONSTRUCTIVE PERSONAL GROUND
  The machine-proved dependence: wherever Right/Wrong is real, its ground-type is personal (`∀ s, RightWrong s → Person s`, via the priced discovery theorem). The `GroundsRightWrong` record carries only the agential substrate (`∃ p q, Chooses s p q`); personalness of the ground is the priced theorem `grounding_right_wrong_entails_person`, never a field (see §8).
  ⊢ ObjectiveNormativity → ∃ p : Person, RightWrong p ∧ GroundedRightWrong := Σ' p, RightWrong p
  *[✅]*
        │
        ├─── [PROVEN · NECESSARY GROUND — EVERLASTING & ATEMPORAL] → NECESSARY DIVINE GROUND / BEING
        │     ⊢ ∃ g s, NecessaryEntity g ∧ NecessaryGroundOfReality g ∧ Person s ∧ GroundsRightWrong s
        │     *[✅]*
        │
        ├─── [DEFERRED · NOT PART OF PROOF] → ONE GOD / STRICT MONOTHEISM
        │     ⊢ Monotheism
        │     *[⏸]*
        │
        └─── [COUNTERMODEL SEPARATION FRONTIERS] → WHAT THIS DOES NOT YET PROVE
              ⊢ preceding_theory ⇏ trinity | necessary_ground ⇏ contingent_creation
              *[🧱]*
                   │
                   │ [COUNTERMODEL SEPARATION FRONTIERS]
                   ▼
              THEOLOGICAL FRONTIERS
                *[🧱]*
```

## 1. Objective Right and Wrong

The deduction begins with the objective distinction between Right and Wrong (Right ≠ Wrong). Objective normative distinction is real: neither all propositions are true nor all are false (¬N_T ∧ ¬N_F), and rational judgment constitutively presupposes an objective standard of correctness.

The main reader should first understand WHAT is established: the reality of the normative distinction itself. The performative retorsion is a supporting investigation explaining HOW the normative datum is defended against skeptical denial.

Terminology: 'Right'/'Wrong' here denote the objective truth/correctness polarity — a proposition's being true (so that affirming it is correct) vs. being false (so that affirming it is incorrect) — not a moral evaluation of good vs. evil. Moral good/evil is machine-separated from epistemic normativity: a permanent countermodel frontier 🧱 (C175, the model M_amoral carries epistemic agential normativity with zero practical obligation), with the positive moral pole obtained under one disclosed, priced META bridge (the fair definition Good = helping another person is vocabulary-only; moral_good_obtains, C178, rests on AxBenevolentBearingObtains, C177, whose price is machine-visible since the bare value layer is empty, C176). The negative pole Evil remains a declared SEM datum. The extensional distinction (¬N_T ∧ ¬N_F) and the agential stance-conditional form RightWrong s (bridge open, M_inanimate C167) are two distinct formal objects.

*(Detailed technical proof & model analysis: [investigations/right-and-wrong.md](investigations/right-and-wrong.md))*

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** Deny Right/Wrong at all — adopt NoRight, claiming 'there is no correct standard' as if that were itself correct.
> **The reply / the frontier —** Retorsive: claiming the denial as *correct* while it is true is a constructive contradiction (claims_correct_no_right_self_refuting); downplaying to a mere assertion forfeits the claim to correctness. Under classical meta-logic {CL} objective Right necessarily exists — with zero substantive axioms.
>
> **Machine-Checked Kernel Rebuttal —** [`claims_correct_no_right_self_refuting`](formal/Logos/DirectNormativeRetorsion.lean#L60) (Footprint: 0 substantive axioms):
> `⊢ ClaimsCorrect s NoRight ∧ NoRight → ⊥`
</details>

<details>
<summary>Definitions used in this section (4)</summary>

Non-factive assertion-as-correct: Subject s performs an intentional act presenting p as correct.

    ∴ ClaimsCorrect ≡ Act s p ∧ Means(s, Correct s p)

📘 · [RetorsiveNormativity.lean#ClaimsCorrect](formal/Logos/RetorsiveNormativity.lean#L60)

N_F := "no proposition is false" (bivalence: falsity is untruth).

    ∴ N_F ≡ ∀ p, T(p)

📘 · [Core.lean#N_F](formal/Logos/Core.lean#L49)

N_T := "no proposition is true".

    ∴ N_T ≡ ∀ p, ¬T(p)

📘 · [Core.lean#N_T](formal/Logos/Core.lean#L46)

NoRight: The universal skeptical thesis asserting that no genuine normative correctness judgment exists.

    ∴ NoRight ≡ ¬NormativeRightExists

📘 · [DirectNormativeRetorsion.lean#NoRight](formal/Logos/DirectNormativeRetorsion.lean#L53)

</details>

Right and wrong both obtain: it is false that nothing is true, and false that everything is true.

    ∴ ¬N_T ∧ ¬N_F

✅ · [Core.lean#rightWrongDistinction](formal/Logos/Core.lean#L145)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

    1. notNothingTrue  (component witness 1: notNothingTrue)
    2. notEverythingTrue  (component witness 2: notEverythingTrue)

    ∴ ¬N_T ∧ ¬N_F

</details>

The Established Right/Wrong Distinction: The binary normative distinction is real.

    ∴ EstablishedRightWrong ≡ ¬N_T ∧ ¬N_F

📘 · [IndubitableNormativeFreeWill.lean#EstablishedRightWrong](formal/Logos/IndubitableNormativeFreeWill.lean#L53)

<details>
<summary><b>Retorsive Defense Against Skeptical Denial</b> (3 machine-checked theorems) — click to expand</summary>

### Retorsive Defense Against Skeptical Denial

The attempted denial of objective Right and Wrong (NoRight := ¬NormativeRightExists) refutes itself performatively. Claiming the denial as correct (ClaimsCorrect s NoRight) while the denial is true produces a strict constructive contradiction (claims_correct_no_right_self_refuting). Classical double-negation elimination (Classical.not_not, footprint {CL}) derives that objective Right necessarily exists (performative_normative_denial_establishes_normative_right).

The Fundamental Diagonal Retorsion Theorem: Claiming NoRight as correct while NoRight is true produces a strict, constructive contradiction.

    ClaimsCorrect(s, NoRight) ∧ NoRight → ⊥

✅ · [DirectNormativeRetorsion.lean#claims_correct_no_right_self_refuting](formal/Logos/DirectNormativeRetorsion.lean#L60)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

Assume ClaimsCorrect(s, NoRight), and NoRight:

    1. Act s NoRight  (elimination of 1 from hClaim)
    2. Correct(s, NoRight)  (instantiation of Logos.Order.Correct from hAct, hTrue)
    3. NormativeRightExists  (existential introduction with witness s)

    Contradiction: hTrue hEx refutes assumption (→ ⊥)

</details>

Unassertability Theorem: No agent can claim NoRight as correct if NoRight is true.

    ∴ ¬∃ s, ClaimsCorrect(s, NoRight) ∧ NoRight

✅ · [DirectNormativeRetorsion.lean#cannot_claim_correct_no_right_and_true](formal/Logos/DirectNormativeRetorsion.lean#L70)

<details>
<summary>Formal Derivation (1 step, natural deduction, 0 substantive axioms)</summary>

    1. assume ⟨s, hClaim, hTrue⟩  (hypothesis assumption for conditional/reductio proof)

    ∴ ¬∃ s, ClaimsCorrect(s, NoRight) ∧ NoRight

</details>

Performative Derivation Theorem: If any agent actually performs a normative correctness claim on NoRight, the thesis NoRight is strictly false.

    ∃ s, ClaimsCorrect(s, NoRight) → ¬NoRight

✅ · [DirectNormativeRetorsion.lean#performative_normative_denial_establishes_normative_right](formal/Logos/DirectNormativeRetorsion.lean#L79)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

Assume ∃ s, ClaimsCorrect(s, NoRight):

    1. assume hTrue  (hypothesis assumption for conditional/reductio proof)
    2. witness components ⟨s, hClaim⟩  (existential elimination from hDenial)

    ∴ ¬NoRight

</details>

</details>

> ➔ **Linear Forward Transition to Step 2 (Ought and Normative Polarity):** [▲ Discovery · *normative standard specification*]

---

## 2. Ought and Normative Polarity

From objective Right and Wrong, the normative standard is expressed as agential Ought and Ought-Not. Under the objective epistemic TruthNorm, correct judgment implies what the subject ought to affirm, and incorrect judgment implies what the subject ought not to affirm. Correctness and incorrectness constitute a strict deontic opposition between what ought and what ought not to be judged.

Terminology: the Ought/Ought-Not here are derived from the epistemic TruthNorm — they govern whether a judgment about reality is correct to affirm (true) or incorrect (false). They are not the irreducible practical deontic Ought of actions (`OughtRetorsion.Ought`, a separate VOCAB primitive).

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** 'Ought' is nothing but a relabel of 'correct' — no genuinely normative force is added.
> **The reply / the frontier —** The deontic opposition here is derived under the objective epistemic TruthNorm (correct → ought to affirm; incorrect → ought not to affirm) — a genuinely new normative relation, not a relabel; the irreducible practical Ought of actions stays a separate primitive (see the terminology note above).
>
> **Machine-Checked Kernel Rebuttal —** [`correctness_deontic_opposition`](formal/Logos/NormativeOrder.lean#L155) (Footprint: 0 substantive axioms):
> `⊢ DeonticOpposition (Correct s p) (Incorrect s p)`
</details>

<details>
<summary>Definitions used in this section (7)</summary>

Correctness: a subject's act of judging p is correct iff p is true. The act is constitutive: an act is a meaningful initiation (`A s p := Means s p ∧ ∃ w w', Initiates s w w' p`), so every correct judgment embodies intentional meaning.

    ∴ Correct ≡ A(s, p) ∧ T(p)

📘 · [Order.lean#Correct](formal/Logos/Order.lean#L29)

Deontic Opposition: Compliance (p) and violation (q) are mutually incompatible and distinct.

    ∴ DeonticOpposition ≡ Incompatible(p, q) ∧ (p ≠ q)

📘 · [IndubitableNormativeFreeWill.lean#DeonticOpposition](formal/Logos/IndubitableNormativeFreeWill.lean#L72)

Incorrectness: a subject's act of *meaning* p is incorrect iff p is false. Same as `Correct`: the meaning-act `A s p` is a conjunct, hence unavoidable.

    ∴ Incorrect ≡ A(s, p) ∧ IsFalse(p)

📘 · [Order.lean#Incorrect](formal/Logos/Order.lean#L49)

Falsity under bivalence: a proposition is false iff it is not true.

    ∴ IsFalse ≡ ¬T(p)

📘 · [Core.lean#IsFalse](formal/Logos/Core.lean#L52)

General agential Ought: the act is prescribed by standard N.

    ∴ Ought ≡ N.prescribes a

📘 · [NormativeOrder.lean#Ought](formal/Logos/NormativeOrder.lean#L61)

General agential OughtNot: the act is prohibited by standard N.

    ∴ OughtNot ≡ N.prohibits a

📘 · [NormativeOrder.lean#OughtNot](formal/Logos/NormativeOrder.lean#L66)

Truth, *defined* as identity (E0): `T p` is `p` itself.

    ∴ T ≡ p

📘 · [Core.lean#T](formal/Logos/Core.lean#L40)

</details>

Deontic opposition between the positive normative pole (Correct s p) and the negative pole (Incorrect s p).

    Act s p → DeonticOpposition(Correct s p, Incorrect s p)

✅ · [NormativeOrder.lean#correctness_deontic_opposition](formal/Logos/NormativeOrder.lean#L155)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

Assume Act s p:

    1. correctness_incompatible s p  (component witness 1: correctness_incompatible s p)
    2. correctness_distinct_of_act s p hAct  (component witness 2: correctness_distinct_of_act s p hAct)

    ∴ DeonticOpposition(Correct s p, Incorrect s p)

</details>

<details>
<summary>Supporting Infrastructure — 3 auxiliary theorem(s) beneath this step</summary>

The objective epistemic norm of Truth: truth prescribes affirmation, and falsity prohibits affirmation.

    ∴ TruthNorm ≡ T(a).content prohibits a := IsFalse(a).content incompatible a := fun ⟨hT, hF⟩ => hF hT

📘 · [NormativeOrder.lean#TruthNorm](formal/Logos/NormativeOrder.lean#L72)

A correct judgment act implies that the subject ought to affirm the content under TruthNorm.

    Correct(s, p) → Ought TruthNorm ⟨s, p⟩

✅ · [NormativeOrder.lean#correct_implies_ought](formal/Logos/NormativeOrder.lean#L83)

An incorrect judgment act implies that the subject ought not to affirm the content under TruthNorm.

    Incorrect(s, p) → OughtNot TruthNorm ⟨s, p⟩

✅ · [NormativeOrder.lean#incorrect_implies_oughtNot](formal/Logos/NormativeOrder.lean#L89)

</details>

> ➔ **Linear Forward Transition to Step 3 (Genuine Choice):** [▲ Discovery · *apprehension of incompatible alternatives*]

---

## 3. Genuine Choice

Step glossary, aligned with the definitions. THE core: `Chooses s p q` (co-meaning) — the agent cognitively grasps both incompatible contents in thought; it is the vocabulary level at which freedom is defined (`FreeWill s := ∃ p q, Chooses s p q`, definitional). Commitment ('committing to one') is NOT inside `Chooses`: a contemplative subject who co-means without settling still satisfies it (`contemplatesWithoutSettling_implies_freeWill`). Settlement is carried by the normative-judicative stance, whose bundle is the new definition `CommittedChoice s p q r := Act s p ∧ Chooses s q r` — the stance instantiates it on the judicative poles with zero substantive axioms (`claims_normative_correctness_implies_committed_choice`, footprint {Initiates, Means, State, Subject, CL}). Boundaries: weak choice = choice field (representability only, `ChoiceField`); contemplative co-meaning does count as `Chooses`/`FreeWill` (the honest boundary); real deliberation (`Selects`/`DeliberateChoice`) demands the truth-laden assertion and is not forced; the libertarian-grade notions (`StrongChooses`, `GenuineChooses`) remain the incompatibilist frontier, available only under the constitutive deontic semantics (conditional T6/T7). Executive selection (`Selects`/`Choice`/`FreeAgency`) is separated from the deliberative `Chooses` line with no bridge axioms (`M_det`, `ExecutiveDeliberativeFrontier` Track A–H): committing bundles settlement via the `Act` conjunct but derives no executive causation or sourcehood, while `ContemplatesWithoutSettling` still implies `FreeWill`.

*(Detailed technical proof & model analysis: [investigations/contrastive-choice.md](investigations/contrastive-choice.md))*

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** Genuine Normativity is a stipulation — the chain GN → Chooses → FreeWill may be valid but empty.
> **The reply / the frontier —** Retorsive: claiming the denial of genuine normativity as correct (ClaimsCorrect s NoGN) yields a literal term of the identical GenuineNormativity structure (denial_of_genuine_normativity_is_self_refuting); the axiom-free stance-level derivation is set out in the retorsion block below.
>
> **Machine-Checked Kernel Rebuttal —** [`d7_co_grasp_is_definitionally_choice`](formal/Logos/UndeniableNormativeDerivation.lean#L267) (Footprint: 0 substantive axioms):
> `⊢ Means s p ∧ Means s q ∧ Incompatible p q ∧ ¬ Chooses s p q → ⊥`
</details>

<details>
<summary>Definitions used in this section (19; 15 new, 4 already shown)</summary>

`Act s p`: strong act: meaningful initiation of movement.

    ∴ Act ≡ Means(s, p) ∧ ∃ w, w', Initiates s w w' p

📘 · [Agency.lean#Act](formal/Logos/Agency.lean#L173)

Mechanical Checker: A deterministic syntactic decision procedure checking formal tree validity. It operates purely on syntax without intentionality.

    ∴ Checker ≡ T(conclusion d)

📘 · [ProofPresentationRetorsion.lean#Checker](formal/Logos/ProofPresentationRetorsion.lean#L79)

The constitutive normative judicative stance: the subject performs the judgment act while grasping both the positive normative standard (Correctness) and the negative normative standard (Incorrectness).

    ∴ ClaimsNormativeCorrectness ≡ Act s p ∧ Means(s, Correct s p) ∧ Means(s, Incorrect s p)

📘 · [NormativeOrder.lean#ClaimsNormativeCorrectness](formal/Logos/NormativeOrder.lean#L168)

Committed choice: the subject is committed to p (performs the act on p) while co-meaning the incompatible alternatives q and r in thought.

    ∴ CommittedChoice ≡ Act s p ∧ Chooses(s, q, r)

📘 · [NormativeOrder.lean#CommittedChoice](formal/Logos/NormativeOrder.lean#L236)

Semantic soundness: The conclusion of the derivation tracks reality / truth.

    ∴ DerivationSound ≡ T(conclusion d)

📘 · [ProofPresentationRetorsion.lean#DerivationSound](formal/Logos/ProofPresentationRetorsion.lean#L84)

A subject is a free subject iff it possesses free will (definitionally, genuinely chooses).

    ∴ FreeSubject ≡ FreeWill(s)

📘 · [Choice.lean#FreeSubject](formal/Logos/Choice.lean#L185)

§15 — freedom (DEFINITION; freedom/choice fix, 2026-09-18): a subject is free iff it genuinely chooses between some incompatible pair. The implication choice → freedom is definitional (`chooses_implies_freeWill`).

    ∴ FreeWill ≡ ∃ p, q, Chooses(s, p, q)

📘 · [Choice.lean#FreeWill](formal/Logos/Choice.lean#L177)

Genuine Strong Normativity: The complete constitutive structure of an authoritative normative directive addressed to subject s between Right (p) and Wrong (q).

    ∴ structure GenuineNormativity (s : Subject) (p q : Prop) : Prop where

📘 · [IndubitableNormativeFreeWill.lean#GenuineNormativity](formal/Logos/IndubitableNormativeFreeWill.lean#L84)

`p` and `q` are incompatible contents.

    ∴ Incompatible ≡ ¬(p ∧ q)

📘 · [Alternatives.lean#Incompatible](formal/Logos/Alternatives.lean#L17)

Incorrect delimitation in a judicative signature (mirrors Order.Incorrect).

    ∴ JudSigIncorrect ≡ JudSigAct(sig, s, p) ∧ sig.IsFalse(p)

📘 · [BipolarityRetorsion.lean#JudSigIncorrect](formal/Logos/BipolarityRetorsion.lean#L267)

Local means-relation: the subject's judgement always reaches any content.

    ∴ Means ≡ True

📘 · [MoralFrontierAudit.lean#Means](formal/Logos/MoralFrontierAudit.lean#L80)

The skeptical denial proposition: There is no genuine normativity anywhere.

    ∴ NoGN ≡ ¬GenuineNormativityExists

📘 · [RetorsiveNormativity.lean#NoGN](formal/Logos/RetorsiveNormativity.lean#L123)

Person: an individual substance of a rational nature, possessed of dominion over its own acts (Boethius; Aquinas, ST I q.29 a.3).

    ∴ Person ≡ ThomisticPersonCore(s)

📘 · [Person.lean#Person](formal/Logos/Person.lean#L127)

Voice: act plus grasp of the positive pole `Correct s p` — nothing more; this is all `ClaimsCorrect` gives in Γ.

    ∴ VoiceSig ≡ JudSigAct(sig, s, p) ∧ sig.Means(s, JudSigCorrect(sig, s, p))

📘 · [BipolarityRetorsion.lean#VoiceSig](formal/Logos/BipolarityRetorsion.lean#L272)

Extract the conclusion proposition from a syntactic derivation tree.

    ∴ conclusion ≡ T(conclusion d)

📘 · [ProofPresentationRetorsion.lean#conclusion](formal/Logos/ProofPresentationRetorsion.lean#L73)

    ∴ Correct ≡ A(s, p) ∧ T(p) — defined in §2. Ought and Normative Polarity.

    ∴ Incorrect ≡ A(s, p) ∧ IsFalse(p) — defined in §2. Ought and Normative Polarity.

    ∴ N_F ≡ ∀ p, T(p) — defined in §1. Objective Right and Wrong.

    ∴ N_T ≡ ∀ p, ¬T(p) — defined in §1. Objective Right and Wrong.

</details>

Deliberate choice entails genuine choice in the co-meaning sense.

    DeliberateChoice(s, p, q) → Chooses(s, p, q)

✅ · [Choice.lean#deliberateChoice_implies_chooses](formal/Logos/Choice.lean#L461)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

Assume DeliberateChoice(s, p, q):

    1. h.1  (component witness 1: h.1)
    2. h.2.1  (component witness 2: h.2.1)
    3. h.2.2.1  (component witness 3: h.2.2.1)

    ∴ Chooses(s, p, q)

</details>

<details>
<summary>Supporting Infrastructure — 2 auxiliary theorem(s) beneath this step</summary>

`Chooses s p q`: strong choice: the subject co-means incompatible alternatives.

    ∴ Chooses ≡ Means(s, p) ∧ Means(s, q) ∧ Incompatible(p, q)

📘 · [Choice.lean#Chooses](formal/Logos/Choice.lean#L116)

Every proposition is incompatible with its own negation.

    ∴ Incompatible(p, ¬p)

✅ · [Choice.lean#incompatible_self_negation](formal/Logos/Choice.lean#L124)

<details>
<summary>Formal Derivation (1 step, natural deduction, 0 substantive axioms)</summary>

    1. assume h  (hypothesis assumption for conditional/reductio proof)

    ∴ Incompatible(p, ¬p)

</details>

</details>

<details>
<summary><b>Retorsion Against 'Genuine Normativity Is Stipulative'</b> (5 machine-checked theorems) — click to expand</summary>

### Retorsion Against 'Genuine Normativity Is Stipulative'

Attack: `GenuineNormativity` is just incompatible alternatives plus `Means(s,p)` and `Means(s,q)` — a stipulation of what 'normativity' means.

Strong retorsion, axiom-free: the normative-judicative stance — the performative datum described in the scope box above — derives GenuineNormativity on the judicative poles and thereby refutes NoGN, without any substantive axiom (normative_stance_refutes_attack_without_axioms). Its stance antecedent `(∃ s, ∃ p, ClaimsNormativeCorrectness s p)` is made explicit in the step block and the chart; `Cogito` turns a *given* assertion into an act and does not supply the stance; only the weak-voice twin of the retorsion costs `AxJudicativeBipolarity` (SEM).

Residuals, stated once: voicing alone does not force the stance (`M_oneway`, C166), and an inanimate bivalent universe realizes no genuine normativity (`M_inanimate`, C167) — the two independence witnesses below establish both, so no zero-input `⊢ ∃ s, FreeWill s` theorem is claimed; under a denied horn, deliberation lives on the separate DeliberateChoice / ClaimsNormativeCorrectness route. A weak-voice twin variant exists but is dispensable for this narrative.

**Axiom-free normative-judicative route — ZERO substantive axioms (footprint {Initiates, Means, State, Subject, CL}):**

Structure-identity: the axiom-free normative route terminates in the SAME GenuineNormativity type (horns = the judicative normative poles Correct vs Incorrect) as the AxJudicativeBipolarity route; the downstream chain GN → Chooses → FreeWill is therefore route-agnostic.

    ClaimsNormativeCorrectness(s, NoGN) → GenuineNormativity s (Correct(s, NoGN)) (Incorrect(s, NoGN))

✅ · [RetorsiveNormativity.lean#normative_retorsion_same_structure_type](formal/Logos/RetorsiveNormativity.lean#L278)

Non-vacuity: any normative-judicative stance (an actual claim of correctness over some content) derives GenuineNormativity on the Correct/Incorrect poles and thereby refutes NoGN — with ZERO substantive axioms, no AxJudicativeBipolarity, no new SEM.

    ∃ s, p, ClaimsNormativeCorrectness(s, p) → ¬NoGN

✅ · [RetorsiveNormativity.lean#normative_stance_refutes_attack_without_axioms](formal/Logos/RetorsiveNormativity.lean#L291)

<details>
<summary>Formal Derivation (4 steps, natural deduction, 0 substantive axioms)</summary>

Assume ∃ s, p, ClaimsNormativeCorrectness(s, p):

    1. assume hNoGN  (hypothesis assumption for conditional/reductio proof)
    2. witness components ⟨s, p, hClaim⟩  (existential elimination from h)
    3. GenuineNormativity s (Correct(s, p)) (Incorrect(s, p))  (from )
    4. GenuineNormativityExists  (from )

    ∴ ¬NoGN

</details>

Free-will corollary: the combined result `(¬ NoGN) ∧ (∃ s, FreeWill s)` falls out by pure logic — the stance yields GenuineNormativity (refuting NoGN), and co-grasp of incompatible alternatives is definitionally choice, which is definitionally free will (`d8_choice_is_definitionally_free_will`).

    ∃ s, p, ClaimsNormativeCorrectness(s, p) → (¬NoGN) ∧ (∃ s, FreeWill(s))

✅ · [RetorsiveNormativity.lean#attack_inviable_without_axioms](formal/Logos/RetorsiveNormativity.lean#L309)

<details>
<summary>Formal Derivation (4 steps, natural deduction, 0 substantive axioms)</summary>

Assume ∃ s, p, ClaimsNormativeCorrectness(s, p):

    1. split into forward and reverse directions (↔ / ∧)  (split equivalence/conjunction into forward (mp) and reverse (mpr) goals)
    2. witness components ⟨s, p, hClaim⟩  (existential elimination from h)
    3. s  (conjunction conjunct 1: s)
    4. (claims_normative_correctness_derives_free_will s p hClaim).2  (conjunction conjunct 2: (claims_normative_correctness_derives_free_will s p hClaim).2)

    ∴ (¬NoGN) ∧ (∃ s, FreeWill(s))

</details>

**Independence witnesses — what the retorsion does NOT force:**

In primitive Γ, voicing a judgment does NOT force the normative-judicative stance: M_oneway voices `True` as correct (act plus grasp of the positive pole) while failing to mean `Incorrect () True` — machine witness of the voice↔stance gap.

    ∴ ∃ sig, s, p, VoiceSig(sig, s, p) ∧ ¬sig.Means(s, JudSigIncorrect(sig, s, p))

✅ · [BipolarityRetorsion.lean#voice_without_normative_stance](formal/Logos/BipolarityRetorsion.lean#L319)

<details>
<summary>Formal Derivation (5 steps, natural deduction, 0 substantive axioms)</summary>

    1. M_oneway  (component witness 1: M_oneway)
    2. ()  (component witness 2: ())
    3. True  (component witness 3: True)
    4. m_oneway_voice_holds  (component witness 4: m_oneway_voice_holds)
    5. m_oneway_stance_fails  (component witness 5: m_oneway_stance_fails)

    ∴ ∃ sig, s, p, VoiceSig(sig, s, p) ∧ ¬sig.Means(s, JudSigIncorrect(sig, s, p))

</details>

Direct witness (`M_inanimate`): an inanimate universe is extensionally bivalent (`¬N_T ∧ ¬N_F`) yet realizes NO instance of the genuine-normativity shape — incompatible alternatives plus agential address via a means relation.

    ∴ ∃ U, MeansRel, (¬N_T ∧ ¬N_F) ∧ ¬∃ s,(p q : Prop), Incompatible(p, q) ∧ p ≠ q ∧ MeansRel s p ∧ MeansRel s q

✅ · [UndeniableNormativeDerivation.lean#inanimate_universe_satisfies_bivalence_and_no_genuine_normativity](formal/Logos/UndeniableNormativeDerivation.lean#L93)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

    1. witness tuple ⟨Empty, fun e _ => False, Logos.Core.rightWrongDistinction, ?_⟩  (existential/conjunction refinement with Empty, fun e _ => False, Logos.Core.rightWrongDistinction, ?_)
    2. assume ⟨s, _p, _q, _hInc, _hNeq, _hMeansP, _hMeansQ⟩  (hypothesis assumption for conditional/reductio proof)
    3. vacuous contradiction on empty s  (elimination of empty type s (→ ⊥))

    ∴ ∃ U, MeansRel, (¬N_T ∧ ¬N_F) ∧ ¬∃ s,(p q : Prop), Incompatible(p, q) ∧ p ≠ q ∧ MeansRel s p ∧ MeansRel s q

</details>

</details>

<details>
<summary><b>Committed Choice — the stance carries settlement (2026-09-24)</b> (7 machine-checked theorems) — click to expand</summary>

### Committed Choice — the stance carries settlement (2026-09-24)

The reader-facing gloss 'apprehending incompatible alternatives and committing to one' had no defendant: `Chooses` is only the cognitive co-meaning core, and a purely contemplative subject satisfies it. The strengthening locates commitment in the existing normative-judicative stance: `ClaimsNormativeCorrectness s p` performs the judgment act on p (the commitment) AND co-means the incompatible judicative poles `Correct s p` / `Incorrect s p` (the grasp). That bundle, defined as `CommittedChoice`, entails `Chooses`, `FreeWill`, and `FreeSubject` at the unchanged footprint {Initiates, Means, State, Subject, CL} — zero substantive axioms, no added hypotheses. `ClaimsNormativeCorrectness` itself is **defined** (`NormativeOrder.lean`), not assumed: instantiating it by grasping the negative pole is the performative datum, and a bare voice that never co-means `Incorrect` does not force it (`M_oneway`, C166).

**Stance instantiates CommittedChoice — zero substantive axioms (footprint {Initiates, Means, State, Subject, CL}):**

The normative judicative stance is, by construction, a committed choice: the stance performs the judgment act on p (commitment) and co-means the two judicative normative poles `Correct s p` and `Incorrect s p` (grasp), which are incompatible.

    ClaimsNormativeCorrectness(s, p) → CommittedChoice s p (Correct(s, p)) (Incorrect(s, p))

✅ · [NormativeOrder.lean#claims_normative_correctness_implies_committed_choice](formal/Logos/NormativeOrder.lean#L269)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

Assume ClaimsNormativeCorrectness(s, p):

    1. h.1  (conjunction conjunct 1: h.1)
    2. (claims_normative_correctness_derives_free_will s p h).1  (conjunction conjunct 2: (claims_normative_correctness_derives_free_will s p h).1)

    ∴ CommittedChoice s p (Correct(s, p)) (Incorrect(s, p))

</details>

Master committed-choice theorem from the stance: committed choice, co-meaning, and free will all hold of the judicative stance at the unchanged footprint.

    ClaimsNormativeCorrectness(s, p) → CommittedChoice s p (Correct(s, p)) (Incorrect(s, p)) ∧ Chooses(s, Correct(s, p), Incorrect(s, p)) ∧ FreeWill(s)

✅ · [NormativeOrder.lean#claims_normative_correctness_derives_committed_free_will](formal/Logos/NormativeOrder.lean#L277)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

Assume ClaimsNormativeCorrectness(s, p):

    1. claims_normative_correctness_implies_committed_choice s p h  (component witness 1: claims_normative_correctness_implies_committed_choice s p h)
    2. claims_normative_correctness_derives_free_will s p h  (component witness 2: claims_normative_correctness_derives_free_will s p h)

    ∴ CommittedChoice s p (Correct(s, p)) (Incorrect(s, p)) ∧ Chooses(s, Correct(s, p), Incorrect(s, p)) ∧ FreeWill(s)

</details>

Whenever a normative judicative stance exists (any Act-judged content claimed correct against a prohibited alternative), committed choice exists.

    ∃ s, p, ClaimsNormativeCorrectness(s, p) → ∃ s,(p q r : Prop), CommittedChoice s p q r

✅ · [NormativeOrder.lean#committed_choice_exists_of_stance](formal/Logos/NormativeOrder.lean#L287)

<details>
<summary>Formal Derivation (5 steps, natural deduction, 0 substantive axioms)</summary>

Assume ∃ s, p, ClaimsNormativeCorrectness(s, p):

    1. s  (conjunction conjunct 1: s)
    2. p  (conjunction conjunct 2: p)
    3. Correct s p  (conjunction conjunct 3: Correct s p)
    4. Incorrect s p  (conjunction conjunct 4: Incorrect s p)
    5. claims_normative_correctness_implies_committed_choice s p hc  (conjunction conjunct 5: claims_normative_correctness_implies_committed_choice s p hc)

    ∴ ∃ s,(p q r : Prop), CommittedChoice s p q r

</details>

**Definitional entailments of the committed bundle (pure logic):**

Committed choice carries the deliberate grasp of the incompatible alternatives.

    CommittedChoice s p q r → Chooses(s, q, r)

✅ · [NormativeOrder.lean#committedChoice_implies_chooses](formal/Logos/NormativeOrder.lean#L241)

Committed choice carries commitment in the world (the performed act on p).

    CommittedChoice s p q r → Act s p

✅ · [NormativeOrder.lean#committedChoice_implies_act](formal/Logos/NormativeOrder.lean#L247)

Committed choice entails free will, definitionally from `Chooses`.

    CommittedChoice s p q r → FreeWill(s)

✅ · [NormativeOrder.lean#committedChoice_implies_freeWill](formal/Logos/NormativeOrder.lean#L253)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

Assume CommittedChoice s p q r:

    1. q  (component witness 1: q)
    2. r  (component witness 2: r)
    3. committedChoice_implies_chooses s p q r h  (component witness 3: committedChoice_implies_chooses s p q r h)

    ∴ FreeWill(s)

</details>

Committed choice entails free subjectivity, definitionally (`FreeSubject s := FreeWill s`).

    CommittedChoice s p q r → FreeSubject(s)

✅ · [NormativeOrder.lean#committedChoice_implies_freeSubject](formal/Logos/NormativeOrder.lean#L259)

</details>

<details>
<summary><b>The Proof-Presentation Alternate Route — Argumentative Engagement Forces Personhood (2026-09-25)</b> (8 machine-checked theorems) — click to expand</summary>

### The Proof-Presentation Alternate Route — Argumentative Engagement Forces Personhood (2026-09-25)

Where does the initial normative claim come from? In addition to the foundational performative datum of everyday judgment (Route A), Γ provides a machine-checked alternate route directly from the proof itself (Route B):

1. **The Machine Fallacy Separated:** Mechanical syntax checking (`Checker d = true`) does not force normativity; in an uninhabited world (`Subject = Empty`), `M_inanimate_checker` verifies the proof with zero subjects (`syntactic_validity_without_subject_or_normativity`, `{}`).
2. **Argumentative Presentation (Route B):** Any agent who presents a derivation as sound (`PresentsAsSound s d`) co-means correctness and the prohibition of fallacy, deriving `CommittedChoice`, `FreeWill`, and `Person s` with 0 substantive axioms (`presents_as_sound_derives_personhood`, `{Initiates, Means, State, Subject, CL}`).
3. **Dialectical Retorsion on Proof Criticism:** An adversarial critic who attacks Γ by presenting an objection argumentatively as sound themselves instantiates the normative stance, constructively proving their own freedom and personhood (`critic_presenting_objection_is_person`, 0 substantive axioms).

**Proof Presentation Derivations — zero substantive axioms (footprint {Initiates, Means, State, Subject, CL}):**

Presenting a derivation as sound constitutively instantiates the normative-judicative stance (`ClaimsNormativeCorrectness`).

    Derivation ∧ PresentsAsSound(s, d) → ClaimsNormativeCorrectness(s, DerivationSound(d))

✅ · [ProofPresentationRetorsion.lean#presents_as_sound_implies_claims_normative_correctness](formal/Logos/ProofPresentationRetorsion.lean#L134)

<details>
<summary>Formal Derivation (1 step, natural deduction, 0 substantive axioms)</summary>

Assume Derivation, and PresentsAsSound(s, d):

    1. ClaimsNormativeCorrectness(s, DerivationSound(d))  (definitional identity via h)

    ∴ ClaimsNormativeCorrectness(s, DerivationSound(d))

</details>

Presenting a derivation as sound derives committed choice on the normative poles.

    Derivation ∧ PresentsAsSound(s, d) → CommittedChoice s (DerivationSound(d)) (Correct(s, DerivationSound(d))) (Incorrect(s, DerivationSound(d)))

✅ · [ProofPresentationRetorsion.lean#presents_as_sound_derives_committed_choice](formal/Logos/ProofPresentationRetorsion.lean#L152)

Master Theorem of Proof Presentation: An agent presenting a formal derivation as sound necessarily instantiates committed choice, co-grasp of incompatible alternatives, free will, free subjectivity, and personhood.

    Derivation ∧ PresentsAsSound(s, d) → CommittedChoice s (DerivationSound(d)) (Correct(s, DerivationSound(d))) (Incorrect(s, DerivationSound(d))) ∧ Chooses(s, Correct(s, DerivationSound(d)), Incorrect(s, DerivationSound(d))) ∧ FreeWill(s) ∧ FreeSubject(s) ∧ Person(s)

✅ · [ProofPresentationRetorsion.lean#presents_as_sound_derives_personhood](formal/Logos/ProofPresentationRetorsion.lean#L164)

<details>
<summary>Formal Derivation (9 steps, natural deduction, 0 substantive axioms)</summary>

Assume Derivation, and PresentsAsSound(s, d):

    1. Chooses(s, Correct(s, DerivationSound(d)), Incorrect(s, DerivationSound(d)))  (from )
    2. FreeWill(s)  (elimination of 2 from hFWTuple)
    3. FreeSubject(s)  (modus ponens via (freeSubject_iff_freeWill)
    4. Person(s)  (modus ponens via free_subject_is_person)
    5. hCC  (conjunction conjunct 1: hCC)
    6. hChooses  (conjunction conjunct 2: hChooses)
    7. hFW  (conjunction conjunct 3: hFW)
    8. hFS  (conjunction conjunct 4: hFS)
    9. hPerson  (conjunction conjunct 5: hPerson)

    ∴ CommittedChoice s (DerivationSound(d)) (Correct(s, DerivationSound(d))) (Incorrect(s, DerivationSound(d))) ∧ Chooses(s, Correct(s, DerivationSound(d)), Incorrect(s, DerivationSound(d))) ∧ FreeWill(s) ∧ FreeSubject(s) ∧ Person(s)

</details>

Whenever any agent presents any derivation as sound, a Free Person exists.

    ∃ s, d, PresentsAsSound(s, d) → ∃ s, Person(s) ∧ FreeWill(s)

✅ · [ProofPresentationRetorsion.lean#person_exists_of_presentation](formal/Logos/ProofPresentationRetorsion.lean#L184)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

Assume ∃ s, d, PresentsAsSound(s, d):

    1. s  (conjunction conjunct 1: s)
    2. hRes.2.2.2.2  (conjunction conjunct 2: hRes.2.2.2.2)
    3. hRes.2.2.1  (conjunction conjunct 3: hRes.2.2.1)

    ∴ ∃ s, Person(s) ∧ FreeWill(s)

</details>

**Dialectical Retorsion on Adversarial Proof Criticism:**

Dialectical Retorsion: Any skeptic attempting to deny objective correctness in formal derivations by claiming normative nihilism (`NoRight`) refutes itself constructively.

    ClaimsCorrect(s, NoRight) ∧ NoRight → False

✅ · [ProofPresentationRetorsion.lean#proof_criticism_nihilism_self_refuting](formal/Logos/ProofPresentationRetorsion.lean#L199)

An adversarial critic who presents an objection argumentatively as sound themselves instantiates the normative stance and is therefore a Free Person.

    Derivation ∧ PresentsAsSound(critic, objection) → Person(critic) ∧ FreeWill(critic)

✅ · [ProofPresentationRetorsion.lean#critic_presenting_objection_is_person](formal/Logos/ProofPresentationRetorsion.lean#L206)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

Assume Derivation, and PresentsAsSound(critic, objection):

    1. hRes.2.2.2.2  (conjunction conjunct 1: hRes.2.2.2.2)
    2. hRes.2.2.1  (conjunction conjunct 2: hRes.2.2.1)

    ∴ Person(critic) ∧ FreeWill(critic)

</details>

**Separation Countermodels — Syntactic validity alone does not force normativity:**

Hostile Model 1 (`M_inanimate_checker`): An uninhabited universe with zero subjects.

    syntactic_validitywithout_subject_or_normativity ⇏ Independence

🧱 syntactic_validitywithout_subject_or_normativity ⇏ Independence · [ProofPresentationRetorsion.lean#syntactic_validity_without_subject_or_normativity](formal/Logos/ProofPresentationRetorsion.lean#L97)

<details>
<summary>Formal Derivation (5 steps, natural deduction, 0 substantive axioms)</summary>

    1. witness tuple ⟨Empty, fun e _ => False, Derivation.leaf True, ?_⟩  (existential/conjunction refinement with Empty, fun e _ => False, Derivation.leaf True, ?_)
    2. rfl  (conjunction conjunct 1: rfl)
    3. fun e _ => id  (conjunction conjunct 2: fun e _ => id)
    4. fun e  (conjunction conjunct 3: fun e)
    5. _ => nomatch e  (conjunction conjunct 4: _ => nomatch e)

    ∴ ∃ Universe, MeansRel, d, Checker(d) = true ∧ (∀ s, p, ¬MeansRel s p) ∧ ¬(∃ _s, True)

</details>

Hostile Model 2: Mechanical execution in `JudicativeSig` using `M_oneway`.

    checker_validity_does_not_force_normative_stance ⇏ Independence

🧱 checker_validity_does_not_force_normative_stance ⇏ Independence · [ProofPresentationRetorsion.lean#checker_validity_does_not_force_normative_stance](formal/Logos/ProofPresentationRetorsion.lean#L109)

<details>
<summary>Formal Derivation (1 step, natural deduction, 0 substantive axioms)</summary>

    1. witness tuple ⟨M_oneway, (), Derivation.leaf True, rfl, ?_, m_oneway_stance_fails⟩  (existential/conjunction refinement with M_oneway, (), Derivation.leaf True, rfl, ?_, m_oneway_stance_fails)

    ∴ ∃ sig, s, d, Checker(d) = true ∧ VoiceSig(sig, s, conclusion(d)) ∧ ¬sig.Means(s, JudSigIncorrect(sig, s, conclusion(d)))

</details>

</details>

> ➔ **Linear Forward Transition to Step 4 (Free Will):** [▲ Discovery · *PURE LOGIC · 0 substantive axioms*]

---

## 4. Free Will

We did not assume a free subject. Free Will is derived, not assumed: from the reality of genuine normative address and rational choice, Free Will follows from Genuine Normativity by pure logic with zero substantive axioms — a subject endowed with the capacity to choose between incompatible alternatives possesses Free Will by definition.

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** You assumed freedom — a free will was smuggled in as a premise.
> **The reply / the frontier —** No — the starting point is normative address, not a free subject: see the derivation in the section text (`indubitable_normative_free_will`).
>
> **Machine-Checked Kernel Rebuttal —** [`d8_choice_is_definitionally_free_will`](formal/Logos/UndeniableNormativeDerivation.lean#L275) (Footprint: 0 substantive axioms):
> `⊢ Chooses s p q ∧ ¬ FreeWill s → ⊥`
</details>

<details>
<summary>Definitions used in this section (2; 0 new, 2 already shown)</summary>

    ∴ Chooses ≡ Means(s, p) ∧ Means(s, q) ∧ Incompatible(p, q) — first shown in §3. Genuine Choice.

    ∴ FreeWill ≡ ∃ p, q, Chooses(s, p, q) — defined in §3. Genuine Choice.

</details>

The Shortest Complete Master Proof: Genuine Normativity derives Choice and Free Will.

    GenuineNormativity s p q → Chooses(s, p, q) ∧ FreeWill(s)

✅ · [IndubitableNormativeFreeWill.lean#indubitable_normative_free_will](formal/Logos/IndubitableNormativeFreeWill.lean#L115)

<details>
<summary>Formal Derivation (7 steps, natural deduction, 0 substantive axioms)</summary>

Assume GenuineNormativity s p q:

    1. Means(s, p)  (elimination of 1 from h.address)
    2. Means(s, q)  (elimination of 2 from h.address)
    3. Incompatible(p, q)  (elimination of 1 from h.opposition)
    4. Chooses(s, p, q)  (instantiation of Chooses from hMeansP, hMeansQ, hIncomp)
    5. FreeWill(s)  (instantiation of FreeWill from p, q, hChooses)
    6. hChooses  (conjunction conjunct 1: hChooses)
    7. hFreeWill  (conjunction conjunct 2: hFreeWill)

    ∴ Chooses(s, p, q) ∧ FreeWill(s)

</details>

<details>
<summary>Supporting Infrastructure — 1 auxiliary theorem(s) beneath this step</summary>

Freedom exists as soon as a genuine choice witness is supplied. This is the formal shape of the target `freeWillExists`; it is *conditional* because the unconditional witness is exactly the blocked `rejectedHornCoMeant`.

    ∃ s, p, q, Chooses(s, p, q) → ∃ s, FreeWill(s)

✅ · [Choice.lean#freeWillExists_of_chooses](formal/Logos/Choice.lean#L221)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

Assume ∃ s, p, q, Chooses(s, p, q):

    1. witness components ⟨s, p, q, hc⟩  (existential elimination from h)
    2. s  (conjunction conjunct 1: s)
    3. chooses_implies_freeWill hc  (conjunction conjunct 2: chooses_implies_freeWill hc)

    ∴ ∃ s, FreeWill(s)

</details>

</details>

<details>
<summary><b>Adversarial Denial Normal Forms (D1–D8) — Exhaustive Proof of Inevitability</b> (3 machine-checked theorems) — click to expand</summary>

### Adversarial Denial Normal Forms (D1–D8) — Exhaustive Proof of Inevitability

Every conceivable skeptical evasion against the derivation of Free Will has been formally classified and refuted in the kernel:

- **D1 & D2 (Denial of Right/Wrong):** Refuted by core retorsion (`d1_d2_denial_contradicts_core_retorsion`).
- **D3 (Denial of Prescriptivity):** Descriptive truth alone lacks deontic guidance (`d3_descriptive_truth_lacks_deontic_guidance`).
- **D4 (Denial of Agential Address):** Impersonal ought without a subject fails relationality (`d4_impersonal_normativity_fails_relationality`).
- **D5 (Denial of Alternatives):** Monolithic command without opposition lacks choice (`d5_monolithic_command_lacks_opposition`).
- **D6 (Denial of Cognitive Grasp):** Ungraspable command fails agential address (`d6_ungraspable_command_fails_agential_address`).
- **D7 (Denial of Choice from Co-Grasp):** Denying `Chooses` given co-meaning of incompatible alternatives yields a direct formal contradiction (`d7_co_grasp_is_definitionally_choice` → ⊥).
- **D8 (Denial of Free Will from Choice):** Denying `FreeWill` given `Chooses` yields a direct formal contradiction (`d8_choice_is_definitionally_free_will` → ⊥).

D8: Denial of Free Will from Choice — denying FreeWill when Chooses obtains is a direct formal contradiction. Footprint: `{Means, Subject}`.

    Chooses(s, p, q) ∧ ¬FreeWill(s) → False

✅ · [UndeniableNormativeDerivation.lean#d8_choice_is_definitionally_free_will](formal/Logos/UndeniableNormativeDerivation.lean#L275)

The Smallest Local Kernel Theorem: Genuine Normativity entails Choice and Free Will.

    GenuineNormativity s p q → Chooses(s, p, q) ∧ FreeWill(s)

✅ · [UndeniableNormativeDerivation.lean#normative_free_will_local](formal/Logos/UndeniableNormativeDerivation.lean#L287)

The Smallest Existential Kernel Theorem: Constitutive Right/Wrong derives Free Will.

    ConstitutiveRightWrong → ∃ s, FreeWill(s)

✅ · [UndeniableNormativeDerivation.lean#normative_free_will](formal/Logos/UndeniableNormativeDerivation.lean#L294)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

Assume ConstitutiveRightWrong:

    1. witness components ⟨s, p, q, hNorm⟩  (existential elimination from h)
    2. s  (conjunction conjunct 1: s)
    3. (normative_free_will_local hNorm).2  (conjunction conjunct 2: (normative_free_will_local hNorm).2)

    ∴ ∃ s, FreeWill(s)

</details>

</details>

> ➔ **Linear Forward Transition to Step 5 (The Free Subject):** [▲ Discovery · *definitional equivalence [FreeSubject(s) ≡ FreeWill(s)]*]

---

## 5. The Free Subject

A subject is definitionally a free subject iff it possesses free will (`FreeSubject(s) ↔ FreeWill(s)`, Iff.rfl). The recognition runs strictly forward: free will first, the free subject only after it.

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** A definitional manoeuvre — the free subject is bought by a definition, not proven.
> **The reply / the frontier —** Precisely — the 'manoeuvre' *is* the theorem: the equivalence is `Iff.rfl`, which is exactly why nothing can precede free will.
>
> **Machine-Checked Kernel Rebuttal —** [`freeSubject_iff_freeWill`](formal/Logos/Choice.lean#L188) (Footprint: 0 substantive axioms):
> `⊢ FreeSubject s ↔ FreeWill s`
</details>

<details>
<summary>Definitions used in this section (2; 0 new, 2 already shown)</summary>

    ∴ FreeSubject ≡ FreeWill(s) — defined in §3. Genuine Choice.

    ∴ FreeWill ≡ ∃ p, q, Chooses(s, p, q) — defined in §3. Genuine Choice.

</details>

FreeSubject and FreeWill are definitionally equivalent.

    ∴ FreeSubject(s) ↔ FreeWill(s)

✅ · [Choice.lean#freeSubject_iff_freeWill](formal/Logos/Choice.lean#L188)

<details>
<summary>Formal Derivation (1 step, natural deduction, 0 substantive axioms)</summary>

    1. FreeSubject(s) ↔ FreeWill(s)  (definitional equality / reflection)

    ∴ FreeSubject(s) ↔ FreeWill(s)

</details>

<details>
<summary>Supporting Infrastructure — 1 auxiliary theorem(s) beneath this step</summary>

Genuine choice entails a free subject — by definition.

    Chooses(s, p, q) → FreeSubject(s)

✅ · [Choice.lean#chooses_implies_freeSubject](formal/Logos/Choice.lean#L202)

</details>

> ➔ **Linear Forward Transition to Step 6 (Person):** [▲ Discovery · *priced theorem [Person := ThomisticPersonCore; via will_individuation]*]

---

## 6. Person

In the unified Γ ontology, Personhood IS the classical Boethius–Aquinas criterion — an *individual substance of a rational nature*, with *dominion over its own acts* — formalized as the three-conjunct core (`Person(s) := ThomisticPersonCore(s)`); the reduction of the core to free will is the priced theorem `freeWill_implies_person` (0 substantive axioms; the only non-definitional content is the declared VOCAB law `will_individuation`), never an unfolding step. Personhood is therefore not an opaque or unprovable predicate: every Free Subject is an authoritative Person by priced theorem (`free_subject_is_person`), and the exact boundary is machine-checked — a free-willing subject with a non-individuated will is not a person (`SharedWillModel`, footprint `{}`). This is the first point at which the personal subject properly enters the main deduction.

*(Detailed technical proof & model analysis: [investigations/divine-personhood.md](investigations/divine-personhood.md))*

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** A loaded, theological word smuggled into the deduction.
> **The reply / the frontier —** Classical, not novel: the term follows Boethius and Aquinas rather than theological invention. Nothing theological is *assumed*; theology would enter only downstream, in the branches — and is then explicitly bounded by countermodels.
>
> **Machine-Checked Kernel Rebuttal —** [`person_iff_thomisticCore`](formal/Logos/Person.lean#L183) (Footprint: 0 substantive axioms):
> `⊢ Person s ↔ IndividualSubstance s ∧ RationalNature s ∧ DominionOverActs s`
</details>

<details>
<summary>Definitions used in this section (4; 1 new, 3 already shown)</summary>

Thomistic person core: the Boethius–Aquinas conditions of personhood — "individual substance of a rational nature" possessed of dominion over its own acts — formalized through their operative distinguishing features.

    ∴ ThomisticPersonCore ≡ IndividualSubstance(s) ∧ RationalNature(s) ∧ DominionOverActs(s)

📘 · [Person.lean#ThomisticPersonCore](formal/Logos/Person.lean#L93)

    ∴ FreeSubject ≡ FreeWill(s) — defined in §3. Genuine Choice.

    ∴ FreeWill ≡ ∃ p, q, Chooses(s, p, q) — defined in §3. Genuine Choice.

    ∴ Person ≡ ThomisticPersonCore(s) — defined in §3. Genuine Choice.

</details>

Master Theorem: Every Free Subject is a Person — via the priced AC2 theorem.

    FreeSubject(s) → Person(s)

✅ · [Person.lean#free_subject_is_person](formal/Logos/Person.lean#L140)

Master Correspondence: Personhood IS the Thomistic person core — honestly `rfl` now, since that is the definition (AC1′).

    ∴ Person(s) ↔ ThomisticPersonCore(s)

✅ · [Person.lean#person_iff_thomisticCore](formal/Logos/Person.lean#L183)

<details>
<summary>Formal Derivation (1 step, natural deduction, 0 substantive axioms)</summary>

    1. Person(s) ↔ ThomisticPersonCore(s)  (definitional equality / reflection)

    ∴ Person(s) ↔ ThomisticPersonCore(s)

</details>

<details>
<summary>Supporting Infrastructure — 2 auxiliary theorem(s) beneath this step</summary>

Personhood is equivalent to Free Subjecthood — as a theorem resting on the named law `will_individuation`, never `Iff.rfl`.

    ∴ Person(s) ↔ FreeSubject(s)

✅ · [Person.lean#person_iff_freeSubject](formal/Logos/Person.lean#L146)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

    1. fun h => h.2.2  (component witness 1: fun h => h.2.2)
    2. fun h => freeWill_implies_person s h  (component witness 2: fun h => freeWill_implies_person s h)

    ∴ Person(s) ↔ FreeSubject(s)

</details>

Every Person possesses Free Will — projection out of the dominion conjunct.

    Person(s) → FreeWill(s)

✅ · [Person.lean#person_has_free_will](formal/Logos/Person.lean#L157)

</details>

> ➔ **Linear Forward Transition to Step 7 (Personal and Independent Will):** [▲ Discovery · *numerical individuation [will_individuation]*]

---

## 7. Personal and Independent Will

We distinguish carefully between: (1) the subject possessing a Will; (2) the faculty of will (subjectWill s); (3) the act of willing (Wills s p); and (4) the capacity of free choice (FreeWill s). By the principle of numerical individuation (will_individuation), distinct subjects possess numerically distinct faculties of will (subjectWill s₁ ≠ subjectWill s₂). A Person is constitutively a subject with a free will that is genuinely its own, not numerically identical with another subject's will (Person(s) ↔ FreeIndependentWill(s), 0 substantive axioms). The postulate status is machine-witnessed: `will_individuation` is not derivable from the pre-will spine — the hostile model `Subject := Bool`, `Will := Unit`, `subjectWill := fun _ => ()` satisfies the spine yet the law refutes there (`WillIndividuationAudit.will_individuation_not_forced_by_prewill_spine`, `{}`).

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** Two persons could share one will — individuation is not forced.
> **The reply / the frontier —** Individuation is a constitutive meaning-postulate, not a derived construction: `will_individuation` (A18, VOCAB — a **declared** injectivity law `subjectWill s₁ ≠ subjectWill s₂`, not a theorem) assigns each subject its own numerically distinct will-faculty, so two Persons cannot share one will; given that postulate, `Person ↔ FreeIndependentWill` follows with 0 substantive axioms. Its status as a declared postulate — not a theorem — is **kernel-verified**: the hostile model `Subject := Bool`, `Will := Unit`, `subjectWill := fun _ => ()` satisfies the pre-will spine (performative act included), and there the law **arrives at a contradiction** — forcing injectivity demands `subjectWill true ≠ subjectWill false` while both wills are `()`; spine+law is inconsistent, spine alone satisfiable ⇒ the law cannot be derived (`WillIndividuationAudit.will_individuation_not_forced_by_prewill_spine`, footprint `{}`).
>
> **Machine-Checked Kernel Rebuttal —** [`person_iff_freeIndependentWill`](formal/Logos/Person.lean#L166) (Footprint: 0 substantive axioms):
> `⊢ Person s ↔ FreeIndependentWill s`
</details>

<details>
<summary>Definitions used in this section (4; 2 new, 2 already shown)</summary>

Free, Independent Will: a subject endowed with both the capacity of free choice (`FreeWill s`) and an independently individuated volitional faculty (`IndependentWill s`).

    ∴ FreeIndependentWill ≡ FreeWill(s) ∧ IndependentWill(s)

📘 · [Person.lean#FreeIndependentWill](formal/Logos/Person.lean#L60)

Independent Will: the faculty of will possessed by subject s is uniquely its own, numerically distinct from the will of any distinct subject.

    ∴ IndependentWill ≡ ∀ s', s' ≠ s → subjectWill(s') ≠ subjectWill(s)

📘 · [Person.lean#IndependentWill](formal/Logos/Person.lean#L36)

    ∴ Person ≡ ThomisticPersonCore(s) — defined in §3. Genuine Choice.

    ∴ ThomisticPersonCore ≡ IndividualSubstance(s) ∧ RationalNature(s) ∧ DominionOverActs(s) — defined in §6. Person.

</details>

Master Equivalence: Personhood is equivalent to Free, Independent Will.

    ∴ Person(s) ↔ FreeIndependentWill(s)

✅ · [Person.lean#person_iff_freeIndependentWill](formal/Logos/Person.lean#L166)

<details>
<summary>Formal Derivation (6 steps, natural deduction, 0 substantive axioms)</summary>

    1. fun h => ⟨h.2.2  (component witness 1: fun h => ⟨h.2.2)
    2. h.1⟩  (component witness 2: h.1⟩)
    3. fun ⟨hFW  (component witness 3: fun ⟨hFW)
    4. hI⟩ => ⟨hI  (component witness 4: hI⟩ => ⟨hI)
    5. freeWill_implies_rationalNature s hFW  (component witness 5: freeWill_implies_rationalNature s hFW)
    6. hFW⟩  (component witness 6: hFW⟩)

    ∴ Person(s) ↔ FreeIndependentWill(s)

</details>

<details>
<summary>Supporting Infrastructure — 3 auxiliary theorem(s) beneath this step</summary>

Numerical individuation guarantees that every subject possesses an independent will.

    ∴ IndependentWill(s)

✅ · [Person.lean#independent_will_of_subject](formal/Logos/Person.lean#L65)

Master Theorem: Every Person possesses a Free, Independent Will.

    Person(s) → FreeIndependentWill(s)

✅ · [Person.lean#person_has_free_independent_will](formal/Logos/Person.lean#L172)

Master Equivalence: free, independent will is equivalent to the Thomistic person core.

    ∴ FreeIndependentWill(s) ↔ ThomisticPersonCore(s)

✅ · [Person.lean#freeIndependentWill_iff_thomisticCore](formal/Logos/Person.lean#L111)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

    1. freeIndependentWill_implies_thomisticCore s  (component witness 1: freeIndependentWill_implies_thomisticCore s)
    2. thomisticCore_implies_freeIndependentWill s  (component witness 2: thomisticCore_implies_freeIndependentWill s)

    ∴ FreeIndependentWill(s) ↔ ThomisticPersonCore(s)

</details>

</details>

> ➔ **Linear Forward Transition to Step 8 (Personal Agency as Ontological Ground of Normativity):** [▼ Ontological Grounding · *ONTOLOGICAL GROUNDING ARROW [Grounding ≠ Identity]*]

---

## 8. Personal Agency as Ontological Ground of Normativity

The complete logical shape is a strictly forward implication chain: A₀ ⇒ A₁ ⇒ ... ⇒ P ⇒ G. Every implication has a true antecedent once the previous step has been established: from the starting normative datum (A₀), through genuine choice and free will, to the Person (P), and finally to the proposition (G) that this Person grounds the original normative datum.

### The Four Critical Distinctions
1. **Discovery of a personal ground (forward proof):** The deductive proof runs forward via successive modus ponens: A₀ ⇒ Choice ⇒ Free Will ⇒ Free Subject ⇒ Person ⇒ G. Discovery identifies a personal ground from the normative datum.
2. **Grounding in a personal kind/type (derived ontological proposition):** Objective Right/Wrong has such a necessary ontological grounding. The derived subject s is the formal index/witness satisfying the universal grounding specification (`dependence: ∀ s', RightWrong s' → Person s'`). **The argument does not identify a particular contingent individual as the creator of Right and Wrong.**
3. **Separation from specific divine personal identity:** Establishing that the ground of normativity is personal in kind is distinct from identifying which particular divine person(s), if any, instantiate that ground. That further question belongs to the downstream theological and monotheistic branches (Branches A and B), not to the initial derivation of the personal ground-type.
4. **Grounding correctness about reality is not producing reality:** The claim is that the personal ground is the ontological basis of the objective normative/truth order governing whether judgments about what is the case are correct or incorrect. It is NOT a claim that the personal ground causally creates every existent, makes evil exist, or morally legitimizes anything that exists. If an apple exists, 'an apple exists' is objectively correct; if evil exists, 'evil exists' is objectively correct — neither assertion evaluates the apple or evil morally, and neither implies that the ground of truth/correctness caused them. Entity-level `GroundOfReality` (Claim E) stays annotated-only.

Grounding is derived directly from Personhood itself without Act (Grounding from Personhood). Grounding is not causal generation and not identity (Grounding ≠ Identity): identifying Ought with current volition collapses normative violation (will_identity_collapses_normativity). Every step in the chain—including the step from Person to 'Person grounds Right/Wrong'—is derived without arbitrary grounding axioms, PSR smuggling, or reliance on Act.

*(Detailed technical proof & model analysis: [investigations/grounding.md](investigations/grounding.md))*

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** Principle-of-Sufficient-Reason smuggling: this makes the Person (or the argument) the causal creator of morality.
> **The reply / the frontier —** Grounding ≠ identity and ≠ causation — see distinctions 2 and 4: Right/Wrong's correctness-order has a ground *personal in kind*, not a particular person causally producing existents or rightness. The bare ought survives the impersonal model, the personal ground is forced within the normative order, and model_b_separation marks exactly what the antecedent does and does not reach.
>
> **Machine-Checked Kernel Rebuttal —** [`will_identity_collapses_normativity`](formal/Logos/PersonalNormativeGround.lean#L347) (Footprint: 0 substantive axioms):
> `⊢ Wills s p = Ought s p → NormativeViolation s p → ⊥`
</details>

<details>
<summary>Definitions used in this section (6; 3 new, 3 already shown)</summary>

GroundedNormativePolarity: Normative polarity is ontologically grounded in a subject endowed with free, independent will, witnessing the personal ontological ground-type.

    ∴ GroundedNormativePolarity ≡ FreeIndependentWill(s) ∧ GroundsRightWrong s

📘 · [PersonalNormativeGround.lean#GroundedNormativePolarity](formal/Logos/PersonalNormativeGround.lean#L317)

GroundsRightWrong: Objective Right/Wrong is ontologically grounded in an agential basis: the witness s co-means incompatible alternatives (`∃ p q, Chooses s p q`), supplying the ontological ground-type required by normative polarity.

    ∴ structure GroundsRightWrong (s : Subject) : Prop where

📘 · [PersonalNormativeGround.lean#GroundsRightWrong](formal/Logos/PersonalNormativeGround.lean#L288)

Right/Wrong Distinction at contents p and q for subject s: The subject is addressed by an objective deontic opposition between Right (p) and Wrong (q).

    ∴ RightWrongAt ≡ GenuineNormativity s p q

📘 · [PersonalNormativeGround.lean#RightWrongAt](formal/Logos/PersonalNormativeGround.lean#L153)

    ∴ Chooses ≡ Means(s, p) ∧ Means(s, q) ∧ Incompatible(p, q) — first shown in §3. Genuine Choice.

    ∴ FreeWill ≡ ∃ p, q, Chooses(s, p, q) — defined in §3. Genuine Choice.

    ∴ Person ≡ ThomisticPersonCore(s) — defined in §3. Genuine Choice.

</details>

Direct Derivation: The derived subject s instantiates the personal ground of the normative datum.

    RightWrongAt(s, p, q) → Person(s) ∧ GroundsRightWrong s

✅ · [PersonalNormativeGround.lean#person_grounds_original_normative_datum](formal/Logos/PersonalNormativeGround.lean#L607)

Master Grounding Theorem from Personhood (Historical Compatibility Name): Personhood supplies the ontological ground-type required by the normative order — now as a derived theorem routing through free will, not as a field projection.

    Person(s) → GroundsRightWrong s

✅ · [PersonalNormativeGround.lean#person_grounds_normative_polarity](formal/Logos/PersonalNormativeGround.lean#L529)

<details>
<summary>Supporting Infrastructure — 3 auxiliary theorem(s) beneath this step</summary>

Master Realization Theorem: Any Person realizes GroundedNormativePolarity, showing that normative polarity is grounded in a personal ontological basis.

    Person(s) → GroundedNormativePolarity(s)

✅ · [PersonalNormativeGround.lean#person_realizes_grounded_polarity](formal/Logos/PersonalNormativeGround.lean#L546)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

Assume Person(s):

    1. FreeIndependentWill(s)  (modus ponens via (person_iff_freeIndependentWill)
    2. hFW  (conjunction conjunct 1: hFW)
    3. freeWill_grounds_right_wrong s hFW.1  (conjunction conjunct 2: freeWill_grounds_right_wrong s hFW.1)

    ∴ GroundedNormativePolarity(s)

</details>

The Non-Reversal Architectural Principle: 1. Deductive Discovery runs forward: RightWrongAt s p q ⇒ ... ⇒ Person s ⇒ GroundsRightWrong s.

    ∴ (RightWrongAt(s, p, q) → Person(s) ∧ GroundsRightWrong s) ∧ (Person(s) → GroundsRightWrong s)

✅ · [PersonalNormativeGround.lean#non_reversal_discovery_and_grounding](formal/Logos/PersonalNormativeGround.lean#L651)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

    1. fun h => forward_modus_ponens_derivation s p q h  (component witness 1: fun h => forward_modus_ponens_derivation s p q h)
    2. fun hp => freeWill_grounds_right_wrong s (Logos.Person.person_has_free_will s hp)  (component witness 2: fun hp => freeWill_grounds_right_wrong s (Logos.Person.person_has_free_will s hp))

    ∴ (RightWrongAt(s, p, q) → Person(s) ∧ GroundsRightWrong s) ∧ (Person(s) → GroundsRightWrong s)

</details>

Non-Circularity Architectural Theorem: The retorsive discovery proof of Free Will (`indubitable_normative_free_will`) does NOT require or depend upon any grounding bridge.

    GenuineNormativity s p q → Chooses(s, p, q) ∧ FreeWill(s)

✅ · [PersonalNormativeGround.lean#discovery_independent_of_grounding](formal/Logos/PersonalNormativeGround.lean#L737)

</details>

<details>
<summary>Obstruction / Formal Boundary: `model_b_separation`</summary>

### Obstruction / Formal Boundary: `model_b_separation`

Theorem: Separation Theorem from Model B.

    model_b_separation ⇏ Independence

🧱 model_b_separation ⇏ Independence · [PersonalNormativeGround.lean#model_b_separation](formal/Logos/PersonalNormativeGround.lean#L824)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

Assume ModelBSignature:

    1. witness components ⟨s, hFW⟩  (existential elimination from M.free_subject_exists)
    2. witness tuple ⟨⟨s, hFW⟩  (existential/conjunction refinement with ⟨s, hFW)
    3. assume hAll  (hypothesis assumption for conditional/reductio proof)

    ∴ (∃ s,.Subject, M.FreeIndependentWill(s)) ∧ ¬(∀ s,.Subject, M.FreeIndependentWill(s) → M.GroundProp (M.EntityOf(s)) M.Polarity)

</details>

</details>

> ➔ **Linear Forward Transition to Step 9 (Necessary Truth):** [➔ Continuation · *modal continuation from normative truth*]

---

## 9. Necessary Truth

After normative reality and its personal grounding have been established, §9 reaches Necessary Truth (∃ τ, □ τ) as the *logical* continuation of the objective logical order — `Semantics.strongTruthExists` (C59, `{CL}`), the classical meta-logic resident in Core/Semantics. This world-level modality is NOT derived from the normative chain: the normative world-level continuation is the separate, stronger claim `NecessaryNormativeOrder : ∀ w, NormativeOrderAt w` (anchored in `Core.rightWrongDistinction`), and no theorem states `NecessaryNormativeOrder → ∃ τ, □ τ`. The two continuations are kept apart.

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** Quietly assumes modal metaphysics — necessity is a contested fragment, not a consequence.
> **The reply / the frontier —** The world-level necessity of §9 is the *logical* continuation — classical meta-logic resident in Core/Semantics (`Semantics.strongTruthExists`, C59, footprint `{CL}`) — not a theorem derived from the normative chain. The normative world-level continuation is recorded separately (`NecessaryNormativeOrder : ∀ w, NormativeOrderAt w`) and is never claimed to entail `∃ τ, □ τ`. Neither continuation presupposes an ungrounded modal metaphysics.
>
> **Machine-Checked Kernel Rebuttal —** [`strongTruthExists`](formal/Logos/Semantics.lean#L113) (Footprint: 0 substantive axioms):
> `⊢ ∃ τ, □ τ`
</details>

Step 1: Strong Necessary Truth exists (resident in the Core/Semantics machinery).

    ∴ ∃ τ, □ τ

✅ · [NecessaryPersonalGround.lean#step1_necessary_truth_exists](formal/Logos/NecessaryPersonalGround.lean#L204)

> ➔ **Linear Forward Transition to Step 10 (Constructive Personal Ground):** [▲ Discovery · *constructive discovery [ObjectiveNormativity ⇒ Person]*]

---

## 10. Constructive Personal Ground

The dependence `RightWrong ⇒ Person` was proved in §8 via the priced discovery theorem (the only non-definitional content is the VOCAB law `will_individuation`). Its constructive form needs no grounding axiom: `ObjectiveNormativity ⇒ Person` is discovery, `FreeWill ⇒ GroundsRightWrong` is the definitional agential route, and ground-personalness is a priced theorem — never a record field.

The headline — 'the Person supports the reality of Right' — asserts that the RightWrong-reality, the objective correctness structure governing judgments about what is the case, has a personal ontological ground-type. The four distinctions of §8 apply unchanged; in particular, grounding the correctness order is not producing reality (§8, distinction 4).

*(Detailed technical proof & model analysis: [investigations/divine-personhood.md](investigations/divine-personhood.md))*

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** You still quietly pick a contingent author of morality — some particular person who happens to ground Right/Wrong.
> **The reply / the frontier —** The indexing encodes *dependence without nomination*: RightWrong is indexed by a personal kind/type, not by any arbitrary contingent individual — objective Normativity ⇒ Person is discovery, Person ⇒ Right/Wrong is the typed index. And Branch C below marks exactly what is NOT forced: trinity, contingent creation, and incarnation all remain countermodel frontiers (⇏).
>
> **Machine-Checked Kernel Rebuttal —** [`discover_person`](formal/Logos/PersonalNormativeGround.lean#L106) (Footprint: 0 substantive axioms):
> `⊢ ObjectiveNormativity → Σ' p, RightWrong p`
</details>

<details>
<summary>Definitions used in this section (10; 3 new, 7 already shown)</summary>

The Invariant Necessity of the Objective Normative Order: holds across all possible worlds via Logos.Necessity.Necessity.

    ∴ NecessaryNormativeOrder ≡ ∀ w, NormativeOrderAt(w)

📘 · [NecessaryPersonalGround.lean#NecessaryNormativeOrder](formal/Logos/NecessaryPersonalGround.lean#L105)

Objective Normativity: the existence of a person whose judgment carries Right/Wrong.

    ∴ ObjectiveNormativity ≡ ∃ p, RightWrong(p)

📘 · [PersonalNormativeGround.lean#ObjectiveNormativity](formal/Logos/PersonalNormativeGround.lean#L100)

Right and Wrong distinction indexed by Person: The normative distinction is genuinely addressed to and held by the person.

    ∴ RightWrong ≡ ∃ a, b, GenuineNormativity p.subject a b

📘 · [PersonalNormativeGround.lean#RightWrong](formal/Logos/PersonalNormativeGround.lean#L96)

    ∴ ClaimsCorrect ≡ Act s p ∧ Means(s, Correct s p) — defined in §1. Objective Right and Wrong.

    ∴ EstablishedRightWrong ≡ ¬N_T ∧ ¬N_F — first shown in §1. Objective Right and Wrong.

    ∴ structure GroundsRightWrong (s : Subject) : Prop where — defined in §8. Personal Agency as Ontological Ground of Normativity.

    ∴ IsFalse ≡ ¬T(p) — defined in §2. Ought and Normative Polarity.

    ∴ NoRight ≡ ¬NormativeRightExists — defined in §1. Objective Right and Wrong.

    ∴ Person ≡ ThomisticPersonCore(s) — defined in §3. Genuine Choice.

    ∴ T ≡ p — defined in §2. Ought and Normative Polarity.

</details>

The ontology in one universal: wherever Right/Wrong is real, its ground-type is personal (the 'simple thing'). The elaborated `GroundsRightWrong` record is its record-form (DEFINITIONAL).

    ∴ RightWrong(s) → Person(s)

✅ · [PersonalGroundOfReality.lean#personal_ground_of_right_wrong](formal/Logos/PersonalGroundOfReality.lean#L100)

Constructive direction of discovery: Objective Normativity ⇒ Person.

    ∴ ObjectiveNormativity → ∃ p, RightWrong(p)

✅ · [PersonalNormativeGround.lean#discover_person](formal/Logos/PersonalNormativeGround.lean#L106)

<details>
<summary>Formal Derivation (1 step, natural deduction, 0 substantive axioms)</summary>

    1. assume h  (hypothesis assumption for conditional/reductio proof)

    ∴ ObjectiveNormativity → ∃ p, RightWrong(p)

</details>

HEADLINE — THE PERSON SUPPORTS THE REALITY OF RIGHT.

    ∴ (¬∃ s, ClaimsCorrect(s, NoRight) ∧ NoRight) ∧ EstablishedRightWrong ∧ (∀ p, T(p) ∨ IsFalse(p)) ∧ NecessaryNormativeOrder ∧ (∀ s, RightWrong(s) → Person(s)) ∧ (∀ s, Person(s) → GroundsRightWrong s)

✅ · [PersonalGroundOfReality.lean#the_person_supports_the_reality_of_right](formal/Logos/PersonalGroundOfReality.lean#L153)

<details>
<summary>Formal Derivation (6 steps, natural deduction, 0 substantive axioms)</summary>

    1. deny_right_self_contradicts  (conjunction conjunct 1: deny_right_self_contradicts)
    2. Logos.Core.rightWrongDistinction  (conjunction conjunct 2: Logos.Core.rightWrongDistinction)
    3. Logos.Core.bivalence  (conjunction conjunct 3: Logos.Core.bivalence)
    4. necessary_normative_order  (conjunction conjunct 4: necessary_normative_order)
    5. normative_datum_forces_person  (conjunction conjunct 5: normative_datum_forces_person)
    6. person_grounds_normative_order  (conjunction conjunct 6: person_grounds_normative_order)

    ∴ (¬∃ s, ClaimsCorrect(s, NoRight) ∧ NoRight) ∧ EstablishedRightWrong ∧ (∀ p, T(p) ∨ IsFalse(p)) ∧ NecessaryNormativeOrder ∧ (∀ s, RightWrong(s) → Person(s)) ∧ (∀ s, Person(s) → GroundsRightWrong s)

</details>

<details>
<summary>Supporting Infrastructure — 2 auxiliary theorem(s) beneath this step</summary>

Objective Normativity holds from any agential normative address.

    ∃ s, a, b, GenuineNormativity s a b → ObjectiveNormativity

✅ · [PersonalNormativeGround.lean#objective_normativity_holds](formal/Logos/PersonalNormativeGround.lean#L132)

<details>
<summary>Formal Derivation (6 steps, natural deduction, 0 substantive axioms)</summary>

Assume ∃ s, a, b, GenuineNormativity s a b:

    1. witness components ⟨s, a, b, h⟩  (existential elimination from hDatum)
    2. s  (conjunction conjunct 1: s)
    3. free_subject_is_person s (Logos.IndubitableNormativeFreeWill.indubitable_normative_free_will h).2  (conjunction conjunct 2: free_subject_is_person s (Logos.IndubitableNormativeFreeWill.indubitable_normative_free_will h).2)
    4. a  (conjunction conjunct 3: a)
    5. b  (conjunction conjunct 4: b)
    6. h  (conjunction conjunct 5: h)

    ∴ ObjectiveNormativity

</details>

HEADLINE (instance form, datum-guarded). The personal ontological ground is the necessary ground of the objective normative/truth order governing judgments about Γ-reality (Right/Wrong, truth/falsity, Ought/OughtNot under TruthNorm): it grounds the correctness of propositions *about* what is the case, not the fact of what exists.

    Person(s) → Person(s) ∧ GroundsRightWrong s ∧ NecessaryNormativeOrder

✅ · [PersonalGroundOfReality.lean#person_yields_personal_grounding_of_reality](formal/Logos/PersonalGroundOfReality.lean#L199)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

Assume Person(s):

    1. hPerson  (component witness 1: hPerson)
    2. freeWill_grounds_right_wrong s (Logos.Person.person_has_free_will s hPerson)  (component witness 2: freeWill_grounds_right_wrong s (Logos.Person.person_has_free_will s hPerson))
    3. necessary_normative_order  (component witness 3: necessary_normative_order)

    ∴ Person(s) ∧ GroundsRightWrong s ∧ NecessaryNormativeOrder

</details>

</details>

### Branch A: Necessity and Eternity of the Divine Being (Ground)

Live theorem: the ground is world-rigid (`NecessaryEntity Entity.ofGround`, `∀ w, ExistsAt w .ofGround`, definitional `EntityExistsAt w .ofGround := True`, footprint `{Means, Subject}`), **everlasting**, **atemporal**, and possesses **Canonical Aseity** (`conditional_canonical_aseity`, `{Means, Subject}`: `¬ ∃ g, ExternalGrounding g .ofGround`). Claim E is the *non-hypostatic* pairing (`∃ g s, NecessaryEntity g ∧ NecessaryGroundOfReality g ∧ Person s ∧ GroundsRightWrong s`): entity-necessity conjunct PROVEN; personal-kind conjunct honestly `{AxTwoSubjects, Means, Subject, Will, subjectWill}` (PROVEN↑ under META `AxTwoSubjects`). Hypostatic identity, a 'necessary Person', Trinity and monotheism are NOT claimed — `ofGround_ne_ofSubject` blocks the identity line.

HEADLINE — the necessary ground of reality exists: `Entity.ofGround` is a necessary entity and the ontological ground of reality.

    ∴ NecessaryGroundOfReality Entity.ofGround

✅ · [NecessityEternity.lean#ofGround_necessary_ground_of_reality](formal/Logos/NecessityEternity.lean#L153)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

    1. ofGround_necessary  (component witness 1: ofGround_necessary)
    2. ofGround_ground_of_reality  (component witness 2: ofGround_ground_of_reality)

    ∴ NecessaryGroundOfReality Entity.ofGround

</details>

### Branch B: Divine Uniqueness and Monotheism

Two different claims were being carried under one label, and only one of them is still open. (1) UNIQUENESS OF THE UNIVERSAL GROUND is now machine-checked: `Logos.FoundationalUnicity.exactly_one_universal_modal_ground` (C320) proves that exactly one universal modal ground exists, with existence unconditional and uniqueness under the single named hypothesis of frontier row F15. (2) PERSON-LEVEL MONOTHEISM — one God as numerically one Person, and its compatibility with three Persons — remains DEFERRED: it needs the person bridge C228, which is BLOCKED, so `monotheism_of_god_and_uniqueness` and `monotheism_compatible_with_trinity` are still out of the live kernel and no compiled declaration exists for either. The deferral of this branch is therefore NARROWED to claim (2).

> ⏸ **DEFERRED, NARROWED (2026-09-27)** — the ground-unicity half is no longer deferred: C320 (`Logos.FoundationalUnicity.exactly_one_universal_modal_ground`) proves exactly one universal modal ground exists, existence unconditionally and uniqueness under frontier hypothesis F15 — now the declared axiom `SemanticFinitude` (C388, `Tag: VOCAB`, the 27th), which C389 consumes unconditionally. What remains deferred is the Person-level claim — one God as numerically one Person, and trinity-compatibility — which needs the person bridge C228 (`BLOCKED`); no compiled declaration exists for `monotheism_of_god_and_uniqueness` or `monotheism_compatible_with_trinity`, and the generic non-collapse of unicity into a solitary monad is already checked at C212 (`{}`).

### Branch C: What This Does Not Yet Prove (Theological Frontiers)

The power of a formal system lies as much in what it refrains from claiming as in what it proves. The deduction strictly distinguishes established theorems from open frontiers. Machine-checked independence countermodels prove that preceding theory does NOT logically entail: (1) The Trinitarian structure of Three Divine Persons; (2) Contingent creation of a temporal cosmos; or (3) The Incarnation. These remain independent theological frontiers — for the deep technical proofs, countermodel models, and exhaustive dependency matrices, consult the Further Investigations catalogue at the end of this document.

*(Detailed technical proof & model analysis: [investigations/countermodels.md](investigations/countermodels.md))*

<details>
<summary>Obstruction / Formal Boundary: `preceding_theory_not_entails_trinity`</summary>

Binitarian Separation Model (Toy Cardinality Model over Bool): Demonstrates that an unconstrained 2-element domain (`Subj := Bool`) cannot accommodate three distinct personal centers by pure cardinality (Pigeonhole Principle).

    preceding_theory ⇏ trinity

🧱 preceding_theory ⇏ trinity · [ConditionalTheology.lean#preceding_theory_not_entails_trinity](formal/Logos/ConditionalTheology.lean#L336)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

    1. witness tuple ⟨Bool, Unit, fun _ _ _ => True, fun _ _ => True, fun _ _ => True, ?_⟩  (existential/conjunction refinement with Bool, Unit, fun _ _ _ => True, fun _ _ => True, fun _ _ => True, ?_)
    2. witness tuple ⟨⟨true, false, fun h => by cases h⟩  (existential/conjunction refinement with ⟨true, false, fun h => by cases h)
    3. vacuous contradiction on empty p1  (elimination of empty type p1 (→ ⊥))

    ∴ ∃ Subj, Ent, Chooses, Loves, Divine, -- Plurality of distinct persons (∃ s₁, s₂, s₁ ≠ s₂) ∧ -- Free agency (∀ s, ∃ p, q, Chooses(s, p, q)) ∧ -- Mutual love (∀ s₁, s₂, s₁ ≠ s₂ → Loves(s₁, s₂)) ∧ -- Common divine ground (∃ e,(s₁ s₂ : Subj), s₁ ≠ s₂ ∧ Divine s₁ e ∧ Divine s₂ e) ∧ -- Exactly two subjects: impossible to satisfy three mutually distinct centers ¬(∃ _t, True)

</details>

</details>

<details>
<summary>Obstruction / Formal Boundary: `necessary_ground_not_entails_contingent_creation`</summary>

**Separation Model (rebuilt on a populated world).** A necessary divine ground exists, grounds every content, and coexists with a contingent subject that is not *its* creation: necessary reality does NOT entail creation.

    necessary_ground ⇏ contingent_creation

🧱 necessary_ground ⇏ contingent_creation · [ConditionalTheology.lean#necessary_ground_not_entails_contingent_creation](formal/Logos/ConditionalTheology.lean#L616)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

    1. Nonempty (CreationRecord populatedCreationWorld)  (from )
    2. witness components ⟨c⟩  (existential elimination from hRec)

    ∴ ¬(∀ (Subj Ent World : Type), GroundEntailsCreation(Subj, Ent, World))

</details>

</details>

<details>
<summary>Obstruction / Formal Boundary: `preceding_theory_not_entails_incarnation`</summary>

Unincarnate Hostile Model: The existing theory (necessary divine ground, human agency, free will) is completely consistent with God remaining purely transcendent and unincarnate.

    preceding_theory ⇏ incarnation

🧱 preceding_theory ⇏ incarnation · [ConditionalTheology.lean#preceding_theory_not_entails_incarnation](formal/Logos/ConditionalTheology.lean#L380)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

    1. witness tuple ⟨Bool, Bool, Unit, fun _ _ _ => True, fun s n => s = n, ?_⟩  (existential/conjunction refinement with Bool, Bool, Unit, fun _ _ _ => True, fun s n => s = n, ?_)
    2. witness tuple ⟨⟨true, false, fun h => by cases h⟩  (existential/conjunction refinement with ⟨true, false, fun h => by cases h)

    ∴ ∃ Subj, Nature, _Ent, Chooses, HasNature, -- Distinct divine and human natures exist (∃ d, h, d ≠ h) ∧ -- Divine reality and human choosers exist (∃ s, p, q, Chooses(s, p, q)) ∧ -- Zero subjects combine both natures ¬(∃ _i, True)

</details>

</details>

---

## Formal Frontiers

The frontier is the set of claims that are not currently derived. An **OPEN** claim has no kernel node (blocked, deferred, answered, or a missing lemma) and is listed below. A **COUNTERMODEL** claim is a proposed inference that a hostile model refutes: the step is *withdrawn*, and what survives is recorded in Appendix C.2. The premier open frontier is deontic teleology (F2); moral good (F3) is no longer open — the faithful model `M_amoral` machine-separates practical bindingness from epistemic agential normativity (`MoralFrontierAudit.epistemic_normativity_without_practical_obligation`, C175, `{}`), making F3 a countermodel frontier, not a gap. The *positive* moral pole is separately obtained under one disclosed, priced META bridge (`Value.AxBenevolentBearingObtains`, C177 → `moral_good_obtains`, C178); the bare value layer is machine-proven empty (C176), so the bridge is a paid commitment rather than a hidden derivation, and the negative pole `Evil` remains a declared SEM datum (its fair reading needs a parallel harm bridge, not declared).

* **`C78`** (`T7 — `) — Contingent ground is retired: manufactured witness destroyed under hostile semantics.
* **`C79`** (`T7 — `) — Ultimate ground existence is blocked: infinite descending chains have no ultimate element without a well-foundedness axiom.
* **`C87`** (`T7 — `) — Origin necessity is retired: manufactured origin witness destroyed.
* **`C88`** (`T7 — `) — Transcendental quantifier swap is retired: the manufactured origin quantifier swap was destroyed under hostile semantics; the declaration is absent from the live kernel.
* **`C89`** (`T7 — `) — Ultimate ground by initiation is blocked: non-entailed without well-foundedness.
* **`C90`** (`T8 — `) — Personal ultimate ground is blocked: ultimate grounding does not entail personal nature.
* **`F2`** (`§21 teleology (`Ought → Goal`) — `) — Deontic teleology is deferred: how norms point at goals is not yet derived.
* **`F6`** (`§28 Trinity — `) — The Trinity is deferred: no argument exists yet.
* **`F1bUncond`** (`§15 unconditional `∃ s, FreeWill s` — rejectedHornCoMeant`) — The precise missing resource (F1b, BLOCKED): one subject co-meaning a content and its negation — the same-subject dual meaning-act.
* **`OpenBridgeNormativity`** (`§0.10 positive bridge bivalence → `GenuineNormativity` (`∀ s p, Judge s p → GenuineNormativity s p (¬p)` or stance-antecedent variant) — `) — The positive bivalence→normativity bridge (∀ s p, Judge s p → GenuineNormativity s p (¬p), or stand-antecedent variant) is BLOCKED: bivalence alone is insufficient (M_inanimate, C167); the weak-voice route C106 closes it at SEM cost AxJudicativeBipolarity (independent via M_opaque, dispensable); the axiom-free full-stance route C164/C165 needs the stance datum; unconditional ¬NoGN is not derivable.
* **`C69`** (`§15/F1b — `) — Free will of origin is retired: manufactured constructor split destroyed.
* **`C70`** (`§15/F1b — `) — Posited content non-freedom is retired: manufactured witness destroyed.
* **`C71`** (`§15/F1b — `) — Origin freedom denial self-refuting is retired: manufactured witness destroyed.
* **`C72`** (`§15/F1b — `) — Judge is free is retired: act does not entail free will; `judge_commits` yields only the choice field.
* **`C73`** (`P5/P7 — `) — Plurality without bridges is blocked: unit countermodel settles that 1 act does not entail plurality; requires AxTwoSubjects.
* **`C75`** (`P7 — `) — Propositional personhood is blocked: content existence does not entail personhood.
* **`C76`** (`P8 — `) — Canonical rigid love is retired: plurality does not entail love without substantive relational bridges.
* **`C77`** (`P5/P8 — `) — Conditional necessary-person claim is deferred: the theorem Love.necessaryPersonExists_conditional was removed from the live kernel (commit ae7f4bd); retained as annotated conditional surface only, never a derived divine Person.
* **`C92`** (`P8/§27 — `) — Conditional necessary-entity claim is deferred: the theorem Love.necessary_entity_exists_conditional was removed from the live kernel (commit ae7f4bd); retained as annotated conditional surface only.
* **`C64`** (`§1 — `) — Movement not transfer is retired: initiation constructor evaluation excised.
* **`C65`** (`§1/T5 — `) — Person iff originates is retired: manufactured initiation identity excised.
* **`C66`** (`§1 fnd — `) — Cogito as initiation is retired: manufactured initiation witness excised.
* **`C67`** (`§1 fnd — `) — Denial of initiation self-refuting is retired: manufactured witness excised.
* **`C80`** (`§1 — `) — Posited content deterministic transfer is retired: constructor evaluation excised.
* **`C81`** (`§1 — `) — Origin branching is retired: constructor evaluation excised.
* **`C82`** (`§1/§12 — `) — Origin initiating person is retired: constructor evaluation excised.
* **`F8`** (`Trinity — `) — The Trinity is not attempted.
* **`C228`** (`§24a/§29 — PersonalNormativeGround.normative_ground_is_personal`) — BLOCKED (AC5 unmet, D1′ recorded not executed): any entity that grounds Right/Wrong is a Personal Entity — but the personalness is a THREE-STEP FIELD PROJECTION, not a free-standing theorem: `grounds_normativity` supplies the `GenericGroundingRelation`…
* **`F10`** (`§15 causal/creative omnipotence ("can bring X about", not "is present where X obtains") — `) — Causal (creative) omnipotence — the power to BRING a state of affairs about, as against being present where it obtains — is BLOCKED, and the prose disclaimer is retained for this causal sense alone, since the non-contradictory sense of omnipotence is now PROVEN (C242, the ground operates every satisfiable state of affairs, and C251, that scope domain is non-empty and contradiction-free). Γ declares no entity-level production relation: its only initiation relation, Agency.Initiates : Subject → State → State → Prop → Prop, is subject-indexed, and Entity.ofGround is provably not a subject correlate (ofGround_ne_ofSubject), so the ground cannot instantiate it at all. The closest relation Γ has is explanatory containment (GroundsEntity), and exhaustive_scope_without_operative_scope already machine-checks that an exhaustive scope does not entail an operative one, so the causal sense must not be weakened to it. Two exact statements are missing, in this order: (1) the vocabulary, a production relation Produces : Entity → World → Form → Prop; and (2) the derivation, that the ground produces every satisfiable state of affairs.
* **`F11`** (`§30 bare rejected horn: the co-signification of the rejected implication follows from the existence of a meaning-act alone — `) — The bare rejected horn is BLOCKED, and now nameable: Logos.AsieticChoice.bareRejectedHornCoMeant : (∃ s : Subject, ∃ p : Prop, Means s p) → ∃ s : Subject, ∃ p : Prop, Means s p ∧ Means s (¬ p). Every non-circular route in Gamma to Means s (¬ p) is Act-gated — AxJudicativeBipolarity (premise ClaimsCorrect s p), AxActPolarity and AxIntentionalChoice (premise Act s p, and its q is arbitrary, never ¬ p), ClaimsNormativeCorrectness (premise Act s p) — while Act s p := Means s p ∧ ∃ w w', Initiates s w w' p, and no axiom of Gamma supplies an Initiates witness. So the single upstream gap is the Initiates-existence gap, NOT horn-saturation. Two discharges do work and both name their premise: derives_rejectedHornCoMeant from a correctness-judgment, and retorsion_implies_rejectedHornCoMeant from the retorsion event. The bare form is not merely unproved but REFUTED — singleContentModelRefutesBareRejectedHorn exhibits a model of the meaning vocabulary in which the antecedent holds and the consequent does not — so the blocker is a sentence false in a model, not an artefact of an unsuccessful search. Footprint and status are orthogonal: the {Means, Subject} marker on the definition is what it depends on, BLOCKED is that it is not discharged.
* **`F12`** (`§32 the missing justification for ◈ `asietyFreedom_ofGroundFreedom`: the ground's being the ground of *freedom* follows from Γ's grounding vocabulary — `) — The justification for the ASIETY-FREEDOM stipulation is BLOCKED, in two halves that must both be closed. (1) MISSING VOCABULARY: a substantive grounding relation relating Entity.ofGround to the normative content of a subject. Gamma declares none. GroundsEntity is vacuous on the ground side, because EntityMeans Entity.ofGround p reduces to True; and the only non-vacuous grounding predicate, GroundsRightWrong, is definitionally ∃ p q, Chooses s p q (C168) — already free will, so using it as the antecedent would be circular. The substantive relation stays BLOCKED at C228, with its named lemma verbatim. (2) MISSING DERIVATION: from such a relation plus Asiety (EntityOf s), derive TrueChoice s p q at every incompatible pair, not merely the witnessing pair. C299 groundingCannotDeliverTrueChoice (footprint {}) is the machine-checked reason this cannot be discharged from a premise of containment shape: it grants the full premise — a ground of total meaning-capacity, forall v, M g v, and the containment premise at every entity, forall e v, M e v -> M g v, which is GroundsEntity verbatim — and still denies the conclusion at the same pair. So the corpus records both facts about the bridge at once: we chose to assert it, and we cannot justify it. Note the scope limit: C299 covers relations of containment shape only, so a relation of some other shape remains open work, which makes the block serious rather than permanent.
* **`F13`** (`§32 the Creator-sharing existence claim: the ground's shared freedom reaches **someone** — `) — The Creator-sharing existence claim is BLOCKED, and refuted as derivable rather than open. The obligation is now nameable, following the F11 precedent: Logos.AsietyFreedom.groundFreedomSharedWithSomeone : Prop := ∃ s, AsietyFreeWill s, footprint {Means, Subject}. Sharing the ground's freedom with us contains an existence claim, and Gamma cannot supply it: Core.rightWrongDistinction is a fact about contents, quantifies over no Subject, and is compatible with a meaning-vocabulary in which no subject means anything — that is C294, whose content-vocabulary countermodel shows the antecedent holding with no subject to be shared with. The unconditional route therefore still costs AxTwoSubjects (Tag: META). Naming this advances nothing; it is recorded so that the batch's strongest negative result is a citable frontier row rather than a footnote inside a module. This def is an obligation, not a reading, and must never be badged as a stipulation: the registry stays at 5 stipulations, 25 dependents.
* **`F14`** (`§33 the Gödel/Tarski/Turing route as a *transcendental* argument: a system cannot supply its own evaluative foundation, therefore the foundation lies external to every system — NegativeRetorsionAudit.DiagonalSpec`) — Axiomatic diagonal specification for self-referential entertainment.
* **`F16`** (`§28 Immutability: meaning capacity is constant *across worlds* (the substantive reading of the capacity-invariance predicate) — `) — Divine Immutability - the substantive reading of capacity invariance, that a subject's meaning capacity is constant ACROSS WORLDS - is BLOCKED, and it is blocked for a reason no proof can repair: the claim cannot even be STATED. The meaning relation is EntityMeans (e : Entity) (p : Prop) : Prop at RecoveredOntologicalGround.lean:46, which takes no world argument at all, so there is no Entity -> World -> Prop -> Prop relation anywhere in the library and 

**§28 open bridges.** The prose corpus lists the still-missing named lemmas: #7 `NecessaryEntity e → ∃ τ, Ground e τ`; #8 the target opposite of #7; #9 `Ground(e, personal) → Personal(e)`; #10 its target. Each appears above in the open inventory; none is silently assumed.

---

## Which Classical Attributes Are Already Established?

> **Which classical characteristics of God do we already have?** This table reports the
> **live formal status** of the main classical attributes, derived from the current kernel
> and ledger (never from intentions). The three divine-adjacent scopes are kept apart: the **Divine
> Being / Ground**, **Divine Personhood**, and the **personal normative ground /**
> **person-type** — what §1–§10 actually establish. A separate **proof-architecture** scope reports
> a result about the deduction itself, never as a divine attribute. "Necessity" concerns the
> Being/Ground, not each Divine Person; "Personal", "Three Persons", and "One God"
> are separate claims and are reported separately. Nothing here claims a "necessary
> Person": "He is necessary" is a claim about the Divine Being / Ground, "He is
> personal" a claim about the ground-type — two different rows, never conjoined.

Status vocabulary used here (extends the badge legend above): `✅` PROVEN (machine-verified, footprint stated) · `📘` DEFINITIONAL · `⏸` DEFERRED (target not in the live kernel) · `❌` NOT ESTABLISHED (no current theorem; distinct from the ledger's `✖` BLOCKED) · `🧱` INDEPENDENT / FRONTIER (explicit countermodel: the preceding theory does not entail it).

A **`◈` suffix** on a status cell is derived from `formal/stipulation_audit.json`: the row's
anchor is a declared dependent of a registered definitional stipulation, so its theorem is
machine-verified **given that declaration**, not from Γ's axioms. It is not a warning about
rigour — the proof is as solid as any other — it is a pointer to the price, which is listed
in §D.2b and, for the ASIETY-FREEDOM batch, in the step-by-step block below.

| Classical characteristic | Scope | Status | Exact sense established by the current theory (reference) |
|---|---|---|---|
| **Personal** — the ground-type is personal | Personal ground / person-type | ✅ PROVEN | `RightWrong ⇒ Person` (`∀ s, RightWrong s → Person s`). Established of the personal ground/type, not of a particular divine person. — [PersonalGroundOfReality.lean#personal_ground_of_right_wrong](formal/Logos/PersonalGroundOfReality.lean#L100), footprint {Means, Subject, Will, subjectWill, will_individuation} |
| **Psychological personality** (humanoid consciousness, stream of experience) | Personal ground / person-type | 🧱 INDEPENDENT | Minimal personhood in Γ is functional: the Boethius–Aquinas locus of non-derived normative discrimination (`Person := ThomisticPersonCore`). Substantive psychological personhood (ordinary humanoid mind, emotional states, stream of consciousness) is provably independent: `faithful_model_satisfies_free_will_without_opaque_person` (footprint `{}`) satisfies free will without substantive psychological personality. The text explicitly disclaims ordinary psychological personality (`README-OLD.md:179-187`). — [PersonhoodOntologyAudit.lean#faithful_model_satisfies_free_will_without_opaque_person](formal/Logos/PersonhoodOntologyAudit.lean#L182), footprint {} ; [PersonhoodOntologyAudit.lean#faithful_contingent_person_fails_necessary_subject](formal/Logos/PersonhoodOntologyAudit.lean#L221), footprint {} |
| **Rational** — formally equivalent to the Thomistic core containing RationalNature | Personal ground / person-type | ✅ PROVEN | `Person(s) ↔ ThomisticPersonCore(s)`, whose conjunct `RationalNature s ≡ Intentional s ∧ FreeWill s` is definitional (`📘`). Established of the person-type. — [Person.lean#person_iff_thomisticCore](formal/Logos/Person.lean#L183), footprint {Means, Subject, Will, subjectWill} ; [Person.lean#RationalNature](formal/Logos/Person.lean#L51), footprint {Means, Subject} |
| **Free** — genuine normativity yields genuine choice and free will | Personal ground / person-type | ✅ PROVEN | `GenuineNormativity ⇒ Chooses ⇒ FreeWill`; `FreeWill s ≡ ∃ p q, Chooses s p q` is definitional (`📘`). The *existence* half is now also derived outright: a person exists (`T5_personExists_from_plurality`), `Person` bundles `FreeWill` (`DominionOverActs s ≡ FreeWill s`), so a chooser exists — at the META price of `AxTwoSubjects`, which is why the Asiety row below is ⚠️ AXIOMATIC while this row stays ✅. **Disclosed limit on this row:** `indubitable_normative_free_will` is a **sub-formula extraction, not a derivation.** It unfolds `GenuineNormativity s p q` to `Incompatible p q ∧ p ≠ q ∧ Means s p ∧ Means s q`, uses `.1`s, **discards `p ≠ q`**, and concludes `Chooses s p q` by reordering three of the four conjuncts. Its `{Means, Subject}` footprint is accurate — it records that the structure's fields *are* `Means` — but it measures no derivation from independent premises, and it must not be read as one. — [IndubitableNormativeFreeWill.lean#indubitable_normative_free_will](formal/Logos/IndubitableNormativeFreeWill.lean#L115), footprint {Means, Subject} ; [Choice.lean#FreeWill](formal/Logos/Choice.lean#L177), footprint {Means, Subject} ; [AsieticChoice.lean#chooses_implies_trueChoice](formal/Logos/AsieticChoice.lean#L164), footprint {Means, Subject} ; [AsieticChoice.lean#trueChoice_exists](formal/Logos/AsieticChoice.lean#L463), footprint {AxTwoSubjects, Means, Subject, Will, subjectWill} |
| **Asiety** — true freedom (true choice) | Personal ground / person-type | ⚠️ AXIOMATIC | `Asiety e ≡ ∃ s p q, e = EntityOf s ∧ TrueChoice s p q`, and `TrueChoice s p q ≡ Means s p ∧ Means s (¬ p) ∧ ContestedContent ∧ Incompatible p q` — so asiety is true freedom **by definition** (`📘`); the substantive content is the *derivation*, not the identification. Two disclosed prices, both pre-existing: `TrueChoice ≡ Chooses` (the openness conjunct is a global frame fact, not a per-pair modality), and existence at `AxTwoSubjects` (META). The weak→strong step is `ChoiceField → Chooses`, which is **not** free: it needs the correctness-judgment premise under `AxJudicativeBipolarity` (SEM), and the bare implication with no premise is not merely unproved but machine-refuted. **Batch ASIETY-FREEDOM splits this row's chain in two, and the split is the point:** the *Act-free* route into asiety is now **axiom-free** (`weakChoice_implies_asiety`: `GenuineNormativity s p q → Asiety (EntityOf s)`, footprint `{Means, Subject}` — 0 substantive axioms, no `Act`, no `Initiates`, no `ClaimsCorrect`, no stipulation), whereas **everything from `AsietyFreedom` onward rests on ◈ META** and is badged accordingly. See the **ASIETY-FREEDOM chain, step by step** block below for the full pricing. — [AsieticChoice.lean#asietic_summary](formal/Logos/AsieticChoice.lean#L546), footprint {AxJudicativeBipolarity, AxTwoSubjects, Initiates, Means, State, Subject, Will, subjectWill} ; [AsieticChoice.lean#TrueChoice](formal/Logos/AsieticChoice.lean#L139), footprint {Means, Subject} ; [AsieticChoice.lean#Asiety](formal/Logos/AsieticChoice.lean#L147), footprint {Means, Subject} ; [AsieticChoice.lean#asietic_is_true_freedom](formal/Logos/AsieticChoice.lean#L485), footprint {Means, Subject} ; [AsieticChoice.lean#trueChoice_exists](formal/Logos/AsieticChoice.lean#L463), footprint {AxTwoSubjects, Means, Subject, Will, subjectWill} |
| **Shared freedom of the ground** (`AsietyFreedom` — the ground's freedom, shared) | Divine Being / Ground | ✅ PROVEN ◈ | `AsietyFreedomOfGround`: the ground's freedom *reaches* every subject, so `TrueChoice` and `AsietyFreeWill` follow **conditionally** (`AsietyFreedomOfGround → AsietyFreeWill s`, C290) — this is the reading of "which is shared with us by the creator". The `Asiety` half of it is **axiom-free and independent of the ground** (`weakChoice_implies_asiety`, C287); only the *transfer* is priced. **◈ META, and the price is load-bearing:** the bridge is a **`def`**, so `#print axioms` cannot see it, and its reported `{Means, Subject}` footprint is vocabulary-only *whether the bridge is principled or arbitrary* — **"the axiom count did not move" is therefore NOT a test for this batch** (for ASIETIC-CHOICE it was). Three `{}` countermodels price it: `asietyAloneDoesNotYieldTrueChoice` (C292, the universal reading is strictly stronger than the existential one), `frameContingencyDoesNotBindAPair` (C293), and `rightWrongFactYieldsNoChooser` (C294). **No axiom-free existence of a chooser**: `¬ N_T ∧ ¬ N_F` is `Prop`-level and quantifies over no `Subject`, so the Creator step is conditional and its existence half is *not derivable*. **The ground is still not a chooser** (C295 = C285 preserved, by `ofGround_ne_ofSubject`): the ground *reaches* subjects, it is not one of them. Its `GroundsEntity` premise is **vacuous** (`ground_grounds_the_meaningless`), which is why the whole metaphysical weight sits on the ◈ entry. — [AsietyFreedom.lean#asietyFreedom_summary](formal/Logos/AsietyFreedom.lean#L296), footprint {Means, Subject} ; [AsietyFreedom.lean#AsietyFreedomOfGround](formal/Logos/AsietyFreedom.lean#L119), footprint {Means, Subject} ; [AsietyFreedom.lean#AsietyFreeWill](formal/Logos/AsietyFreedom.lean#L130), footprint {Means, Subject} ; [AsietyFreedom.lean#asietyFreedom_yields_trueChoice](formal/Logos/AsietyFreedom.lean#L176), footprint {Means, Subject} ; [AsietyFreedom.lean#asietyFreedom_yields_asietyFreeWill](formal/Logos/AsietyFreedom.lean#L192), footprint {Means, Subject} ; [AsietyFreedom.lean#asietyFreeWill_yields_trueChoice](formal/Logos/AsietyFreedom.lean#L202), footprint {Means, Subject} ; [AsietyFreedom.lean#groundIsNotASharerOfAsietyFreeWill](formal/Logos/AsietyFreedom.lean#L283), footprint {Means, Subject} |
| **Divine love** (the ground as lover of contingent reality) | Divine Being / Ground | ⚠️ AXIOMATIC | The ground is a *necessary* lover of a *chosen* good: `NecessaryEntity Entity.ofGround` (`trivial`, ontology-forced) conjoined with a directional good it holds toward a contingent, meaning-bearing realm — the machine form of `poem.txt:24`'s "Amar é escolhido e também é necessário". The claim is about the ground **as a kind**; no hypostatic identification is made (C344). **Two prices, different in kind** (see the **LOVE chain, step by step** block below): the VOCAB primitive `GroundBearsGood` (the directed-good vocabulary the library lacked — `GroundsEntity` is undirected and vacuous, `EntityMeans` is a capacity of the target, `Good s (_a)` is `Subject`-indexed) and the META bridge `AxGroundLovesContingentRealm` (the inhabitation, genuinely not forced: the `GroundBearsGood := False` model satisfies all vocabulary while every inhabitant fails). Note the badge reads **⚠️ AXIOMATIC (AxGroundLovesContingentRealm)** only: `GroundBearsGood` is filed under the vocabulary baseline by `footprint_parts` and never appears in the parenthetical, so a reader trusting the badge alone will take the primitive as free — the chain block below is the only place the VOCAB price is visible. What the batch is mostly is negative: the separation is machine-checked (C336: grounding reaches an atom, love does not); the unrestricted, more attractive bridge is *false* (C338 — the only justification for the axiom's meaning hypothesis); and the `GroundLoves → Loves` transfer is **unstatable, not merely unproved** (C348), so bridge #9 / C228 is untouched and F3, F6/Trinity and the personal-monotheism frontier do not move. The cosmos it loves now *exists by theorem* — free, in fact: C350 `contingent_realm_obtains` at `{propext, Subject}`, with the plurality bridge paying only for the realm's *content* (C367 `cosmos_obtains`, given an exhibited contingent person) — which is not an entailment from the ground. — [LovesAsGround.lean#the_ground_is_a_necessary_and_chosen_lover](formal/Logos/LovesAsGround.lean#L493), footprint {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} ; [LovesAsGround.lean#GroundLoves](formal/Logos/LovesAsGround.lean#L339), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject} ; [LovesAsGround.lean#grounding_reaches_what_love_cannot](formal/Logos/LovesAsGround.lean#L385), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject} ; [LovesAsGround.lean#meaningful_love_bridge_is_refuted](formal/Logos/LovesAsGround.lean#L413), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} ; [LovesAsGround.lean#ground_love_cannot_be_read_as_person_love](formal/Logos/LovesAsGround.lean#L561), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} ; [CosmicExistence.lean#the_ground_loves_the_cosmos](formal/Logos/CosmicExistence.lean#L559), footprint {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, Will, subjectWill, CL} |
| **Independent will** — with numerical individuation | Personal ground / person-type | ✅ PROVEN | `Person(s) ↔ FreeIndependentWill(s)`; `subjectWill s₁ ≠ subjectWill s₂` — distinct persons have numerically distinct wills. The meaning-postulate status is kernel-verified: `will_individuation` is not derivable from the pre-will spine (`WillIndividuationAudit.will_individuation_not_forced_by_prewill_spine`, `{}`). — [Person.lean#person_iff_freeIndependentWill](formal/Logos/Person.lean#L166), footprint {Means, Subject, Will, subjectWill} ; [Person.lean#IndependentWill](formal/Logos/Person.lean#L36), footprint {Subject, Will, subjectWill} |
| **Dominion over acts** / authoritative personhood | Personal ground / person-type | ✅ PROVEN | the Thomistic-personcore conjunct `DominionOverActs s ≡ FreeWill s` is definitional (`📘`); present inside `person_iff_thomisticCore`. — [Person.lean#DominionOverActs](formal/Logos/Person.lean#L56), footprint {Means, Subject} |
| **Ground of objective normativity (Right and Wrong)** | Personal ground / person-type | ✅ PROVEN | `Person s → GroundsRightWrong s`, and the headline that "the person supports the reality of Right". Established of the personal ground. — [PersonalNormativeGround.lean#person_grounds_normative_polarity](formal/Logos/PersonalNormativeGround.lean#L529), footprint {Means, Subject, Will, subjectWill} ; [PersonalGroundOfReality.lean#the_person_supports_the_reality_of_right](formal/Logos/PersonalGroundOfReality.lean#L153), footprint {Initiates, Means, State, Subject, Will, subjectWill, will_individuation, CL} |
| **Non-relative core** — strict architectural invariance only | Proof architecture (not divine scope) | ✅ PROVEN | `(∀ l, AgentInvariant l → FreeWillInvariant l) ∧ ∃ l, FreeWillInvariant l ∧ ¬ AgentInvariant l` (GAPMAP C180; prose T18): the dependency-layer core admissible in every proof regime — including the non-agentive structural regime — is strictly contained in the core admissible across all agentive regimes (footprint `{}`, pure logic). This is proof architecture only: it does not establish that the Divine Being / Ground, a divine person, or the ultimate foundation is invariant across systems, perspectives, or worlds. — [HardenedInvariance.lean#agent_invariant_core_is_strictly_inside_freewill_invariant_core](formal/Logos/HardenedInvariance.lean#L226), footprint {} ; [HardenedInvariance.lean#strict_core_inclusion](formal/Logos/HardenedInvariance.lean#L173), footprint {} ; [HardenedInvariance.lean#agent_invariant_iff_agent_neutral_core](formal/Logos/HardenedInvariance.lean#L118), footprint {} ; [HardenedInvariance.lean#freewill_invariant_iff_freewill_neutral_core](formal/Logos/HardenedInvariance.lean#L153), footprint {} |
| **Necessary Divine Being / Ground** | Divine Being / Ground | ✅ PROVEN ◈ | The ground itself is world-rigid: `NecessaryEntity Entity.ofGround` (`∀ w, ExistsAt w .ofGround`, definitional `EntityExistsAt w .ofGround := True`, footprint `{Means, Subject}` — VOCAB only). Claim E is now a **live theorem** as a *non-hypostatic* pairing: the entity-necessity conjunct is PROVEN, the personal-kind conjunct is `{AxTwoSubjects, Means, Subject}` (PROVEN↑ under the declared META axiom `AxTwoSubjects`), and the hypostatic identity is blocked (`ofGround_ne_ofSubject`: `ofGround ≠ EntityOf s`). NO 'necessary Person' theorem exists — this row is the entity-level ground, distinct from the necessary-*order* row above. — [NecessityEternity.lean#ofGround_necessary_ground_of_reality](formal/Logos/NecessityEternity.lean#L153), footprint {Means, NecessarySubjectKind, Subject} ; [NecessityEternity.lean#claimE](formal/Logos/NecessityEternity.lean#L304), footprint {AxTwoSubjects, Means, NecessarySubjectKind, Subject, Will, subjectWill} ; [NecessaryPersonalGround.lean#step1_necessary_truth_exists](formal/Logos/NecessaryPersonalGround.lean#L204), footprint {CL} ; [NecessaryPersonalGround.lean#necessary_normative_order](formal/Logos/NecessaryPersonalGround.lean#L110), footprint {Initiates, Means, State, Subject} |
| **Aseity** — non-derived / non-dependent | Divine Being / Ground | ✅ PROVEN | In the canonical ontology of entities, `conditional_canonical_aseity` (`CanonicalAseity.lean`, footprint `{Means, Subject}` — VOCAB only) establishes that `Entity.ofGround` has Canonical Aseity (`¬ ∃ g, ExternalGrounding g .ofGround`), conditional on all subjects being discriminating (`∀ s, ∃ p, ¬ Means s p`). Atomic entities are unconditionally excluded (`atom_cannot_ground_the_ground`, `{Means, Subject}`). At the generic modal frontier, C182 and C184 establish two-way logical independence between bare `Aseity` and volitional alternatives (footprint `{}`); that generic separation is not a proof or disproof of aseity for `Entity.ofGround` or the ultimate foundation. — [CanonicalAseity.lean#conditional_canonical_aseity](formal/Logos/CanonicalAseity.lean#L133), footprint {Means, Subject} ; [CanonicalAseity.lean#atom_cannot_ground_the_ground](formal/Logos/CanonicalAseity.lean#L96), footprint {Means, Subject} ; [CanonicalAseity.lean#canonical_aseity_implies_modal_aseity](formal/Logos/CanonicalAseity.lean#L73), footprint {Means, NecessarySubjectKind, Subject} ; [ModalPossibilityFrontier.lean#aseity_does_not_force_any_volition_alternatives](formal/Logos/ModalPossibilityFrontier.lean#L463), footprint {} ; [ModalPossibilityFrontier.lean#volitional_alternative_does_not_force_aseity](formal/Logos/ModalPossibilityFrontier.lean#L485), footprint {} |
| **Foundational unicity** (structural unicity of the universal ground of reality) | Divine Being / Ground | ✅ PROVEN | **Classical Monotheism of the ground is PROVEN.** `exactly_one_universal_modal_ground` (C320) states it outright (Aquinas *ST* I, q. 11, a. 3): **existence is unconditional**, and uniqueness follows from the single named hypothesis that no subject has total meaning-capacity — which is now the **27th declared axiom**, `SemanticFinitude` (C388, `Tag: VOCAB`, ledger row F15), and is consumed unconditionally by `exactly_one_universal_modal_ground_stipulated` (C389, footprint `{Means, NecessarySubjectKind, SemanticFinitude, Subject}`). So the price of unicity is one *named vocabulary* axiom, not an anonymous premise: the same shape `∀ s, ∃ p, ¬ Means s p` was already being paid 20 times across 5 files as the standing hypothesis of `DivineSimplicity`, `DivinePureActuality`, `FoundationalUnicity` and `CanonicalAseity`; declaring it once is a *consolidation*, and it turned ten conditional attribute corollaries (C389–C398) into unconditional theorems. In `FoundationalUnicity.lean` (footprint `{Means, NecessarySubjectKind, Subject}` — VOCAB only). **Correction (2026-09-27): the original route is void.** (1) Diagnosis — `not_asymmetric_grounding` machine-refutes `AsymmetricGrounding`: grounding is meaning-containment and therefore **reflexive** (`groundsEntity_reflexive`), and the definition omitted the `g1 ≠ g2` guard, so the premise consumed by `universal_ground_unicity` and `ofGround_foundational_unicity` is **unsatisfiable**. Those two rows stay PROVEN as conditional theorems, but no unpayable premise may stand as a proven attribute. (2) The needed notion already existed — `grounds_ground_iff_maximal` proves that grounding the ground **is** `MaximalCapacity`, so no new axiom was invented. (3) Repair — `ofGround_sole_universal_ground` already excludes every entity except a subject meaning *everything*; `ofGround_unicity_from_no_discriminating_subject` closes exactly that last case from the single hypothesis that no subject has total meaning-capacity, and `exactly_one_universal_modal_ground` states **Classical Monotheism outright** (Aquinas *ST* I, q. 11, a. 3): existence unconditional, uniqueness under that one named hypothesis. `no_discriminating_subject_iff_no_maximal_non_ground` proves the hypothesis **is** the exclusion of maximal capacity among non-ground entities, so the whole price is one existing predicate. **F15, closed by declaration (2026-09-28):** this row used to read *"no *axiom* asserts the hypothesis, so C320 cannot consume it unconditionally … F15 is an *unnamed* commitment rather than a new bridge. The outstanding decision is consolidation."* All three sentences are now superseded: the consolidation was carried out, the sentence is `SemanticFinitude`, and C320's unicity has an unconditional corollary (C389). The diagnosis below is kept because it is still the reason the *old* route was void, and because it is the reason the axiom is a declaration rather than a derivation — the hypothesis was always being paid, which is exactly what makes it vocabulary. Honest boundary: strictly separated from numerical unitarianism (which would rule out Trinitarian relations) and pantheism. — [FoundationalUnicity.lean#ofGround_foundational_unicity](formal/Logos/FoundationalUnicity.lean#L215), footprint {Means, NecessarySubjectKind, Subject, CL} ; [FoundationalUnicity.lean#universal_ground_unicity](formal/Logos/FoundationalUnicity.lean#L86), footprint {Means, NecessarySubjectKind, Subject, CL} ; [FoundationalUnicity.lean#no_atom_is_universal_modal_ground](formal/Logos/FoundationalUnicity.lean#L155), footprint {Means, NecessarySubjectKind, Subject} ; [FoundationalUnicity.lean#no_discriminating_subject_is_universal_modal_ground](formal/Logos/FoundationalUnicity.lean#L168), footprint {Means, NecessarySubjectKind, Subject} ; [FoundationalUnicity.lean#ofGround_sole_universal_ground](formal/Logos/FoundationalUnicity.lean#L181), footprint {Means, NecessarySubjectKind, Subject} ; [FoundationalUnicity.lean#unicity_strictly_transcends_world](formal/Logos/FoundationalUnicity.lean#L327), footprint {Subject} ; [FoundationalUnicity.lean#groundsEntity_reflexive](formal/Logos/FoundationalUnicity.lean#L113), footprint {Means, Subject} ; [FoundationalUnicity.lean#grounds_ground_iff_maximal](formal/Logos/FoundationalUnicity.lean#L121), footprint {Means, Subject} ; [FoundationalUnicity.lean#ofGround_unicity_from_no_discriminating_subject](formal/Logos/FoundationalUnicity.lean#L235), footprint {Means, NecessarySubjectKind, Subject} ; [FoundationalUnicity.lean#no_discriminating_subject_iff_no_maximal_non_ground](formal/Logos/FoundationalUnicity.lean#L249), footprint {Means, Subject, CL} ; [FoundationalUnicity.lean#exactly_one_universal_modal_ground](formal/Logos/FoundationalUnicity.lean#L301), footprint {Means, NecessarySubjectKind, Subject} |
| **Strict numerical unitarianism** (ruling out relational internal plurality/persons) | Divine Being / Ground | 🧱 INDEPENDENT | Proving that the universal ground of reality is structurally unique does not force that the internal life of the ground is a solitary, relationless monad (`unicity_does_not_force_unitarian_monad`, footprint `{}`). The relational plurality of persons remains an open, non-collapsed frontier. — [FoundationalUnicity.lean#unicity_does_not_force_unitarian_monad](formal/Logos/FoundationalUnicity.lean#L317), footprint {} ; [TheologicalModalHardening.lean#necessary_existence_not_entails_uniqueness](formal/Logos/TheologicalModalHardening.lean#L406), footprint {} ; [Plurality.lean#T12_twoPersons](formal/Logos/Plurality.lean#L207), footprint {AxTwoSubjects, Means, Subject, Will, subjectWill} |
| **One God / strict monotheism** (unity of the Divine Being) | Divine Being / Ground | ⏸ DEFERRED | **This label was carrying two claims; only one of them is still open (corrected 2026-09-27).** (1) *Uniqueness of the universal ground* is **PROVEN**: `exactly_one_universal_modal_ground` (C320) proves that exactly one universal modal ground exists — **existence unconditional**, uniqueness under the single named hypothesis `∀ s, ∃ p, ¬ Means s p`, which is now the **declared axiom** `SemanticFinitude` (C388, `Tag: VOCAB`, ledger row F15) and is consumed unconditionally by `exactly_one_universal_modal_ground_stipulated` (C389). That is the mathematical content of monotheism at the level of the Divine Being. (2) *Person-level monotheism* — one God as numerically one Person, and its compatibility with three Persons — **remains DEFERRED**: `monotheism_of_god_and_uniqueness` and `monotheism_compatible_with_trinity` are still out of the live kernel and no compiled declaration exists for either, because they need the person bridge C228, which is BLOCKED. The scope limit is unchanged and machine-checked: unicity of the ground does not force a solitary, relationless monad (`unicity_does_not_force_unitarian_monad`, C212, `{}`), so the Trinitarian frontier stays open. The older justification for the deferral — that "uniqueness is provably NOT a kernel consequence" — held only of the *modal* route (`TheologicalModalHardening.necessary_existence_not_entails_uniqueness`, `{}`: bare necessity does not entail uniqueness). It did not hold of the grounding route, which now closes. — [FoundationalUnicity.lean#exactly_one_universal_modal_ground](formal/Logos/FoundationalUnicity.lean#L301), footprint {Means, NecessarySubjectKind, Subject} ; [FoundationalUnicity.lean#ofGround_sole_universal_grounding](formal/Logos/FoundationalUnicity.lean#L284), footprint {Means, NecessarySubjectKind, Subject} ; [FoundationalUnicity.lean#ofGround_unicity_from_no_discriminating_subject](formal/Logos/FoundationalUnicity.lean#L235), footprint {Means, NecessarySubjectKind, Subject} ; [FoundationalUnicity.lean#unicity_does_not_force_unitarian_monad](formal/Logos/FoundationalUnicity.lean#L317), footprint {} ; [TheologicalModalHardening.lean#necessary_existence_not_entails_uniqueness](formal/Logos/TheologicalModalHardening.lean#L406), footprint {} |
| **Perfect (moral) goodness** | Divine Being / Ground | 🧱 INDEPENDENT | GAPMAP ledger row `F3 §28 (Good)` = COUNTERMODEL (🧱) via C175: the `M_amoral` model (`{}`) satisfies epistemic agential normativity with no practical obligation — the separation is permanent (`moral_pole_postulate_is_not_a_consequence`, vocabulary-only), so the moral pole is never *read off* the normative structure. Right/Wrong here is epistemic correctness, explicitly distinguished from moral good/evil. The *positive pole itself* is nevertheless obtained: `Good` is a fair definition (helping another person; `{Means, Subject}` — the definition smuggles nothing) and `moral_good_obtains` (C178) is PROVEN↑ under the single disclosed META bridge `AxBenevolentBearingObtains` (C177, "some person is actually helped"). The bridge is a paid commitment, not a hidden derivation: the bare value layer is machine-proven empty (`no_help_obtains`, C176, `{Subject}`), which is the bridge's own countermodel. The negative pole `Evil` remains a declared SEM datum (its fair reading needs a parallel harm bridge, not declared). What stays a countermodel frontier is the *attribution* of this goodness to the Divine Being — that remains a separate target. — [MoralFrontierAudit.lean#moral_good_obtains](formal/Logos/MoralFrontierAudit.lean#L212), footprint {AxBenevolentBearingObtains, Means, Subject, Will, subjectWill} ; [MoralFrontierAudit.lean#Good](formal/Logos/MoralFrontierAudit.lean#L203), footprint {Means, Subject, Will, subjectWill} ; [MoralFrontierAudit.lean#moral_pole_postulate_is_not_a_consequence](formal/Logos/MoralFrontierAudit.lean#L261), footprint {Initiates, Means, State, Subject} ; [Value.lean#AxBenevolentBearingObtains](formal/Logos/Value.lean#L183), footprint {AxBenevolentBearingObtains, Means, Subject, Will, subjectWill} ; [Value.lean#no_help_obtains](formal/Logos/Value.lean#L110), footprint {Subject} |
| **Eternal — ever-present** (everlasting existence) | Divine Being / Ground | ✅ PROVEN ◈ | World-rigid existence is unmodulated by time: `NecessaryEntity e → Everlasting e` (`∀ t, ExistsAtTime t e`) is a definitional corollary of necessity via the Nat-stage layer — the deduction imports NO temporal premise, time enters only on the conclusion side. `Everlasting Entity.ofGround` is therefore PROVEN (`{Subject}` + ground footprint, VOCAB). Distinct from the eternal love-*relation* `T14_eternalRelation_conditional`. C181 supplies the generic empty-footprint necessity-to-stage transport, but deliberately does not instantiate the canonical `Entity` sort. — [NecessityEternity.lean#the_ground_everlasting](formal/Logos/NecessityEternity.lean#L187), footprint {NecessarySubjectKind, Subject} ; [NecessityEternity.lean#necessary_implies_everlasting](formal/Logos/NecessityEternity.lean#L172), footprint {NecessarySubjectKind, Subject} ; [NecessityEternity.lean#necessary_existence_is_stage_uniform](formal/Logos/NecessityEternity.lean#L111), footprint {} ; [NecessityEternity.lean#ofGround_necessary](formal/Logos/NecessityEternity.lean#L137), footprint {NecessarySubjectKind, Subject} ; [Love.lean#T14_eternalRelation_conditional](formal/Logos/Love.lean#L113), footprint {Means, NecessarySubjectKind, Subject, Will, subjectWill} |
| **Atemporal** (existence not time-modulated; outside succession) | Divine Being / Ground | ✅ PROVEN ◈ | `NecessaryEntity e → Atemporal e` (`ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e`); the ground is also outside every initiation-act (`the_ground_not_in_succession`, `{Initiates, State, Subject}`). Separation is honest: atoms/subjects are time-modulated (`atom_has_temporal_mode`) and `Everlasting` does not collapse into necessity (`everlasting_but_contingent`). What is PROVEN is stage-unmodulated world-rigid existence — not a full theology of divine eternity. C181 makes the underlying transport explicit without instantiating the canonical `Entity` sort. — [NecessityEternity.lean#the_ground_atemporal](formal/Logos/NecessityEternity.lean#L191), footprint {NecessarySubjectKind, Subject} ; [NecessityEternity.lean#necessary_implies_atemporal](formal/Logos/NecessityEternity.lean#L179), footprint {NecessarySubjectKind, Subject} ; [NecessityEternity.lean#necessary_existence_is_stage_uniform](formal/Logos/NecessityEternity.lean#L111), footprint {} ; [NecessityEternity.lean#the_ground_not_in_succession](formal/Logos/NecessityEternity.lean#L196), footprint {Initiates, State, Subject} ; [NecessityEternity.lean#atom_has_temporal_mode](formal/Logos/NecessityEternity.lean#L239), footprint {NecessarySubjectKind, Subject} ; [NecessityEternity.lean#everlasting_but_contingent](formal/Logos/NecessityEternity.lean#L272), footprint {NecessarySubjectKind, Subject} |
| **Divine simplicity** | Divine Being / Ground | ✅ PROVEN ◈ | In `DivineSimplicity.lean` (footprint `{Means, Subject, propext}` — VOCAB + CL), `ofGround_divine_simplicity` proves that `Entity.ofGround` satisfies classical Divine Simplicity under finite subjectivity (`∀ s, ∃ p, ¬ Means s p`): (1) Mereological Non-Compositeness (`NonComposite e ↔ CanonicalAseity e`, no proper grounding parts); (2) Structural Inextension (`ofGround_has_no_internal_components`, atomic nullary constructor with zero internal decomposition); (3) Intentional Simplicity (`ofGround_undivided_meaning`, uniform meaning capacity across all propositions); (4) Ontological Transcendence (`ofGround_transcendent`, distinct from all atomic worldly states and finite subjects). Composite entities provably fail simplicity (`composite_entity_fails_simplicity`, `{}`). Honest boundary: this establishes mereological, structural, and intentional simplicity — not identity of essence and existence. — [DivineSimplicity.lean#ofGround_divine_simplicity](formal/Logos/DivineSimplicity.lean#L179), footprint {Means, Subject, CL} ; [DivineSimplicity.lean#ofGround_has_no_internal_components](formal/Logos/DivineSimplicity.lean#L100), footprint {Subject} ; [DivineSimplicity.lean#ofGround_undivided_meaning](formal/Logos/DivineSimplicity.lean#L118), footprint {Means, Subject} ; [DivineSimplicity.lean#ofGround_transcendent](formal/Logos/DivineSimplicity.lean#L151), footprint {Subject} ; [DivineSimplicity.lean#non_composite_iff_canonical_aseity](formal/Logos/DivineSimplicity.lean#L69), footprint {Means, Subject} ; [DivineSimplicity.lean#composite_entity_fails_simplicity](formal/Logos/DivineSimplicity.lean#L202), footprint {} |
| **Scholastic simplicity** (strict identity of essence and existence) | Divine Being / Ground | ❌ NOT ESTABLISHED | The theory proves mereological, structural, and intentional simplicity (`DivineSimplicity.lean`). The traditional scholastic doctrine asserting the strict identity of essence and existence or collapsing all divine attributes into undifferentiated identity is not derived. |
| **Divine immutability** (ontological, temporal, and process unchangeability) | Divine Being / Ground | ✅ PROVEN | In `DivineImmutability.lean` (footprint `{Initiates, Means, State, Subject}` — VOCAB only), `ofGround_divine_immutability` establishes Classical Divine Immutability (Aquinas *ST* I, q. 9) for `Entity.ofGround`: (1) Modal Invariance (`ofGround_modal_invariance`, `{Subject}`, unchanging existence across all worlds); (2) Stage Invariance (`ofGround_stage_invariance`, `{Subject}`, unchanging existence across all temporal stages); (3) Transition Invariance (`ofGround_transition_invariance`, `{Initiates, State, Subject}`, outside all initiation and state becoming); (4) Capacity Invariance (`ofGround_capacity_invariance`, `{Means, Subject}`, uniform intentional capacity across reality). The Thomistic principle is proven: necessity, atemporality, and non-succession entail immutability. Contingent entities provably fail immutability (`contingent_entity_fails_immutability`, `{}`). **Vacuity disclosure (C321):** field (4) discriminates nothing — `capacity_invariance_holds_for_every_entity` proves it holds for *every* entity, because `EntityMeans` takes no world argument, so the two worlds in `CapacityInvariance` are bound and unused and the body is `P ↔ P`. All three siblings genuinely quantify and each has a `{}` countermodel; this one has none, because there is nothing in it to refute. The substantive reading (capacity constant *across worlds*, *ST* I q. 9 a. 3) is not expressible in the present vocabulary and stays open as frontier F16. This is disclosure, not demotion: the immutability row itself remains PROVEN. Honest boundary: establishes modal, temporal, and process unchangeability in Γ, plus a capacity-invariance predicate that is currently vacuous; does not claim psychological impassibility or constrain relational intentionality. — [DivineImmutability.lean#ofGround_divine_immutability](formal/Logos/DivineImmutability.lean#L192), footprint {Initiates, Means, NecessarySubjectKind, State, Subject} ; [DivineImmutability.lean#ofGround_modal_invariance](formal/Logos/DivineImmutability.lean#L73), footprint {NecessarySubjectKind, Subject} ; [DivineImmutability.lean#ofGround_stage_invariance](formal/Logos/DivineImmutability.lean#L92), footprint {NecessarySubjectKind, Subject} ; [DivineImmutability.lean#ofGround_transition_invariance](formal/Logos/DivineImmutability.lean#L109), footprint {Initiates, State, Subject} ; [DivineImmutability.lean#ofGround_capacity_invariance](formal/Logos/DivineImmutability.lean#L137), footprint {Means, Subject} ; [DivineImmutability.lean#capacity_invariance_holds_for_every_entity](formal/Logos/DivineImmutability.lean#L164), footprint {Means, Subject} ; [DivineImmutability.lean#necessity_and_atemporality_yield_immutability](formal/Logos/DivineImmutability.lean#L208), footprint {Initiates, Means, NecessarySubjectKind, State, Subject} ; [DivineImmutability.lean#contingent_entity_fails_immutability](formal/Logos/DivineImmutability.lean#L228), footprint {} |
| **Psychological impassibility** (incapacity for relational affect or compassion) | Divine Being / Ground | ❌ NOT ESTABLISHED | The ground is immutable in its modal existence, temporal stages, process transitions, and capacity (`DivineImmutability.lean`). Impassibility as a **person-level** claim — incapacity for relational affect or compassion in a person — is not established and cannot be: the ground is provably **no person** (`the_ground_is_not_a_person`, C344), and impassibility is a claim about persons. What is *not* excluded is relational affect at the **entity** level: `the_ground_is_a_necessary_and_chosen_lover` (C343, AXIOMATIC) attributes a directed good to the ground **as a kind**, without making it a subject. So the absence is genuine but narrow: person-level impassibility stays absent because there is no person here to be impassible, while Γ explicitly proves both the eternal relationality of interpersonal love (`T14_eternalRelation_conditional`) and a priced ground-level love that is provably disjoint from it (C346/C348). — [Love.lean#T14_eternalRelation_conditional](formal/Logos/Love.lean#L113), footprint {Means, NecessarySubjectKind, Subject, Will, subjectWill} ; [LovesAsGround.lean#the_ground_is_a_necessary_and_chosen_lover](formal/Logos/LovesAsGround.lean#L493), footprint {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} ; [LovesAsGround.lean#the_ground_is_not_a_person](formal/Logos/LovesAsGround.lean#L517), footprint {Subject} |
| **Foundational omnipresence** (sustaining presence to all beings across modal reality) | Divine Being / Ground | ✅ PROVEN | In `FoundationalOmnipresence.lean` (footprint `{Means, Subject}` — VOCAB only), `ofGround_foundational_omnipresence` establishes Classical Foundational Omnipresence (Aquinas *ST* I, q. 8) for `Entity.ofGround`: (1) World-Rigid Presence (`ofGround_world_rigid_presence`, `{Subject}`, present across all possible worlds); (2) Universal Modal Grounding (`ofGround_universal_modal_ground`, `{Means, Subject}`, grounds every entity in every possible world); (3) Non-Reciprocal Grounding (`ofGround_non_reciprocal_ground`, `{Means, Subject}`, asymmetric sustenance, ungrounded by atoms or finite subjects); (4) Maximal Intentional Capacity (`ofGround_maximal_capacity`, `{Means, Subject}`, exhaustive meaning capacity). The Thomistic principle is proven: universal modal grounding, presence, and aseity entail omnipresence. Finite entities provably fail universal grounding (`finite_entity_fails_omnipresence`, `{}`). Honest boundary: establishes foundational sustaining presence across modal reality in Γ; explicitly distinguishes foundational omnipresence from physical spatial omnipresence or quantitative metric infinity. — [FoundationalOmnipresence.lean#ofGround_foundational_omnipresence](formal/Logos/FoundationalOmnipresence.lean#L154), footprint {Means, NecessarySubjectKind, Subject} ; [FoundationalOmnipresence.lean#ofGround_world_rigid_presence](formal/Logos/FoundationalOmnipresence.lean#L88), footprint {NecessarySubjectKind, Subject} ; [FoundationalOmnipresence.lean#ofGround_universal_modal_ground](formal/Logos/FoundationalOmnipresence.lean#L70), footprint {Means, NecessarySubjectKind, Subject} ; [FoundationalOmnipresence.lean#ofGround_non_reciprocal_ground](formal/Logos/FoundationalOmnipresence.lean#L108), footprint {Means, Subject} ; [FoundationalOmnipresence.lean#ofGround_maximal_capacity](formal/Logos/FoundationalOmnipresence.lean#L125), footprint {Means, Subject} ; [FoundationalOmnipresence.lean#omnipresence_from_universal_ground_and_aseity](formal/Logos/FoundationalOmnipresence.lean#L170), footprint {Means, NecessarySubjectKind, Subject} ; [FoundationalOmnipresence.lean#finite_entity_fails_omnipresence](formal/Logos/FoundationalOmnipresence.lean#L190), footprint {} |
| **Physical omnipresence** (spatial presence throughout physical spacetime coordinates) | Divine Being / Ground | ❌ NOT ESTABLISHED | Spatial extension and physical spacetime coordinates are absent from the primitive ontology of Γ. The ground is omnipresent foundationally (sustaining all beings across all possible worlds, `FoundationalOmnipresence.lean`), not by physical diffusion or spatial location. |
| **Quantitative metric infinity** (infinite physical magnitude or cardinal size) | Divine Being / Ground | ❌ NOT ESTABLISHED | The foundation is universal in foundational scope (grounding all reality, `FoundationalOmnipresence.lean`), but quantitative metric infinity (spatial magnitude or cardinal size) is not derived and is explicitly disclaimed (`CHARACTERISTICS.md` §11; `CHARS.md` §11). |
| **Divine pure actuality** (*Actus Purus* / perfection) | Divine Being / Ground | ✅ PROVEN | In `DivinePureActuality.lean` (footprint `{Initiates, Means, State, Subject}` — VOCAB only), `ofGround_divine_pure_actuality` establishes Classical Divine Pure Actuality (*Actus Purus*, Aquinas *ST* I, q. 3, a. 1–2; q. 4, a. 1–2) for `Entity.ofGround` with 0 substantive axioms: (1) Zero Existential Potency (`ofGround_no_existential_potency`, `{Subject}`, necessary actuality across all worlds); (2) Zero Grounding Potency (`ofGround_no_grounding_potency`, `{Means, Subject}`, ungrounded by external entities); (3) Zero Transition Potency (`ofGround_no_transition_potency`, `{Initiates, State, Subject}`, immune to agential succession); (4) Zero Intentional Potency (`ofGround_no_intentional_potency`, `{Means, Subject}`, exhaustive propositional meaning); (5) Universal Actuality (`ofGround_universal_modal_ground`, active sustaining ground of all reality). Corollaries: Divine Incorporeality (`ofGround_incorporeal`, `{Subject}`, non-atomic and non-corporeal); entities with passive potency fail Pure Actuality (`entity_with_potency_fails_pure_actuality`, `{}`). Honest boundary: establishes metaphysical Pure Actuality in Γ; does not imply physical kinetic energy or thermodynamic work. — [DivinePureActuality.lean#ofGround_divine_pure_actuality](formal/Logos/DivinePureActuality.lean#L182), footprint {Initiates, Means, NecessarySubjectKind, State, Subject} ; [DivinePureActuality.lean#ofGround_no_existential_potency](formal/Logos/DivinePureActuality.lean#L100), footprint {NecessarySubjectKind, Subject} ; [DivinePureActuality.lean#ofGround_no_grounding_potency](formal/Logos/DivinePureActuality.lean#L114), footprint {Means, Subject} ; [DivinePureActuality.lean#ofGround_no_transition_potency](formal/Logos/DivinePureActuality.lean#L128), footprint {Initiates, State, Subject} ; [DivinePureActuality.lean#ofGround_no_intentional_potency](formal/Logos/DivinePureActuality.lean#L142), footprint {Means, Subject} ; [DivinePureActuality.lean#necessity_aseity_and_immutability_yield_pure_actuality](formal/Logos/DivinePureActuality.lean#L197), footprint {Initiates, Means, NecessarySubjectKind, State, Subject} ; [DivinePureActuality.lean#ofGround_incorporeal](formal/Logos/DivinePureActuality.lean#L220), footprint {Subject} ; [DivinePureActuality.lean#entity_with_potency_fails_pure_actuality](formal/Logos/DivinePureActuality.lean#L81), footprint {} |
| **Physical / kinetic energy** (thermodynamic or kinetic physical motion) | Divine Being / Ground | ❌ NOT ESTABLISHED | Pure Actuality in Γ is metaphysical (absence of passive potency and universal modal grounding, `DivinePureActuality.lean`). Physical kinetic motion, thermodynamic energy, and material work are not derived and are explicitly demarcated (`pure_actuality_independent_of_physical_energy`, `{}`). — [DivinePureActuality.lean#pure_actuality_independent_of_physical_energy](formal/Logos/DivinePureActuality.lean#L270), footprint {} |
| **Foundational omniscience** (truth-exhaustive scope — the condition of all truth) | Divine Being / Ground | ✅ PROVEN ◈ | In `DivineOmniscience.lean` (footprint `{Means, Subject}` — VOCAB only), `ofGround_foundational_omniscience` establishes the weak classical sense of omniscience for `Entity.ofGround` (the ground as the condition of all truth, Aquinas *ST* I, q. 14, a. 1) with 0 substantive axioms: (1) Truth-exhaustive scope (`ofGround_truth_exhaustive`, `{Means, Subject}`: no true proposition is closed to the ground's scope); (2) World-indexed exhaustiveness (`ofGround_world_truth_exhaustive`, `{Means, Subject}`: no state of affairs true in any world is out of scope); (3) Exhaustive exclusion of worldly atoms (`atom_not_truth_exhaustive`, `{Means, Subject}`) and of discriminating subjects (`discriminating_subject_not_truth_exhaustive`, `{Means, Subject}`), leaving `Entity.ofGround` the sole candidate in the Γ inventory; (4) Undivided scope (reused `ofGround_undivided_meaning`) and universal modal grounding (reused `ofGround_universal_modal_ground`). Honest boundary: the *refutation* of infallibility is carried as a field of the record, not as a remark — see the next row. — [DivineOmniscience.lean#ofGround_foundational_omniscience](formal/Logos/DivineOmniscience.lean#L200), footprint {Means, NecessarySubjectKind, Subject} ; [DivineOmniscience.lean#ofGround_truth_exhaustive](formal/Logos/DivineOmniscience.lean#L122), footprint {Means, Subject} ; [DivineOmniscience.lean#ofGround_world_truth_exhaustive](formal/Logos/DivineOmniscience.lean#L129), footprint {Means, Subject} ; [DivineOmniscience.lean#atom_not_truth_exhaustive](formal/Logos/DivineOmniscience.lean#L155), footprint {Means, Subject} ; [DivineOmniscience.lean#discriminating_subject_not_truth_exhaustive](formal/Logos/DivineOmniscience.lean#L164), footprint {Means, Subject} ; [DivineOmniscience.lean#necessity_and_scope_yield_foundational_omniscience](formal/Logos/DivineOmniscience.lean#L220), footprint {Means, NecessarySubjectKind, Subject} ; [DivineOmniscience.lean#entity_scope_exhaustiveness_is_not_infallibility](formal/Logos/DivineOmniscience.lean#L91), footprint {} ; [DivineOmniscience.lean#exhaustive_scope_without_counterfactual_knowledge](formal/Logos/DivineOmniscience.lean#L242), footprint {} |
| **Infallible / counterfactual omniscience** ("all and only truths", ordinary knowledge of all truth) | Divine Being / Ground | ❌ NOT ESTABLISHED ◈ | The strong sense is not merely unproven but **refuted** for the canonical ground: `ofGround_not_truth_tracking` (`{Means, Subject}`) proves `¬ TruthTracking Entity.ofGround`, because `EntityMeans (Entity.ofGround) p` reduces to `True` (definitional stipulation ◈ `ofGround_meansAll`), so the ground's scope bears every proposition — including `False` — and the exclusive half `EntityMeans e p → T p` is false of it; the scope is exhaustive and provably not error-free. Metatheoretically the two halves are independent (`entity_scope_exhaustiveness_is_not_infallibility`, `{}`), and the counterfactual sense is not forced by the foundational one (`exhaustive_scope_without_counterfactual_knowledge`, `{}`). Ordinary/classical omniscience stays out of reach: Γ has no `Knows` predicate, `Omniscience_AllTruths` / `Omniscience_Counterfactuals` (`DeepModalFrontier`) remain frontier vocabulary definitions, and `Entity.ofGround` is not a subject correlate (`ofGround_ne_ofSubject`) — the prose disclaimer (`README-OLD.md:263`; `CHARS.md` §14) is preserved, no divine knowledge bridge is manufactured. — [DivineOmniscience.lean#ofGround_not_truth_tracking](formal/Logos/DivineOmniscience.lean#L144), footprint {Means, Subject} ; [DivineOmniscience.lean#exhaustive_scope_without_counterfactual_knowledge](formal/Logos/DivineOmniscience.lean#L242), footprint {} ; [DeepModalFrontier.lean#Omniscience_AllTruths](formal/Logos/DeepModalFrontier.lean#L313), footprint {} ; [DeepModalFrontier.lean#Omniscience_Counterfactuals](formal/Logos/DeepModalFrontier.lean#L317), footprint {} |
| **Foundational omnipotence** (operative scope: no non-contradictory state of affairs is closed to the ground) | Divine Being / Ground | ✅ PROVEN ◈ | In `DivineOmnipotence.lean` (footprint `{Means, NecessarySubjectKind, Subject, propext}` — VOCAB only, the `propext` cost inherited from `Semantics.nonContradiction`, C14), `ofGround_foundational_omnipotence` establishes the *orthodox* classical sense of omnipotence for `Entity.ofGround` (Aquinas *ST* I, q. 25, a. 5, ad 1 — *semper et ubique operans*) at 0 substantive axioms: power over whatever does not involve a contradiction. The scope is *operative*, in the sense that no state of affairs satisfiable in any accessible world is closed to the ground (`ofGround_gapless_operative_scope`, `{NecessarySubjectKind, Subject}`), with the two non-contradictory horns made explicit: nothing unobtained — hence nothing unsatisfiable — is operated (`ofGround_operates_only_what_obtains`, `{NecessarySubjectKind, Subject}`) and no contradiction is ever operated (`ofGround_does_not_operate_contradictions`, `{NecessarySubjectKind, Subject, propext}`). The reading is substantive rather than vacuous, since the scope domain is machine-checked non-empty and contradiction-free (`satisfiable_scope_is_nonempty_and_contradiction_free`, `{propext}`), and the ground is gapless alongside the necessary-kind subjects (`gapless_operators_are_ground_or_necessary_kind`, `{NecessarySubjectKind, Subject}`, with `atom_not_gapless_operate` and `discriminating_subject_not_gapless_operate` excluding atoms and contingent-kind subjects). Only the contradiction-omni reading — power over everything conceivable, *including contradictions* — is refuted, and it is refuted *by* the orthodox restriction, not against it. Honest boundary, priced not hidden: Γ has no causal production relation, so `OperatesAt v e P := ExistsAt v e ∧ P v` reads *operates* as presence plus obtaining, and is registered as a priced stipulation ◈ `operatesAt_presencePlusObtaining` (`Tag: SEM`). That price is machine-checked, not asserted: `existence_everywhere_does_not_entail_operation` (`{}`) shows an entity present in every world can still operate nothing, and `exhaustive_scope_without_operative_scope` (`{}`) shows exhaustive meaning scope does not entail operative scope — so the result is proved from world-rigid presence, never read off the meaning-exhaustive scope of `DivineOmniscience`. `gapless_operative_scope_without_conjunctive_power` (`{}`) further bounds the claim: modal accessibility is not conjunctive, so gapless scope does not entail jointly-possible pairs. See the next row for the causal sense. — [DivineOmnipotence.lean#ofGround_foundational_omnipotence](formal/Logos/DivineOmnipotence.lean#L306), footprint {Means, NecessarySubjectKind, Subject, CL} ; [DivineOmnipotence.lean#ofGround_gapless_operative_scope](formal/Logos/DivineOmnipotence.lean#L177), footprint {NecessarySubjectKind, Subject} ; [DivineOmnipotence.lean#ofGround_operates_only_what_obtains](formal/Logos/DivineOmnipotence.lean#L187), footprint {NecessarySubjectKind, Subject} ; [DivineOmnipotence.lean#ofGround_does_not_operate_contradictions](formal/Logos/DivineOmnipotence.lean#L201), footprint {NecessarySubjectKind, Subject, CL} ; [DivineOmnipotence.lean#atom_not_gapless_operate](formal/Logos/DivineOmnipotence.lean#L220), footprint {NecessarySubjectKind, Subject} ; [DivineOmnipotence.lean#discriminating_subject_not_gapless_operate](formal/Logos/DivineOmnipotence.lean#L236), footprint {NecessarySubjectKind, Subject} ; [DivineOmnipotence.lean#gapless_operators_are_ground_or_necessary_kind](formal/Logos/DivineOmnipotence.lean#L258), footprint {NecessarySubjectKind, Subject} ; [DivineOmnipotence.lean#necessity_and_presence_yield_foundational_omnipotence](formal/Logos/DivineOmnipotence.lean#L320), footprint {Means, NecessarySubjectKind, Subject, CL} ; [DivineOmnipotence.lean#satisfiable_scope_is_nonempty_and_contradiction_free](formal/Logos/DivineOmnipotence.lean#L351), footprint {CL} ; [DivineOmnipotence.lean#existence_everywhere_does_not_entail_operation](formal/Logos/DivineOmnipotence.lean#L150), footprint {} ; [DivineOmnipotence.lean#gapless_operative_scope_without_conjunctive_power](formal/Logos/DivineOmnipotence.lean#L367), footprint {} ; [DivineOmnipotence.lean#exhaustive_scope_without_operative_scope](formal/Logos/DivineOmnipotence.lean#L394), footprint {} |
| **Causal / creative omnipotence** ("can bring X about", not "is present where X obtains") | Divine Being / Ground | ❌ NOT ESTABLISHED | No live theorem, and the prose disclaimer (`README-OLD.md:263`; `CHARS.md` §15) is **retained — but narrowed to this causal sense only**, since the non-contradictory sense above is now PROVEN. Γ declares no entity-level production relation: the only initiation relation is `Agency.Initiates : Subject → State → State → Prop → Prop` (`Agency.lean:168`, VOCAB), which is subject-indexed, and `Entity.ofGround` is provably not a subject correlate (`ofGround_ne_ofSubject`, `NecessityEternity.lean:160`), so it cannot be instantiated by the ground at all. The closest relation Γ has is explanatory containment `GroundsEntity` (`RecoveredOntologicalGround.lean:57`, *esse est agere*), and `exhaustive_scope_without_operative_scope` (`{}`) already machine-checks that omni-scope does not entail selection power, so it must not be weakened to that. BLOCKED with both exact missing statements recorded (GAPMAP Level 17, row F10). |
| **Creator of contingent reality** | Divine Being / Ground | 🧱 INDEPENDENT | `necessary_ground ⇏ contingent_creation`, **on a populated world** (footprint `{}`): a necessary ground that grounds *every* content may still create nothing, so the ground does not entail a creation record. (Ledger target F9 DEFERRED.) **This is not the empty world, and the kernel never claimed it was.** `the_creation_countermodel_is_a_populated_contingent_world` proves the separating world contains a subject that is genuinely contingent, and `a_populated_contingent_world_can_also_carry_creation` is its positive counterpart — so the entailment is undetermined in *both* directions, not refuted-and-replaced. The countermodel is a free structure, **not a model of Γ and not a candidate for reality**; the empty world is separately refuted by C355 once a necessary entity exists. **Existence vs entailment, kept apart:** the *existence* of a contingent realm is a **theorem of Γ** — and, since 2026-09-27 (lot COSMOS-EXISTENCE-IS-FREE), a **free** one: `CosmicExistence.contingent_realm_obtains` (C350, `PROVEN` at `{propext, Subject}`, witnessed by an atom, no bridge) — while its being a bearer of content is the separate `CosmicExistence.cosmos_obtains` (C367, `PROVEN` given an exhibited contingent person; conditionally satisfiable per C354, non-trivial in shape per C353). So what stays COUNTERMODEL here is the *entailment* from the ground, not the existence. **These two facts are independent and both hold**: Γ proves a contingent realm exists at no price at all, and Γ refutes that a necessary ground alone entails a creation record. The ground loves the cosmos under declared prices (C351/C352); it does not derive the cosmos from itself, and no production is claimed. — [ConditionalTheology.lean#necessary_ground_not_entails_contingent_creation](formal/Logos/ConditionalTheology.lean#L616), footprint {} ; [CosmicExistence.lean#contingent_realm_obtains](formal/Logos/CosmicExistence.lean#L266), footprint {NecessarySubjectKind, Subject, CL} ; [CosmicExistence.lean#cosmos_obtains](formal/Logos/CosmicExistence.lean#L412), footprint {Means, NecessarySubjectKind, Subject, Will, subjectWill, CL} ; [CosmicExistence.lean#the_ground_loves_the_cosmos](formal/Logos/CosmicExistence.lean#L559), footprint {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, Will, subjectWill, CL} |
| **Three Divine Persons (Trinity)** | Divine Personhood | 🧱 INDEPENDENT | `preceding_theory ⇏ trinity` (Binitarian separation model, footprint `{}`). A separate claim, distinct from necessity and from unity. (F6/F8 DEFERRED; plurality `T12_twoPersons` is at most generic persons under `AxTwoSubjects`.) — [ConditionalTheology.lean#preceding_theory_not_entails_trinity](formal/Logos/ConditionalTheology.lean#L336), footprint {} |
| **Incarnation** | Divine Personhood | 🧱 INDEPENDENT | `preceding_theory ⇏ incarnation` (Unincarnate model, footprint `{}`). (F9 DEFERRED.) — [ConditionalTheology.lean#preceding_theory_not_entails_incarnation](formal/Logos/ConditionalTheology.lean#L380), footprint {} |

### ASIETY-FREEDOM chain, step by step (every step priced)

> **Read this table before reading the asiety rows above.** The author's chain was:
> weak choice (Act-free) → **asiety** → *because of the nature of Him who grounds
> reality*, assert **`AsietyFreedom`** → which gives rise to **true choice** and
> **`AsietyFreeWill`** → *which is shared with us by the creator*. The **◈ row is the
> only step that is not a theorem**, and it is a declaration, not a derivation.

`L1` = the axiom-free Act-free route · `◈` = **the declared bridge, not a theorem** ·
`L2` = the transfers that depend on it · `🧱` = `{}` countermodel pricing it · `✓` =
coherence · `Σ` = master summary.

| # | Ledger | Declaration | Step | Status | Kernel footprint |
|---|---|---|---|---|---|
| L1 | C287 | [AsietyFreedom.lean#weakChoice_implies_asiety](formal/Logos/AsietyFreedom.lean#L150), footprint {Means, Subject} | `GenuineNormativity s p q → Asiety (EntityOf s)` — weak choice, **Act-free** | ✅ PROVEN | {Means, Subject} |
| L1 | C288 | [AsietyFreedom.lean#weakChoice_implies_freeWill](formal/Logos/AsietyFreedom.lean#L159), footprint {Means, Subject} | the same step read toward free will | ✅ PROVEN | {Means, Subject} |
| ◈ | — | [AsietyFreedom.lean#AsietyFreedomOfGround](formal/Logos/AsietyFreedom.lean#L119), footprint {Means, Subject} | **THE BRIDGE, BY DECLARATION**: the ground's freedom reaches every subject | ◈ STIPULATED (META) — a `def`, **not an axiom** | {Means, Subject} |
| L2 | C289 | [AsietyFreedom.lean#asietyFreedom_yields_trueChoice](formal/Logos/AsietyFreedom.lean#L176), footprint {Means, Subject} | `AsietyFreedomOfGround → TrueChoice s p q` (conditional) | ✅ PROVEN ◈ | {Means, Subject} |
| L2 | C290 | [AsietyFreedom.lean#asietyFreedom_yields_asietyFreeWill](formal/Logos/AsietyFreedom.lean#L192), footprint {Means, Subject} | `AsietyFreedomOfGround → AsietyFreeWill s` — the *"shared with us by the creator"* step | ✅ PROVEN ◈ | {Means, Subject} |
| L2 | C291 | [AsietyFreedom.lean#asietyFreeWill_yields_trueChoice](formal/Logos/AsietyFreedom.lean#L202), footprint {Means, Subject} | `AsietyFreeWill s → TrueChoice s p q`, and back again | ✅ PROVEN ◈ | {Means, Subject} |
| 🧱 | C292 | [AsietyFreedom.lean#asietyAloneDoesNotYieldTrueChoice](formal/Logos/AsietyFreedom.lean#L221), footprint {} | countermodel: asiety alone yields no true choice — the universal reading is strictly stronger than the existential one | 🧱 INDEPENDENT | {} |
| 🧱 | C293 | [AsietyFreedom.lean#frameContingencyDoesNotBindAPair](formal/Logos/AsietyFreedom.lean#L244), footprint {} | countermodel: frame contingency binds no given pair — why `TrueChoice ≡ Chooses` is forced, not lazy | 🧱 INDEPENDENT | {} |
| 🧱 | C294 | [AsietyFreedom.lean#rightWrongFactYieldsNoChooser](formal/Logos/AsietyFreedom.lean#L265), footprint {} | countermodel: `¬ N_T ∧ ¬ N_F` with **no** subject meaning anything — **no axiom-free existence of a chooser** | 🧱 INDEPENDENT | {} |
| ✓ | C295 | [AsietyFreedom.lean#groundIsNotASharerOfAsietyFreeWill](formal/Logos/AsietyFreedom.lean#L283), footprint {Means, Subject} | coherence: the ground is still **not** a chooser (C285 preserved) | ✅ PROVEN | {Means, Subject} |
| Σ | C296 | [AsietyFreedom.lean#asietyFreedom_summary](formal/Logos/AsietyFreedom.lean#L296), footprint {Means, Subject} | master summary: the whole chain and both its prices in one statement | ✅ PROVEN ◈ | {Means, Subject} |
| L1 | C300 | [AsietyFreedom.lean#weakChoice_yields_trueChoice](formal/Logos/AsietyFreedom.lean#L358), footprint {Means, Subject} | **the derived side at its actual maximum**: `GenuineNormativity s p q → TrueChoice s p q` — axiom-free, no ◈, true choice **at the specified pair**. The hypothesis already contains the choice; only the `{}` frame fact `ContestedContent` is added. **So the pair's existence is free — what ◈ buys is the extension from the given pair to every incompatible pair** | ✅ PROVEN | {Means, Subject} |
| L1 | C297 | [AsietyFreedom.lean#asiety_yields_witnessed_trueChoice](formal/Logos/AsietyFreedom.lean#L385), footprint {Means, Subject} | the same boundary via `Asiety`: `Asiety (EntityOf s) → ∃ p q, TrueChoice s p q`. **Strictly weaker than C300** (it discards *which* pair); retained, not deleted | ✅ PROVEN | {Means, Subject} |
| L1 | C298 | [AsietyFreedom.lean#asiety_yields_freeWill](formal/Logos/AsietyFreedom.lean#L396), footprint {Means, Subject} | and in the `FreeWill` direction: `Asiety (EntityOf s) → FreeWill s`, equally bounded | ✅ PROVEN | {Means, Subject} |
| 🧱 | C299 | [AsietyFreedom.lean#groundingCannotDeliverTrueChoice](formal/Logos/AsietyFreedom.lean#L424), footprint {} | countermodel: **no grounding premise of containment shape can deliver true choice** — the grounding premise is granted *in full* and the conclusion still fails. Machine-checked reason the ◈ step is `BLOCKED`. Scope limit: relations of *other* shape stay open (F12(1)) | 🧱 INDEPENDENT | {} |

**Cost of ◈ `asietyFreedom_ofGroundFreedom`** (`AsietyFreedom.lean:119`), as registered: The ground's being the ground of freedom is declared, not derived: GroundsEntity is vacuous, GroundsRightWrong is definitionally FreeWill (C168), and substantive grounding is BLOCKED (C228). Priced by three {} countermodels; the universal reading is strictly stronger than the existential one.

**Two limits that the badge alone does not convey, and which are the reason this
block exists:**

1. **"The declared-axiom count did not move" is NOT a test for this batch.** The
   bridge is a `def`, so `#print axioms` cannot see it, and its `{Means, Subject}`
   footprint is vocabulary-only *whether the bridge is principled or arbitrary*. For
   ASIETIC-CHOICE the invariant was a genuine test; here the **◈ registry entry and
   this block are load-bearing rather than decorative**. That is a limitation of the
   auditing instrument, declared rather than exploited.
2. **The `GroundsEntity` premise of the three transfers is vacuous**
   (`ground_grounds_the_meaningless`: the ground grounds even entities bearing no
   meaning), so the whole metaphysical weight sits on the ◈ row. It is named `_hG` and
   declared vacuous rather than quietly dropped, so the footprint cannot be mistaken for
   depth. The only non-vacuous `GroundsEntity` use in the module is C295, which is a
   `¬ ∃ s` over subjects.

**Also not claimed:** the universal reading of the ◈ bridge is strictly stronger than
an existential one ("shared with *someone*"), and nothing here shows the stronger
reading is the correct one; no axiom-free existence of a chooser (C294 **refutes** it,
it is not merely open); and the Act-free `?` around `base.txt`'s `ClaimsCorrect`-free
weak→strong step is **bypassed, not closed** — the bare form stays machine-refuted
(C273/C274).

### SEMANTIC-FINITUDE chain, step by step (F15 declared as a vocabulary axiom)

> **Read this table before reading any unicity/ground row above.** Γ has a ground of
> reality, and on the **declared** bound that no subject means every proposition, that
> ground is the **sole** universal ground. The bound is the **C388 row**, and it is a
> **declaration, not a derivation** — the 27th axiom, tagged `VOCAB`. A reader must not
> read the `L2` rows as a proof of monotheism, and must not read `VOCAB` as "axiom-free".

`◆` = **the declared bound, not a theorem** · `L2` = a theorem resting on the bound
· `🧱` = `{}` countermodel pricing it · `✓` = coherence.

| # | Ledger | Declaration | Step | Status | Kernel footprint |
|---|---|---|---|---|---|
| ◆ | C388 | [SemanticFinitude.lean#SemanticFinitude](formal/Logos/SemanticFinitude.lean#L151), footprint {Means, SemanticFinitude, Subject} | **THE F15 BOUND, BY DECLARATION** — the 27th axiom, `Tag: VOCAB`: no subject means every proposition, so no creature is semantically omnipotent. Paid as an anonymous premise in 19 declarations across the five attribute modules (14 carrying the exact ∀-form) before it was named; now declared, and its price is in every dependent footprint | ◆ AXIOM | {Means, SemanticFinitude, Subject} |
| L2 | C389 | [SemanticFinitude.lean#exactly_one_universal_modal_ground_stipulated](formal/Logos/SemanticFinitude.lean#L170), footprint {Means, NecessarySubjectKind, SemanticFinitude, Subject} | **the unicity of the ground of all reality**, an unconditional theorem of Γ | ✅ PROVEN | {Means, NecessarySubjectKind, SemanticFinitude, Subject} |
| L2 | C390 | [SemanticFinitude.lean#ofGround_sole_universal_grounding_stipulated](formal/Logos/SemanticFinitude.lean#L178), footprint {Means, NecessarySubjectKind, SemanticFinitude, Subject} | sole universal grounding of reality | ✅ PROVEN | {Means, NecessarySubjectKind, SemanticFinitude, Subject} |
| L2 | C391 | [SemanticFinitude.lean#conditional_canonical_aseity_stipulated](formal/Logos/SemanticFinitude.lean#L184), footprint {Means, SemanticFinitude, Subject} | canonical aseity of the ground | ✅ PROVEN | {Means, SemanticFinitude, Subject} |
| L2 | C392 | [SemanticFinitude.lean#ofGround_modal_aseity_conditional_stipulated](formal/Logos/SemanticFinitude.lean#L191), footprint {Means, NecessarySubjectKind, SemanticFinitude, Subject} | modal aseity of the ground w.r.t. `CanonicalExtDepAt` | ✅ PROVEN | {Means, NecessarySubjectKind, SemanticFinitude, Subject} |
| L2 | C393 | [SemanticFinitude.lean#ofGround_divine_pure_actuality_stipulated](formal/Logos/SemanticFinitude.lean#L197), footprint {Initiates, Means, NecessarySubjectKind, SemanticFinitude, State, Subject} | **divine pure actuality** (actus purus) of the ground | ✅ PROVEN | {Initiates, Means, NecessarySubjectKind, SemanticFinitude, State, Subject} |
| L2 | C394 | [SemanticFinitude.lean#ofGround_no_grounding_potency_stipulated](formal/Logos/SemanticFinitude.lean#L203), footprint {Means, SemanticFinitude, Subject} | zero passive grounding potency in the ground | ✅ PROVEN | {Means, SemanticFinitude, Subject} |
| L2 | C395 | [SemanticFinitude.lean#ofGround_divine_simplicity_stipulated](formal/Logos/SemanticFinitude.lean#L209), footprint {Means, SemanticFinitude, Subject, CL} | **divine simplicity** of the ground | ✅ PROVEN | {Means, SemanticFinitude, Subject, CL} |
| L2 | C396 | [SemanticFinitude.lean#ofGround_non_composite_stipulated](formal/Logos/SemanticFinitude.lean#L216), footprint {Means, SemanticFinitude, Subject, CL} | mereological non-compositeness of the ground | ✅ PROVEN | {Means, SemanticFinitude, Subject, CL} |
| L2 | C397 | [SemanticFinitude.lean#ofGround_simplicity_and_transcendence_stipulated](formal/Logos/SemanticFinitude.lean#L222), footprint {Means, SemanticFinitude, Subject, CL} | divine simplicity **and** ontological transcendence of the ground | ✅ PROVEN | {Means, SemanticFinitude, Subject, CL} |
| L2 | C398 | [SemanticFinitude.lean#ground_is_canonically_aseitous_but_not_asietic_stipulated](formal/Logos/SemanticFinitude.lean#L229), footprint {Means, SemanticFinitude, Subject} | canonically aseitous but not itself asietic | ✅ PROVEN | {Means, SemanticFinitude, Subject} |
| 🧱 | C399 | [SemanticFinitude.lean#semantic_omnipotence_is_consistent](formal/Logos/SemanticFinitude.lean#L244), footprint {} | countermodel: a semantically omnipotent carrier is a model of the negation — the bound is **falsifiable, not vacuous**, so the unicity really rests on it | 🧱 INDEPENDENT | {} |
| ✓ | C400 | [SemanticFinitude.lean#semanticFinitude_excludes_ground_from_subjects](formal/Logos/SemanticFinitude.lean#L262), footprint {Means, SemanticFinitude, Subject} | coherence: `ofGround_meansAll` gives the ground *every* proposition, so the bound is exactly what keeps the ground off the `Subject` sort | ✅ PROVEN | {Means, SemanticFinitude, Subject} |

**Cost of the C388 declaration** (`formal/Logos/SemanticFinitude.lean`), as declared:
one axiom, `Tag: VOCAB` — it bounds a single uninterpreted relation `Means` on a single
nullary sort `Subject` and asserts no connection between entities. It is priced in every
dependent footprint below, and the declared-axiom count moved **26 → 27** when it was
promoted. The ten `L2` rows keep the `PROVEN` badge they had as stipulations because the
generator treats only `SEM`/`META`/`TRANS` as substantive; `VOCAB` yields `PROVEN`.

**Four limits that the badge alone does not convey, and which are the reason this
block exists:**

1. **The price was invisible until this batch, and that was the defect.** As a `def` of a
   `Prop` taken as a premise, the bound was reported by `#print axioms` as the *same*
   footprint as the corresponding pre-existing conditional theorem, the axiom count was
   unmoved, and the ◈ badge was the only signal. It is now a declared axiom, so the price
   is in every dependent footprint. The count moving 26 → 27 is what a price looks like
   when it is honestly charged; its earlier stillness was the point, not a pass.
2. **The ten `L2` rows are unconditional theorems, not corollaries.** The ten original
   conditional theorems (`exactly_one_universal_modal_ground`, `ofGround_divine_simplicity`,
   …) are **not** edited and keep their anonymous premise; the `L2` rows are the same
   theorems keyed to the *named* bound, which declaring it turned into theorems of Γ in
   their own right. The `_stipulated` suffix is historical and is kept only because the
   ledger and the prose corpus cite these names.
3. **The bound is falsifiable, not vacuous** (`🧱 semantic_omnipotence_is_consistent`,
   `{}`): a semantically omnipotent carrier is a model of its negation, so the unicity
   genuinely rests on the bound — which is why the bound must be declared, not assumed.
   It is also *load-bearing* in the other direction (`✓`): `ofGround_meansAll` gives the
   ground every proposition, so the bound is exactly what keeps it off the `Subject` sort.
4. **What is still NOT claimed.** `Tag: VOCAB` says the bound restricts one uninterpreted
   relation on one nullary sort (`Means` on `Subject`) and asserts no connection between
   entities — the same status as `ofGround_existsAt`; if the author re-tags it `SEM` the
   badge follows and the ten theorems drop to `⚠️`. Personhood of the ground (C228),
   Trinity (F6/F8) and *explanatory* grounding (C326/C328) are untouched and remain
   BLOCKED / DEFERRED / not attempted. This batch does not move existence, which was
   already `PROVEN` unconditionally.

### MEANING-RETORSION chain, step by step (the "there is no meaning" thesis)

> **The demand:** *to affirm that there is no meaning is to prove the invalidity of my
> own affirmation* — and *the countermodel is wrong, and you shall prove it*. Both are
> discharged here, and the second only in the form in which it is true. The affirmation
> is refuted (4/4). The countermodel is refuted **as an answer** (3a/3b) and is
> **preserved as a model** (3c). A reader who takes 3a as a refutation of the model has
> misread the chain; 3c is the row that forbids it.

`§0` = the re-index · `1/4…4/4` = the ladder, ascending in strength · `+` = the positive
existence form · `3a/3b` = the refutation *as an answer* · `3c` = the complement that
keeps it honest · `🧱` = `{}` countermodel.

| # | Ledger | Declaration | Step | Status | Kernel footprint |
|---|---|---|---|---|---|
| §0 | C368 | [MeaningRetorsion.lean#NoMeaning](formal/Logos/MeaningRetorsion.lean#L101), footprint {Means, Subject} | **THE THESIS ITSELF**, stated in Γ's own `Meaning_I` vocabulary — `base.txt` §26 item 3 ("Não existe conteúdo") and `poem.txt` P3 ("há significado") | ✅ PROVEN | {Means, Subject} |
| §0 | C369 | [MeaningRetorsion.lean#noMeaning_iff_noIntentionalSubject](formal/Logos/MeaningRetorsion.lean#L115), footprint {Means, Subject} | the thesis **is** the audited negation of the retorsive conclusion, re-indexed (two existential quantifiers swapped — no `propext`) | ✅ PROVEN | {Means, Subject} |
| §0 | C370 | [MeaningRetorsion.lean#noMeaning_iff_pointwise](formal/Logos/MeaningRetorsion.lean#L130), footprint {Means, Subject} | pointwise form: no subject means anything at all | ✅ PROVEN | {Means, Subject} |
| 1/4 | C371 | [MeaningRetorsion.lean#noMeaning_is_unmeaned](formal/Logos/MeaningRetorsion.lean#L174), footprint {Means, Subject} | the thesis cannot be **meant** (consistent — a universal negative is not a liar) | ✅ PROVEN | {Means, Subject} |
| 2/4 | C372 | [MeaningRetorsion.lean#noMeaning_is_unperformed](formal/Logos/MeaningRetorsion.lean#L181), footprint {Initiates, Means, State, Subject} | the thesis cannot be **acted** | ✅ PROVEN | {Initiates, Means, State, Subject} |
| 3/4 | C373 | [MeaningRetorsion.lean#no_correct_judgment_of_noMeaning](formal/Logos/MeaningRetorsion.lean#L194), footprint {Initiates, Means, State, Subject} | the thesis cannot be **judged correct** — NEW: no `Correct` rung existed for any meaninglessness thesis | ✅ PROVEN | {Initiates, Means, State, Subject} |
| 3'/4 | C374 | [MeaningRetorsion.lean#judgment_of_noMeaning_is_incorrect](formal/Logos/MeaningRetorsion.lean#L207), footprint {Initiates, Means, State, Subject} | whoever judges the thesis at all judges it **incorrectly** (exhaustive form) | ✅ PROVEN | {Initiates, Means, State, Subject} |
| 4/4 | C375 | [MeaningRetorsion.lean#noMeaning_is_unassertable](formal/Logos/MeaningRetorsion.lean#L224), footprint {Initiates, Means, State, Subject} | **THE RETORSION, unconditional**: nobody can hold the thesis as correct — no hypothesis, no subject, no bridge, **no new axiom** | ✅ PROVEN | {Initiates, Means, State, Subject} |
| 4/4 | C376 | [MeaningRetorsion.lean#noMeaning_ladder](formal/Logos/MeaningRetorsion.lean#L231), footprint {Initiates, Means, State, Subject} | all four rungs in one conjunction | ✅ PROVEN | {Initiates, Means, State, Subject} |
| + | C377 | [MeaningRetorsion.lean#affirms_noMeaning_yields_meaning](formal/Logos/MeaningRetorsion.lean#L262), footprint {Initiates, Means, State, Subject} | the author's sentence, positively: **affirming the thesis produces an instance of what the thesis denies**. Hypothesis `Act` (generalized from `Asserts` 2026-09-27, which is the special case) — the performance, not the performance-plus-success C375 denies | ✅ PROVEN | {Initiates, Means, State, Subject} |
| + | C378 | [MeaningRetorsion.lean#judges_noMeaning_yields_meaning](formal/Logos/MeaningRetorsion.lean#L271), footprint {Initiates, Means, State, Subject} | the same at the judging level — the form `poem.txt` P3 uses | ✅ PROVEN | {Initiates, Means, State, Subject} |
| 3a | C379 | [MeaningRetorsion.lean#no_countermodel_can_affirm_the_thesis](formal/Logos/MeaningRetorsion.lean#L319), footprint {} | **no** meaning-vocabulary, of any shape, can host an affirmation of the thesis (*a corollary* of `level2_signature_asserts_noi_selfRefutes`, generalised) | ✅ PROVEN | {} |
| 3b | — | [MeaningRetorsion.lean#NoWeakActIn](formal/Logos/MeaningRetorsion.lean#L331), footprint {} | the denial of the act-datum, in an arbitrary signature — the withholding that distinguishes M1 from any `Means`-vocabulary | ✅ PROVEN | {} |
| 3b | C380 | [MeaningRetorsion.lean#signature_weak_retorsion](formal/Logos/MeaningRetorsion.lean#L339), footprint {} | the **weak** retorsion, signature-general — NEW: `Agency.noWeakAct_selfRefutes` is canonical-only | ✅ PROVEN | {} |
| 3b | C381 | [MeaningRetorsion.lean#the_two_denials_cannot_both_be_affirmed](formal/Logos/MeaningRetorsion.lean#L354), footprint {} | **THE JOINT REFUTATION, one sentence**: deny the act-datum, then affirm the denial — impossible. This is M1 and C294 refuted as *answers* | ✅ PROVEN | {} |
| 3c | C382 | [MeaningRetorsion.lean#the_meaningless_world_remains_a_model](formal/Logos/MeaningRetorsion.lean#L385), footprint {} | **THE COMPLEMENT, populated**: a world *with subjects* where the thesis is true and no assertion of it succeeds. A **model, not a refutation** — and the machine-checked reason the content survives | 🧱 INDEPENDENT | {} |
| 3c | C383 | [MeaningRetorsion.lean#countermodel_is_a_world_where_the_thesis_is_unutterable](formal/Logos/MeaningRetorsion.lean#L410), footprint {} | both halves together: the countermodel's world is a world where the thesis is true **and** no assertion of it succeeds. *"Unutterable" is not a prohibition on the type:* the sentence is well-formed and the author utters it — what is excluded is the assertion *succeeding* | ✅ PROVEN | {} |
| 3d | C384 | [MeaningRetorsion.lean#Voices](formal/Logos/MeaningRetorsion.lean#L154), footprint {Subject, act} | **THE PERFORMANCE WITHOUT THE SUCCESS CONDITION** — the author's "it can be uttered, it can be asserted". The predicate Γ lacked: every `asserts` in the corpus carries `∧ p`, so *assert* had come to mean *correctly assert*. What the performative contradiction leaves standing, since C375 refutes only the act *succeeding* | ✅ PROVEN | {Subject, act} |
| 3d | C385 | [MeaningRetorsion.lean#the_thesis_is_utterable_though_not_assertable](formal/Logos/MeaningRetorsion.lean#L445), footprint {} | **AND THE WORLD IN WHICH THE THESIS IS UTTERED**: 3c with `act := True`. A subject, nothing meant, the thesis true, the thesis *said* — and still no assertion of it that succeeds. This is what makes 3c's word "unutterable" a misnomer rather than a reading | 🧱 INDEPENDENT | {} |
| 4 | C401 | [MeaningRetorsion.lean#noMeaning_is_refuted_from_plurality](formal/Logos/MeaningRetorsion.lean#L490), footprint {AxTwoSubjects, Means, Subject, Will, subjectWill} | **THE REFUTATION — the no-meaning world is not possible in Γ**: `Meaning_I p` is definitionally `∃ s, Means s p`, so `cogito_from_T12` is already a counterexample to the thesis, three lines that were never written down. NOT axiom-free — C382 *is* the proof nothing in the bare vocabulary refutes it. What C382 shows is a free signature's consistency; what this shows is the thesis does not survive *the theory*, on the plurality bridge | ⚠️ AXIOMATIC | {AxTwoSubjects, Means, Subject, Will, subjectWill} |
| 4 | C402 | [MeaningRetorsion.lean#noMeaning_is_refuted_from_the_act_datum](formal/Logos/MeaningRetorsion.lean#L508), footprint {Initiates, Means, State, Subject} | **the same refutation on the act-datum, no META bridge**: whoever grants that an act occurred grants the falsity with it, since `Act` already contains `Means`. Conditional, bridge-free, price relocated to ◈ `performativeActDatum` — free in axioms, not free in performance | ✅ PROVEN ◈ | {Initiates, Means, State, Subject} |

**Five limits the badges do not convey, and the reason this block exists:**

1. **The retorsion is unconditional but not free.** 4/4 has no hypothesis and no new
   axiom — its footprint is vocabulary only. But the contradiction is fed *by* the
   affirmation: `Asserts s NoMeaning → False` needs the affirmation as input. The
   retorsion is **free in axioms and not free in performance**. That is the honest
   reading of the author's sentence, and it is also the whole price.
   **So "unutterable" is not a prohibition on the sentence.** The sentence is
   well-formed, the author utters it, and 4/4 is discharged by that very utterance:
   the antecedent is supplied and the contradiction follows. What C375 excludes is an
   assertion *succeeding* — an assertion that holds its content — not an assertion
   being made. Uttering the thesis is exactly what triggers the retorsion.
2. **The thesis is NOT shown false.** `¬ NoMeaning` is not derivable and is not
   claimed. 3c exhibits a **populated** world (`Subject := Unit`, against M0's empty
   sort) in which the thesis is true and no assertion of it succeeds. So the content
   survives intact; only the *affirming* of it fails to land. This is the corpus's own
   distinction (`NegativeRetorsionAudit.lean:292-295`): `NoI is false` is **not**
   equivalent to `NoI is unassertable`.
3. **3a is a corollary and is labelled one.** `no_countermodel_can_affirm_the_thesis`
   is `level2_signature_asserts_noi_selfRefutes` (`:286`) generalised from one signature
   to all of them. The batch's novelty is C369 (the re-index), C373 (the `Correct` rung),
   C380 (the signature-general weak retorsion) and C382 (the populated complement).
4. **Why an *answer* and not a *model*.** A countermodel is not a counterexample; it is
   a description of a world. An answer is a move made inside discourse. M1 and C294
   describe worlds where no move is ever made (`Means := False` *and* `act := False`),
   so they cannot contain the affirmation of their own silence. A content nobody can
   hold as correct is not a position; it is a description of a world in which nothing is
   ever held. **This is not a claim that meaninglessness is false.**
5. **Price of the positive claim is unmoved.** Nothing here carries `AxTwoSubjects` or
   `transcendental_reflection_intentional` — that is Batch B's one substantive claim
   about its own cost, and gate B2 verifies it rather than assuming it. But the
   *unconditional* existence of a meaning still costs `AxTwoSubjects` (C367); what is
   shown is that it is over-strong whenever an affirmation is supplied as input.

### LOVE chain, step by step (both prices, every step)

> **Read this table before reading the divine-love row above.** The author's chain was:
> axiom-free ground facts → **the missing vocabulary** (`GroundBearsGood`, PRICE 1) →
> **the declared bridge** (`AxGroundLovesContingentRealm`, PRICE 2) → which yields the
> inhabitants → while the separations say what was **not** bought, and the SEM datum
> (PRICE 3, sibling module) supplies the cosmos. The **◆ rows are axioms, not theorems**,
> and the two prices are different in kind: confusing them is the mistake the kernel
> audit cannot catch.

`L1` = no new vocabulary · `V` = consumes the VOCAB primitive, no substantive axiom ·
`◆` = **the axiom itself, not a theorem** · `L2` = the priced inhabitants · `S` =
separations · `D` = the SEM datum side · `🧱` = `{}` countermodel pricing the shape.

| # | Ledger | Declaration | Step | Status | Kernel footprint |
|---|---|---|---|---|---|
| L1 | C322 | [LovesAsGround.lean#falsityWorld_ne_actualWorld](formal/Logos/LovesAsGround.lean#L159), footprint {CL} | the single witness of modal fragility: the all-`TV.f` world is not the actual world | ✅ PROVEN | {CL} |
| L1 | C323 | [LovesAsGround.lean#an_atom_is_contingent](formal/Logos/LovesAsGround.lean#L167), footprint {NecessarySubjectKind, Subject, CL} | an atom is contingent — this is what makes C338 bite | ✅ PROVEN | {NecessarySubjectKind, Subject, CL} |
| L1 | C324 | [LovesAsGround.lean#a_contingent_entity_exists](formal/Logos/LovesAsGround.lean#L182), footprint {NecessarySubjectKind, Subject, CL} | bare contingency, witnessed by an atom — not the cosmos, not an object of love | ✅ PROVEN | {NecessarySubjectKind, Subject, CL} |
| L1 | C325 | [LovesAsGround.lean#a_meaningful_contingent_entity_exists](formal/Logos/LovesAsGround.lean#L195), footprint {Means, NecessarySubjectKind, Subject, CL} | a contingent entity bearing content exists — *consumes* a `Means` inhabitant, produces none | ✅ PROVEN | {Means, NecessarySubjectKind, Subject, CL} |
| L1 | C326 | [LovesAsGround.lean#ground_grounds_every_entity](formal/Logos/LovesAsGround.lean#L216), footprint {Means, Subject} | the ground grounds everything — proof is `intro p _; exact True.intro` | ✅ PROVEN | {Means, Subject} |
| L1 | C327 | [LovesAsGround.lean#atoms_bear_no_meaning](formal/Logos/LovesAsGround.lean#L222), footprint {Means, Subject} | an atom bears no meaning at all | ✅ PROVEN | {Means, Subject} |
| L1 | C328 | [LovesAsGround.lean#ground_grounds_the_meaningless](formal/Logos/LovesAsGround.lean#L231), footprint {Means, Subject} | the ground grounds even the meaningless — undiscriminating, *vacuously* | ✅ PROVEN | {Means, Subject} |
| L1 | — | [LovesAsGround.lean#the_ground_is_a_universal_modal_ground](formal/Logos/LovesAsGround.lean#L238), footprint {Means, NecessarySubjectKind, Subject} | **restates C204**; body is literally `ofGround_universal_modal_ground` — no second id | ✅ PROVEN | {Means, NecessarySubjectKind, Subject} |
| L1 | C329 | [LovesAsGround.lean#no_subject_is_a_necessary_entity](formal/Logos/LovesAsGround.lean#L249), footprint {NecessarySubjectKind, Subject, CL} | no *contingent-kind* person can occupy the necessary pole — kind-relative, discharges it with no love axiom | ✅ PROVEN | {NecessarySubjectKind, Subject, CL} |
| L1 | C330 | [LovesAsGround.lean#necessary_entities_are_ground_or_necessary_kind](formal/Logos/LovesAsGround.lean#L273), footprint {NecessarySubjectKind, Subject, CL} | **the necessary entities are the ground AND the necessary-kind subjects** (renamed 2026-09-28) — ground disjunct forced by the three-constructor ontology, subject disjunct the priced META bridge — structural fact, **not** evidence of love | ✅ PROVEN | {NecessarySubjectKind, Subject, CL} |
| V | — | [LovesAsGround.lean#GroundLoves](formal/Logos/LovesAsGround.lean#L339), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject} | **THE RELATION, ADDED NOT REUSED**: necessary lover, actual other, directed good, meaningful target, context `a` — `Loves` is `Subject`-indexed and the ground is no subject | ✅ PROVEN | {GroundBearsGood, Means, NecessarySubjectKind, Subject} |
| V | C331 | [LovesAsGround.lean#ground_love_requires_a_necessary_lover](formal/Logos/LovesAsGround.lean#L347), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject} | love is eternal *in the lover* — half of the poem's "também é necessário" | ✅ PROVEN | {GroundBearsGood, Means, NecessarySubjectKind, Subject} |
| V | C332 | [LovesAsGround.lean#ground_love_is_directed_at_another](formal/Logos/LovesAsGround.lean#L352), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject} | love is not self-regarding: actual target, other than the lover | ✅ PROVEN | {GroundBearsGood, Means, NecessarySubjectKind, Subject} |
| V | C333 | [LovesAsGround.lean#ground_love_bears_a_directional_good](formal/Logos/LovesAsGround.lean#L359), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject} | the conjunct with no first-order substitute — the one the inhabitation pays for | ✅ PROVEN | {GroundBearsGood, Means, NecessarySubjectKind, Subject} |
| V | C334 | [LovesAsGround.lean#ground_love_requires_a_meaningful_target](formal/Logos/LovesAsGround.lean#L367), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject} | the target bears content **of its own** — what separates love from mere capacity | ✅ PROVEN | {GroundBearsGood, Means, NecessarySubjectKind, Subject} |
| V | C335 | [LovesAsGround.lean#meaningless_entities_cannot_be_loved](formal/Logos/LovesAsGround.lean#L374), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject} | love cannot reach the meaningless, in any context | ✅ PROVEN | {GroundBearsGood, Means, NecessarySubjectKind, Subject} |
| V | C336 | [LovesAsGround.lean#grounding_reaches_what_love_cannot](formal/Logos/LovesAsGround.lean#L385), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject} | **the separation, in one statement** — the machine-checked content of "not *merely* a mathematical ground" | ✅ PROVEN | {GroundBearsGood, Means, NecessarySubjectKind, Subject} |
| V | C337 | [LovesAsGround.lean#grounding_is_total_but_love_is_not](formal/Logos/LovesAsGround.lean#L393), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} | the totals separate — read with C338 as a pair, not a single step | ✅ PROVEN | {GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} |
| V | C338 | [LovesAsGround.lean#meaningful_love_bridge_is_refuted](formal/Logos/LovesAsGround.lean#L413), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} | **REFUTATION OF THE ATTRACTIVE FORM**: the unrestricted bridge is false in Γ — the only justification for the axiom's meaning hypothesis | ✅ PROVEN | {GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} |
| ◆ | C349 | [LovesAsGround.lean#GroundBearsGood](formal/Logos/LovesAsGround.lean#L323), footprint {GroundBearsGood, Subject} | **PRICE 1, VOCABULARY**: the directed-good primitive — constrains nothing, names what is missing | ◆ AXIOM (VOCAB) — a declared axiom, **not a theorem** | {GroundBearsGood, Subject} |
| ◆ | C339 | [LovesAsGround.lean#AxGroundLovesContingentRealm](formal/Logos/LovesAsGround.lean#L449), footprint {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject} | **PRICE 2, SUBSTANCE**: the inhabitation — genuinely not forced, genuinely not trivial | ◆ AXIOM (META) — a declared axiom, **not a theorem** | {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject} |
| L2 | C340 | [LovesAsGround.lean#the_ground_loves_every_meaningful_contingent_reality](formal/Logos/LovesAsGround.lean#L456), footprint {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject} | the bridge, applied — the ground's love as a *conclusion*, first time in the corpus | ⚠️ AXIOMATIC | {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject} |
| L2 | C341 | [LovesAsGround.lean#the_ground_bears_a_directional_good_toward_the_cosmos](formal/Logos/LovesAsGround.lean#L466), footprint {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject} | the content, unwrapped — where the whole price sits | ⚠️ AXIOMATIC | {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject} |
| L2 | C342 | [LovesAsGround.lean#the_ground_is_a_liver](formal/Logos/LovesAsGround.lean#L478), footprint {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} | the inhabitants, with the price visible — identifies nothing with the cosmos | ⚠️ AXIOMATIC | {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} |
| L2 | C343 | [LovesAsGround.lean#the_ground_is_a_necessary_and_chosen_lover](formal/Logos/LovesAsGround.lean#L493), footprint {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} | **the "necessary ∧ chosen" cell, occupied** — necessity forced, choice exactly the bridge | ⚠️ AXIOMATIC | {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} |
| S | C344 | [LovesAsGround.lean#the_ground_is_not_a_person](formal/Logos/LovesAsGround.lean#L517), footprint {Subject} | the ground-*constructor* is not a subject-correlate — constructor separation, re-scoped 2026-09-28; the necessary-kind person is a *different* entity, so no identification is made | ✅ PROVEN | {Subject} |
| S | C345 | [LovesAsGround.lean#ground_love_does_not_identify_a_person](formal/Logos/LovesAsGround.lean#L525), footprint {Subject} | the inhabitation cannot be read as a claim about a person | ✅ PROVEN | {Subject} |
| S | C346 | [LovesAsGround.lean#subject_love_is_not_ground_love](formal/Logos/LovesAsGround.lean#L536), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} | **contingent interpersonal love never yields ground-level love** — disjoint on the contingent side | ✅ PROVEN | {GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} |
| S | C347 | [LovesAsGround.lean#interpersonal_love_never_reaches_the_necessary_quadrant](formal/Logos/LovesAsGround.lean#L547), footprint {NecessarySubjectKind, Subject, CL} | no amount of *contingent* interpersonal love populates the necessary quadrant — the necessary kind can | ✅ PROVEN | {NecessarySubjectKind, Subject, CL} |
| S | C348 | [LovesAsGround.lean#ground_love_cannot_be_read_as_person_love](formal/Logos/LovesAsGround.lean#L561), footprint {GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} | **the transfer to the contingent kind is unstatable, not merely blocked** — bridge #9 / C228 untouched | ✅ PROVEN | {GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} |
| V | — | [LovesAsGround.lean#ground_love_preserves_pure_actuality](formal/Logos/LovesAsGround.lean#L573), footprint {GroundBearsGood, Initiates, Means, NecessarySubjectKind, State, Subject} | **restates C217** (`ofGround_no_transition_potency`) — love as act *adds to* pure actuality | ✅ PROVEN | {GroundBearsGood, Initiates, Means, NecessarySubjectKind, State, Subject} |
| L1 | C350 | [CosmicExistence.lean#contingent_realm_obtains](formal/Logos/CosmicExistence.lean#L266), footprint {NecessarySubjectKind, Subject, CL} | **contingency-overflow — a theorem, not a datum, and now free of any bridge**: something obtains, is modal-fragile, and is not the necessary ground. Witnessed by an atom via `an_atom_is_contingent 0` (C324), which is why the price vanished — `ContingentRealm` is `Realm` *without* `bears_meaning`, so no `Subject` and no `Means` are consumed. **This row asserts no act of production**: "created" names the region of reality that is actual, modal-fragile and not the ground; no `Creates` relation, agent or first moment is claimed or derivable. Rejecting `AxTwoSubjects` does not touch this row. Was a `Tag: SEM` axiom (`AxContingentCreationObtains`), retired 2026-09-27 — the lemma it declared unavailable was already a theorem | ✅ PROVEN | {NecessarySubjectKind, Subject, CL} |
| D | — | [CosmicExistence.lean#ContingentRealm](formal/Logos/CosmicExistence.lean#L231), footprint {} | the realm **without the meaning condition**: `witness`, `actual`, `contingent`, `not_the_ground` — i.e. `Realm` minus `bears_meaning`, which is precisely why C350 is free | ✅ PROVEN | {} |
| D | — | [CosmicExistence.lean#ContingentRealmObtains](formal/Logos/CosmicExistence.lean#L244), footprint {NecessarySubjectKind, Subject} | the `Prop` form of the same, so the ledger can name the claim as C350 while the record keeps a single witness | ✅ PROVEN | {NecessarySubjectKind, Subject} |
| L2 | C367 | [CosmicExistence.lean#cosmos_obtains](formal/Logos/CosmicExistence.lean#L412), footprint {Means, NecessarySubjectKind, Subject, Will, subjectWill, CL} | **the same realm, now meaning-bearing — given an exhibited *contingent person***: the kind premise (2026-09-28, two-kinds) exhibits what kind-blind semantics got for free, so `AxTwoSubjects` is no longer among the premises — exhibiting the kind subsumes the T12 witness. **It is still the row that identifies the realm as *the* cosmos** — C324's prohibition (an atom is not the cosmos) is untouched, because C350 shows only that the *shape* has an instance. **The price is exhibited, not forced:** 3e below reaches the same inhabitation from the act-datum | ✅ PROVEN | {Means, NecessarySubjectKind, Subject, Will, subjectWill, CL} |
| D | — | [CosmicExistence.lean#CreatedRealm](formal/Logos/CosmicExistence.lean#L201), footprint {Means, NecessarySubjectKind, Subject} | the meaning-bearing realm's structure: `Nonempty Realm`, single witness — fair definition; the inhabitation is now **proved** (C367), no longer stipulated | ✅ PROVEN | {Means, NecessarySubjectKind, Subject} |
| S | — | [CosmicExistence.lean#gamma_exhibits_a_meaning_subject](formal/Logos/CosmicExistence.lean#L427), footprint {AxTwoSubjects, Means, Subject, Will, subjectWill} | **the emptiness result on its own**: Γ exhibits a subject that means something — the user's point, made checkable, with the subject *discovered* inside Γ rather than assumed | ⚠️ AXIOMATIC | {AxTwoSubjects, Means, Subject, Will, subjectWill} |
| L2 | C351 | [CosmicExistence.lean#the_ground_loves_the_cosmos](formal/Logos/CosmicExistence.lean#L559), footprint {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, Will, subjectWill, CL} | **the conclusion, both prices visible** — "not merely a mathematical ground, but loves" | ⚠️ AXIOMATIC | {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, Will, subjectWill, CL} |
| L2 | C352 | [CosmicExistence.lean#the_ground_loves_the_cosmos_in_a_context](formal/Logos/CosmicExistence.lean#L576), footprint {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, Will, subjectWill, CL} | the same conclusion in the relational vocabulary — `GroundLoves`, **not** `Loves` | ⚠️ AXIOMATIC | {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, Will, subjectWill, CL} |
| L2b | C386 | [CosmicExistence.lean#cosmos_presence_model_of_the_act_datum](formal/Logos/CosmicExistence.lean#L342), footprint {Initiates, Means, NecessarySubjectKind, State, Subject, CL} | **THE GOD-LANE, half one — the same inhabitation with the META bridge left out**: the performative act-datum reaches a meaning-bearing subject on its own, because `Act` already contains `Means` as a conjunct, so `act_datum_implies_means` needs no bridge. A **new row**, not a re-anchoring of C367, and it does not replace it: a theorem *discovers*, it does not manufacture, so Γ supplies no subject from nothing — the datum is given, not inferred, and the kind is exhibited with it (2026-09-28, two-kinds). Re-anchoring `cosmos_obtains` would repeat the A1 bug exactly | ✅ PROVEN ◈ | {Initiates, Means, NecessarySubjectKind, State, Subject, CL} |
| L2b | C387 | [CosmicExistence.lean#the_ground_loves_the_cosmos_from_the_act_datum](formal/Logos/CosmicExistence.lean#L618), footprint {AxGroundLovesContingentRealm, GroundBearsGood, Initiates, Means, NecessarySubjectKind, State, Subject, CL} | **THE GOD-LANE's payoff — the ground's love, byte-identical statement, plurality route gone**: the `Will`/`subjectWill` that entered only through `AxTwoSubjects` are gone with it. The interpersonal metaphysics is no longer a premise here, and the remaining premises are independent of it, so the removal is *visible* rather than absorbed. The love bridge stays, and must: a directional good held by the ground is not in Γ's grounding vocabulary. Relocated price ◈ `performativeActDatum` — free in axioms, not free in performance | ⚠️ AXIOMATIC ◈ | {AxGroundLovesContingentRealm, GroundBearsGood, Initiates, Means, NecessarySubjectKind, State, Subject, CL} |
| 🧱 | C353 | [CosmicExistence.lean#perfect_universe_has_no_contingent_realm](formal/Logos/CosmicExistence.lean#L462), footprint {} | **countermodel, `{}`**: the contingency shape is refutable in a world-rigid universe — on an **unrelated free structure, not a model of Γ** | 🧱 INDEPENDENT | {} |
| L1 | C354 | [CosmicExistence.lean#cosmos_presence_model](formal/Logos/CosmicExistence.lean#L298), footprint {Means, NecessarySubjectKind, Subject, CL} | **conditional satisfiability**: the realm obtains for any contingent-kind `Means` inhabitant — kind exhibited, stated, not glossed as unconditional | ✅ PROVEN | {Means, NecessarySubjectKind, Subject, CL} |

**The dual cost, stated because the badge states only half of it.** The `the_ground_is_a_necessary_and_chosen_lover` row above renders **⚠️ AXIOMATIC (AxGroundLovesContingentRealm)**: `footprint_parts` files `GroundBearsGood` under the vocabulary baseline, so the primitive never appears in the parenthetical. A reader trusting the badge alone concludes the directed-good vocabulary is free. It is not: without PRICE 1 there is no `GroundLoves` relation to inhabit, and without PRICE 2 no inhabitant follows. The registry is unmoved at 25 axioms (14/7/4) **not because the batch is free but because all three prices were already declared and invisible** — which is why this block, like the ◈ registry for ASIETIC-CHOICE, is load-bearing rather than decorative.

**Also not claimed:** `GroundLoves` is **not** `Loves` (different index, different kind — merging them would silently reinterpret T14); the `GroundLoves → Loves` transfer is unstatable (C348), so bridge #9 / C228 stands exactly as it was; C330 is ontology-forced, not evidence of love; C353 is a countermodel on an unrelated free structure, not a model of Γ; and C354 is satisfiability conditional on a `Means` inhabitant.

### TWO-KINDS chain, step by step (every step priced)

> **Read this table before reading any plurality/personal-ground row above.** The
> argument's remaining metaphysical gap was *who fills the necessary pole*. This batch
> introduces a free predicate for a subject's **kind**, proves that the two kinds are
> exactly the two modal profiles, and then — on **one** declared `META` bridge — derives
> that the necessary kind is inhabited by a **Person**. The whole price is the `◆` row.

`V` = the `VOCAB` axiom (a free predicate, asserting no existence) · `D` = its `def`
complement · `L1` = a theorem on vocabulary alone, **0 substantive axioms** · `◆` = the
declared `META` bridge · `L2` = a theorem resting on that bridge · `Σ` = the headline
partition.

| # | Ledger | Declaration | Step | Status | Kernel footprint |
|---|---|---|---|---|---|
| V | C403 | [Agency.lean#NecessarySubjectKind](formal/Logos/Agency.lean#L62), footprint {NecessarySubjectKind, Subject} | **THE VOCABULARY OF THE TWO KINDS** (`Tag: VOCAB`): a free predicate for the *kind* of a subject. It asserts no existence — inhabitation is C404, the bridge, and is deliberately not part of this line | ◆ AXIOM | {NecessarySubjectKind, Subject} |
| D | — | [Agency.lean#ContingentSubjectKind](formal/Logos/Agency.lean#L67), footprint {NecessarySubjectKind, Subject} | its `def` complement (`¬ NecessarySubjectKind`); the two kinds partition the sort by C411 | ✅ PROVEN | {NecessarySubjectKind, Subject} |
| L1 | C405 | [Plurality.lean#necessaryKindSubject_is_necessary](formal/Logos/Plurality.lean#L44), footprint {NecessarySubjectKind, Subject} | a subject of the necessary kind is a necessary subject — the kind-relative form of the persistence theorem, from the left disjunct of `SubjectExistsAt` | ✅ PROVEN | {NecessarySubjectKind, Subject} |
| L1 | C406 | [Plurality.lean#contingentKindSubject_not_necessary](formal/Logos/Plurality.lean#L54), footprint {NecessarySubjectKind, Subject} | a contingent-kind subject is **not** necessary — it fails in the all-`TV.f` world. This is where every earlier contingency finding now lives, and it discharges C329 (`no_subject_is_a_necessary_entity`) with **no love axiom** | ✅ PROVEN | {NecessarySubjectKind, Subject} |
| Σ | C410 | [Plurality.lean#kinds_are_the_modal_partition](formal/Logos/Plurality.lean#L79), footprint {NecessarySubjectKind, Subject} | **THE HEADLINE — the two kinds are exactly the two modal profiles**: a subject is necessary-kind **iff** its correlate exists in every world. Vocabulary-only, **0 substantive axioms** | ✅ PROVEN | {NecessarySubjectKind, Subject} |
| L1 | C411 | [Plurality.lean#contingentKind_iff_not_necessary](formal/Logos/Plurality.lean#L98), footprint {NecessarySubjectKind, Subject} | contingent-kind is the complement of necessary-kind, hence — with C410 — the complementarity of world-rigidity itself | ✅ PROVEN | {NecessarySubjectKind, Subject} |
| L1 | C412 | [Plurality.lean#necessaryKind_existsAt_every_world](formal/Logos/Plurality.lean#L110), footprint {NecessarySubjectKind, Subject} | the necessary-kind profile: **every** world. Left disjunct, and nothing more | ✅ PROVEN | {NecessarySubjectKind, Subject} |
| L1 | C413 | [Plurality.lean#contingentKind_existsAt_actualWorld_only](formal/Logos/Plurality.lean#L123), footprint {NecessarySubjectKind, Subject} | the contingent-kind profile: **the actual world and no other**. With C412, the **asymmetry of inhabitation** between the kinds | ✅ PROVEN | {NecessarySubjectKind, Subject} |
| L1 | C414 | [Plurality.lean#falsityWorld_holds_no_contingent_subject](formal/Logos/Plurality.lean#L146), footprint {NecessarySubjectKind, Subject} | the world of falsity hosts no contingent-kind subject. **What this does not say**: it does not say the falsity world is empty, nor that the necessary kind is absent from it | ✅ PROVEN ◈ | {NecessarySubjectKind, Subject} |
| L1 | C415 | [Plurality.lean#contingentSubject_might_not_have_existed](formal/Logos/Plurality.lean#L160), footprint {NecessarySubjectKind, Subject} | a contingent-kind subject **might not have existed** — C406 in world-relative form, and the one half of contingency the argument does *not* need to assume | ✅ PROVEN ◈ | {NecessarySubjectKind, Subject} |
| ◆ | C404 | [Plurality.lean#necessaryPersonalSubjectExists](formal/Logos/Plurality.lean#L185), footprint {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} | **THE BRIDGE, AND THE ONLY SUBSTANTIVE PRICE IN THIS BATCH** (`Tag: META`): the necessary kind is inhabited by a **Person** — the ground read in its Personal Type, as a Subject. **Everything below is this row, and nothing else** | ◆ AXIOM | {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} |
| L2 | C407 | [Plurality.lean#necessarySubject_exists](formal/Logos/Plurality.lean#L189), footprint {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} | a necessary subject exists, by the bridge | ⚠️ AXIOMATIC | {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} |
| L2 | C408 | [Plurality.lean#necessaryPersonalSubject_derived](formal/Logos/Plurality.lean#L197), footprint {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} | a **necessary Person** exists: the meaning-bearing subject is necessary-kind, the contingent one is the other kind | ⚠️ AXIOMATIC | {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} |
| L2 | C409 | [NecessaryPersonalGround.lean#necessary_person_derived_from_bridge](formal/Logos/NecessaryPersonalGround.lean#L145), footprint {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} | **CLAIM D IS NOW DERIVED, NOT ANNOTATED** — the necessary-person existential is no longer empty. The price is exactly the bridge and nothing more | ⚠️ AXIOMATIC | {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} |
| L1 | C151 | [PersonalGroundOfReality.lean#the_person_supports_the_reality_of_right](formal/Logos/PersonalGroundOfReality.lean#L153), footprint {Initiates, Means, State, Subject, Will, subjectWill, will_individuation, CL} | **THE FLAGSHIP, UNCONDITIONAL — 0 substantive axioms**: the person supports the reality of right, with the interpersonal metaphysics already discharged upstream. This is the load-bearing theorem the whole personal-ground route rests on | ✅ PROVEN | {Initiates, Means, State, Subject, Will, subjectWill, will_individuation, CL} |
| L1 | C152 | [PersonalGroundOfReality.lean#personal_ground_of_right_exists](formal/Logos/PersonalGroundOfReality.lean#L171), footprint {Initiates, Means, State, Subject, Will, subjectWill, will_individuation} | a **personal ground of right** exists — `{}`-class, vocabulary alone | ✅ PROVEN | {Initiates, Means, State, Subject, Will, subjectWill, will_individuation} |

**Five limits that the badge alone does not convey, and which are the reason this
block exists:**

1. **Eleven of the sixteen rows are vocabulary-only, and four carry the bridge.**
   The kind predicate `V` is `Tag: VOCAB` and asserts nothing about existence. Every
   `L1` row is vocabulary-only — C410 (the two kinds *are* the two modal profiles) is
   `{NecessarySubjectKind, Subject}`-class, and C152 is
   `{Initiates, Means, State, Subject, Will, subjectWill, will_individuation}`-class. Only
   C151 additionally carries Lean's own `choice`/`propext`/`sound`, which are **core
   kernel**, not Γ-declared axioms — the table prints it so the distinction is visible.
   The four rows carrying `necessaryPersonalSubjectExists` are the `◆` row and its three
   `L2` corollaries.
2. **The `◆` row is the entire price.** `necessaryPersonalSubjectExists` (`Tag: META`)
   is the only substantive axiom the batch introduces, and C407/C408/C409 inherit
   exactly it and nothing else. It is a **metaphysical bridge** (`META`), not a
   vocabulary commitment, and it is stated as an existential inhabitance of the kind —
   not as a derivation of personhood from the ground-constructor.
3. **C406 discharges C329 without a love axiom.** `no_subject_is_a_necessary_entity`
   used to need the exclusion hypothesis; it is now a kind-relative theorem. The love
   bridge is not doing metaphysical work it was never stated to do.
4. **The necessary kind and the ground-constructor are *not* the same row.** The
   `Entity.ofGround` constructor is disjoint from `EntityOf s` by `cases`
   (`ofGround_ne_ofSubject`, `FoundationalUnicity.lean:131`) — that is constructor
   disjointness on a three-constructor inductive, **not** a verdict that the ground is
   impersonal. The necessary *kind* is inhabited by a Person (C404); the ground
   *constructor* is not a `Subject`. Conflating the two is the error `LovesAsGround.lean`
   retracts in its own docstring.
5. **What this batch does NOT close.** C228 — identifying the normative ground with a
   *Person* — remains `BLOCKED`, and C212 proves ground-unicity does not force a unitary
   monad. Monotheism *at the level of the Person* is open; the ground's *sole universal
   modal grounding* (C319/C320) is unaffected by this batch and rests on F15 alone.

_Synthesis — the strongest current profile._ The theory has established, of a
**personal, rational, free, authoritative-over-its-acts, independently individuated**
**normative ground / person-type**, that its objective Right/Wrong order is the object
of a necessary normative/truth order, and (entity-level) that a **necessary Divine Being
/ Ground** exists — world-rigid, **everlasting**, **atemporal**, with **Canonical Aseity**,
**Divine Simplicity**, **Divine Immutability**, **Foundational Omnipresence** (sustaining all
beings across modal reality), **Foundational Unicity**, **Divine Pure Actuality** (*Actus Purus*),
and **Foundational Omniscience** (a truth-exhaustive scope in every world, whose infallible half is
machine-checked as *refuted* for the ground), and **Foundational Omnipotence** (a gapless operative
scope: no state of affairs that does not involve a contradiction is closed to the ground, whose scope
domain is machine-checked non-empty and contradiction-free), and **Divine love** (the ground as lover of contingent reality — ⚠️ AXIOMATIC under the VOCAB primitive `GroundBearsGood` and the META bridge `AxGroundLovesContingentRealm`, with the cosmos's existence a **free theorem** (C350, `{propext, Subject}`, no bridge) and only its content-bearinghood priced on `AxTwoSubjects` (C367); see the LOVE chain block).
Crucially, the theory **strictly separates** these machine-verified
foundational/functional attributes from their unproven physical, psychological, and scholastic counterparts:
**physical/spatial omnipresence**, **psychological personality**, **scholastic simplicity**,
**infallible or counterfactual omniscience**, **causal / creative omnipotence** (the presence-plus-
obtaining reading above is priced ◈ `operatesAt_presencePlusObtaining`, and a production relation plus
its derivation remain BLOCKED), and
**psychological impassibility** remain separate targets (❌ NOT ESTABLISHED or 🔴 INDEPENDENT).
The remaining divine attributes — **unity / monotheism**,
**perfect moral goodness** (the moral pole itself now obtains under the single declared META bridge, C178; its attribution to the Divine Being stays a 🧱 frontier), the **Trinity**, the **Incarnation**, and contingent
**creation as entailment** — remain **separate proof targets**
(`⏸` / `❌`) or explicit **countermodel frontiers** (`🧱`) until the live kernel proves them. Contingent creation *as existence* is no longer among them: it is a **free theorem** (C350 `contingent_realm_obtains`, `{propext, Subject}`), witnessed by an atom, with no bridge and no substantive axiom. Only the realm's *content* is priced, on an exhibited contingent person (C367 `cosmos_obtains`) — the kind premise the two-kinds doctrine exhibits, not a semantic one. And contingent creation *as production* remains unclaimed: no `Creates` relation, no agent, no first moment. So the cost was relocated and then, for existence itself, dissolved — but the act was never ours to claim.

---

## Why Common Skeptical Attacks Fail (The Six Pillars of Formal Defense)

> **Adversarial Guide for Critics and Agents:** External agents evaluating or attacking
> Γ often mistake its conclusions for ungrounded metaphysical assumptions. Every common
> objection has been formalized and refuted in the Lean 4 kernel — typically reducing to a
> direct constructive contradiction (⊥) with zero substantive axioms.
>
> **Three axes — which models are wrong, given that the world exists.** A countermodel makes three claims: the *attack* (a derivability claim, which stands unless Γ derives the inference), the *model* (a description of a world), and the *world-datum* ◈ `contingentWorldDatum` (what the model's own world-structure says about the world the proof is written in). Each model below carries its verdict **as the actual world** with the exact price that would exclude it — WRONG outright (the no-meaning world, on the act-datum; the falsity world read as the actual world, on the world-datum, for free), WRONG ONLY IF an axiom is insisted (plurality, love, choice bridges), NOT ESTABLISHED, or UNANSWERED — plus a third verdict, **given the contingent world exists**, derived in Lean from each model's `WorldStance` and cross-checked against the structure it declares. See the Technical Appendix (kernel-audit.md), Appendix C.1, where all three verdicts are rendered beside the attack each leaves standing.

| Skeptical Attack | What the Skeptic Misses | Formal Rebuttal in Kernel | Kernel Footprint |
|---|---|---|---|
| **1. Normative Nihilism**<br>"There is no objective right and wrong; normativity is arbitrary." | Any rational denial must claim that its denial is *correct* (`ClaimsCorrect s NoRight`). Claiming the denial as correct while it is true produces a strict constructive contradiction. | [`claims_correct_no_right_self_refuting`](formal/Logos/DirectNormativeRetorsion.lean#L60)<br>`⊢ ClaimsCorrect s NoRight ∧ NoRight → ⊥` | `{Initiates, Means, State, Subject, CL}`<br>**(0 substantive axioms)** |
| **2. Eliminativism of Choice**<br>"Normative address does not imply genuine choice." | Prescriptive normativity commands one alternative and forbids an incompatible one. Co-grasping incompatible alternatives *is* the constitutive definition of choice; denying choice yields a direct contradiction. | [`d7_co_grasp_is_definitionally_choice`](formal/Logos/UndeniableNormativeDerivation.lean#L261)<br>`⊢ Means s p ∧ Means s q ∧ Incompatible p q ∧ ¬ Chooses s p q → ⊥` | `{Means, Subject}`<br>**(0 substantive axioms)** |
| **3. Determinism / Incompatibilism**<br>"Choice is not Free Will; freedom requires physical indeterminism." | Having the capacity to choose between incompatible normative alternatives *is* Free Will (`FreeWill s := ∃ p q, Chooses s p q`). Denying free will when one chooses yields a formal contradiction. Physical indeterminism is an orthogonal concept isolated to countermodels. | [`d8_choice_is_definitionally_free_will`](formal/Logos/UndeniableNormativeDerivation.lean#L275)<br>`⊢ Chooses s p q ∧ ¬ FreeWill s → ⊥`<br>[`indubitable_normative_free_will`](formal/Logos/IndubitableNormativeFreeWill.lean#L115) | `{Means, Subject}`<br>**(0 substantive axioms)** |
| **4. Theological Smuggling**<br>"A free subject is not a Person; 'Person' is an anthropomorphic trick." | Personhood in Γ IS the classical Boethian-Thomistic core (`Person := ThomisticPersonCore := IndividualSubstance ∧ RationalNature ∧ DominionOverActs`). The reduction to `FreeSubject` is a priced theorem (`freeWill_implies_person`), machine-checked with 0 substantive axioms, whose exact boundary is witnessed by `SharedWillModel` (`{}`). | [`freeWill_implies_person`](formal/Logos/Person.lean#L135)<br>`⊢ FreeWill s → Person s` | `{Means, Subject, Will, subjectWill, will_individuation}`<br>**(0 substantive axioms)** |
| **5. Euthyphro / Voluntarism**<br>"This makes the person the arbitrary creator of morality." | Identifying Ought with volition (`Wills s p = Ought s p`) destroys normative violation. The ground required by the normative order is *personal in kind*, not an arbitrary dictator inventing rules. | [`will_identity_collapses_normativity`](formal/Logos/PersonalNormativeGround.lean#L261)<br>`⊢ Wills s p = Ought s p → NormativeViolation s p → ⊥` | `{Subject, Wills, Ought}`<br>**(0 substantive axioms)** |
| **6. Physicalist / Atomic Ground**<br>"The ultimate ground could be a physical particle, matter, or an atom." | An entity with false meaning capacity cannot ground an entity with true meaning capacity. Atomic factual entities are unconditionally excluded from grounding `Entity.ofGround`, and the ground possesses Canonical Aseity. | [`atom_cannot_ground_the_ground`](formal/Logos/CanonicalAseity.lean#L96)<br>[`conditional_canonical_aseity`](formal/Logos/CanonicalAseity.lean#L133)<br>`⊢ CanonicalAseity Entity.ofGround` | `{Means, Subject}`<br>**(0 substantive axioms)** |
| **7. Origin of Normativity (The Proof-Self Retorsion)**<br>"Where does the initial normative claim come from? Why grant that any normative judgment exists?" | Bare syntax checking alone does not force normativity (`M_inanimate_checker`, `{}`). But any agent *presenting* a derivation as sound (`PresentsAsSound`) co-means correctness and error, deriving `FreeWill` and `Person` with 0 substantive axioms. Furthermore, an adversarial critic who attacks Γ by presenting an objection argumentatively as sound *themselves* instantiates the normative stance (`critic_presenting_objection_is_person`). | [`presents_as_sound_derives_personhood`](formal/Logos/ProofPresentationRetorsion.lean#L140)<br>[`critic_presenting_objection_is_person`](formal/Logos/ProofPresentationRetorsion.lean#L180)<br>[`syntactic_validity_without_subject_or_normativity`](formal/Logos/ProofPresentationRetorsion.lean#L100) | `{Initiates, Means, State, Subject, CL}`<br>**(0 substantive axioms)** |

## Further Investigations

### Retorsions

<details>
<summary>Retorsion catalogue — 97 machine-checked retorsion theorems (click to expand)</summary>

* **Performative_Boundary_Theorem:** `performative_boundary_theorem` (`formal/Logos/A14SemanticAudit.lean`) — PERFORMATIVE BOUNDARY THEOREM: Performative retorsion forces an intentional subject (Considers, Assumes, Derives, Affirms, Rejects) and asymmetric cognitive resolution (SettlementChoice), but strictly stops before executive aiming (AimsAt), action execution
* **Noact_Conditional_Selfrefutes:** `noAct_conditional_selfRefutes` (`formal/Logos/Agency.lean`) — Asserting NoAct refutes itself under a weak assertion ONLY given the bridge from weak act to strong Act.
* **Nocogito_Selfrefutes:** `noCogito_selfRefutes` (`formal/Logos/Agency.lean`) — Step 4 (C58 strong shortcut): Retorsion — asserting that no act occurs refutes itself.
* **Nosubjectsort_Selfrefutes:** `noSubjectSort_selfRefutes` (`formal/Logos/Agency.lean`) — Denying the domain of discourse refutes itself whenever a speaker asserts it.
* **Nosubject_Performative_Selfrefutes:** `noSubject_performative_selfRefutes` (`formal/Logos/Agency.lean`) — C57: Retorsion — asserting that no subject exists refutes itself.
* **Nosubject_Selfrefutes:** `noSubject_selfRefutes` (`formal/Logos/Agency.lean`) — C57 canonical theorem name in Agency.
* **Noweakact_Selfrefutes:** `noWeakAct_selfRefutes` (`formal/Logos/Agency.lean`) — Step 4 (weak retorsion): Asserting that no performed event occurs refutes itself directly.
* **Retorsion_Implies_Rejectedhorncomeant:** `retorsion_implies_rejectedHornCoMeant` (`formal/Logos/AsieticChoice.lean`) — ★★★ The recorded blocker has a **second, performative** discharge: from the retorsion event the consequent `rejectedHornCoMeant` follows. This differs from `derives_rejectedHornCoMeant` in that the content need not be arbitrary — the denial supplies its own
* **Retorsion_Yields_Genuine_Normativity_On_Its_Own_Content:** `retorsion_yields_genuine_normativity_on_its_own_content` (`formal/Logos/AsieticChoice.lean`) — ★★ The retorsion event forces genuine normativity **on its own content**: a subject who claims "there is no genuine normativity" *as correct* thereby means both `NoGN` and `¬ NoGN`. This is the pinned-content form that answers the meta-level-horn residue
* **Level_3_Retorsion_Impotent_Without_Semantic_Premise:** `level_3_retorsion_impotent_without_semantic_premise` (`formal/Logos/BipolarityRetorsion.lean`) — Level 3: Retorsive Impotence of Bare Denial.
* **Nochoicefield_Selfrefutes:** `noChoiceField_selfRefutes` (`formal/Logos/Choice.lean`) — C53 (field form): performative retorsion — asserting that no choice field exists refutes itself. Footprint: `{Initiates, Means, State, Subject}` (VOCAB only; zero AxTwoSubjects).
* **Nostrongtruth_Assertable_Refutes:** `noStrongTruth_assertable_refutes` (`formal/Logos/Choice.lean`) — No one can assert "there is no strong truth": the act of denying the world-level datum is destroyed by the datum itself (assertive retorsion of C93, completing the retorsion family at the assertion level).
* **Nosubject_Selfrefutes:** `noSubject_selfRefutes` (`formal/Logos/Choice.lean`) — C57: Retorsion — asserting that no actual subject exists refutes itself.
* **Selfassertedparadox_Not_Assertable:** `selfAssertedParadox_not_assertable` (`formal/Logos/Choice.lean`) — Candidate D performative retorsion under factive assertion: one cannot truthfully assert Candidate D.
* **Selfdenialofexecutivechoice_Selfrefutes:** `selfDenialOfExecutiveChoice_selfRefutes` (`formal/Logos/Choice.lean`) — The Performative Retorsion Theorem for Executive Choice: Denying executive choice in an assertion is self-refuting.
* **Diagonal_Negative_Choice_Coherent:** `diagonal_negative_choice_coherent` (`formal/Logos/DeepContrastiveFrontier.lean`) — Candidate Δ2: Negative self-assertion of determinism is strictly true and non-self-refuting.
* **Retorsion_Denial_Does_Not_Commit_To_Content:** `retorsion_denial_does_not_commit_to_content` (`formal/Logos/DefinitiveAgencyFrontier.lean`) — Retorsion Failure Theorem: Asserting "I do not commit to p" reflexively instantiates an assertion of the negation, but does NOT instantiate commitment to p itself.
* **Performative_Self_Refutation_Compatible_With_Determinism:** `performative_self_refutation_compatible_with_determinism` (`formal/Logos/DeterministicReductioFrontier.lean`) — Core Independence Result: Performative self-refutation does NOT imply libertarian freedom.
* **Self_Denial_Of_Reasoning_Self_Refutes:** `self_denial_of_reasoning_self_refutes` (`formal/Logos/DeterministicReductioFrontier.lean`) — Performative Self-Refutation of Denying One's Own Present Act: If an agent asserts "I am not acting", the factive assertion itself refutes the content.
* **Claims_Correct_No_Right_Self_Refuting:** `claims_correct_no_right_self_refuting` (`formal/Logos/DirectNormativeRetorsion.lean`) — The Fundamental Diagonal Retorsion Theorem: Claiming NoRight as correct while NoRight is true produces a strict, constructive contradiction.
* **Model_A_Mere_Utterance_Avoids_Claims_Correct:** `model_a_mere_utterance_avoids_claims_correct` (`formal/Logos/DirectNormativeRetorsion.lean`) — Model A Avoidance Lemma: Mere utterance does not satisfy ClaimsCorrect.
* **Model_B_Mere_Meaning_Avoids_Claims_Correct:** `model_b_mere_meaning_avoids_claims_correct` (`formal/Logos/DirectNormativeRetorsion.lean`) — Model B Avoidance Lemma: Meaning NoRight without acting on it does not instantiate ClaimsCorrect.
* **Retorsion_Nochoice_Self_Refutes:** `retorsion_NoChoice_self_refutes` (`formal/Logos/ExecutiveDeliberativeFrontier.lean`) — Group 1 Theorem: Asserting NoChoice is performatively self-refuting.
* **Retorsion_Nodeliberation_Consistent:** `retorsion_NoDeliberation_consistent` (`formal/Logos/ExecutiveDeliberativeFrontier.lean`) — Group 2 Theorem: Asserting NoDeliberation is completely consistent and non-self-refuting.
* **Retorsion_Nofreewill_Consistent:** `retorsion_NoFreeWill_consistent` (`formal/Logos/ExecutiveDeliberativeFrontier.lean`) — Group 2 Theorem: Asserting NoFreeWill is completely consistent and non-self-refuting.
* **Schema_S4_Satisfiable_And_Non_Self_Refuting:** `schema_S4_satisfiable_and_non_self_refuting` (`formal/Logos/ExecutiveDeliberativeFrontier.lean`) — Schema S4 Theorem: Denying deliberative choice is NOT performatively self-refuting! A deterministic agent can assert with complete truth that it does not deliberate.
* **Trackb_Selfdenialofexecutivechoice_Selfrefutes:** `trackB_selfDenialOfExecutiveChoice_selfRefutes` (`formal/Logos/ExecutiveDeliberativeFrontier.lean`) — Re-verifying the retorsion theorem for executive choice in this module.
* **Contextual_Retorsion_Datum:** `contextual_retorsion_datum` (`formal/Logos/HardenedInvariance.lean`) — Contextual Retorsion: Denying that any deduction is developed in any context refutes itself performatively when that denial is asserted as a step within an inquiry context.
* **Retorsion_Does_Not_Imply_Doubt:** `retorsion_does_not_imply_doubt` (`formal/Logos/HostileSemantics.lean`) — Transcendental retorsion holds fully in TwoPersons, yet Cartesian doubt is empty.
* **A6_A7_Synergistic_Forcing:** `A6_A7_synergistic_forcing` (`formal/Logos/JointForcing.lean`) — Synergy Forcing Theorem: A6 (universal_thesis_claims_objectivity) + A7 (transcendental_reflection_intentional) jointly force NonTrivialOntology under the standard retorsive bridges.
* **Retorsion_Not_Implies_Choice:** `retorsion_not_implies_choice` (`formal/Logos/JointForcing.lean`) — Cross-Frontier Barrier: {A6, A7} (Retorsion) does NOT force AxIntentionalChoice (A1) or FreeWill.
* **Affirms_Nomeaning_Yields_Meaning:** `affirms_noMeaning_yields_meaning` (`formal/Logos/MeaningRetorsion.lean`) — **The retorsion, positively.** To affirm that there is no meaning is itself a meaning: affirming the thesis produces an instance of exactly what the thesis denies. The conclusion is the `Meaning_I` form with the content *named* — `NoMeaning` itself is the
* **Nomeaning_Iff_Nointentionalsubject:** `noMeaning_iff_noIntentionalSubject` (`formal/Logos/MeaningRetorsion.lean`) — **The thesis and the audited negation of the retorsive conclusion are the same sentence, re-indexed.** `NoI_canonical := ¬ P_canonical` and `P_canonical := ∃ s, IntentionalSubject s` with `IntentionalSubject s := ∃ p, Means s p`; `NoMeaning` is `¬ ∃ p, ∃ s
* **Nomeaning_Is_Unassertable:** `noMeaning_is_unassertable` (`formal/Logos/MeaningRetorsion.lean`) — **4/4 — THE RETORSION, unconditional.** Nobody can hold the thesis as correct. No hypothesis, no subject supplied, no bridge, no axiom beyond the declared meaning vocabulary: `Asserts s p` is `Act s p ∧ p`, so an assertion of the thesis is at once an act
* **Signature_Weak_Retorsion:** `signature_weak_retorsion` (`formal/Logos/MeaningRetorsion.lean`) — **The weak retorsion, signature-general.** Affirming that no performed event occurs is self-refuting: the affirmation is itself a performed event. This is `Agency.noWeakAct_selfRefutes` (`Agency.lean:263`) lifted from Γ's canonical vocabulary to an arbitrary
* **Amoral_Disconnection_Is_Judgeable_As_Correct:** `amoral_disconnection_is_judgeable_as_correct` (`formal/Logos/MoralFrontierAudit.lean`) — The amoralist thesis is judgeable-as-correct in the model: satisfiable, not self-refuting.
* **Canonical_Act_Noi_Proves_P:** `canonical_act_noi_proves_P` (`formal/Logos/NegativeRetorsionAudit.lean`) — Positive Retorsion: Performing an act on NoI proves that an intentional subject exists! Classification: DEFINITIONAL. Footprint: `{Initiates, Means, State, Subject}`.
* **Canonical_Asserts_Noi_Selfrefutes:** `canonical_asserts_noi_selfRefutes` (`formal/Logos/NegativeRetorsionAudit.lean`) — The Fundamental Assertive Retorsion: Actually asserting NoI is unconditionally self-refuting (proves False).
* **Canonical_Exists_Asserts_Noi_Selfrefutes:** `canonical_exists_asserts_noi_selfRefutes` (`formal/Logos/NegativeRetorsionAudit.lean`) — Existential Assertive Retorsion: Existence of any assertion of NoI derives False.
* **Canonical_Means_Noi_Proves_P:** `canonical_means_noi_proves_P` (`formal/Logos/NegativeRetorsionAudit.lean`) — Positive retorsion: Any subject meaning NoI proves that an intentional subject exists! Classification: DEFINITIONAL. Footprint: `{Means, Subject}`.
* **Canonical_Noi_Implies_Not_Means:** `canonical_noi_implies_not_means` (`formal/Logos/NegativeRetorsionAudit.lean`) — Canonical Fundamental Theorem of Negative Retorsion: Under NoI, no subject can mean NoI.
* **Level2_Signature_Asserts_Noi_Selfrefutes:** `level2_signature_asserts_noi_selfRefutes` (`formal/Logos/NegativeRetorsionAudit.lean`) — Signature-generalized Theorem: Asserting NoI refutes itself in any signature.
* **Negative_Retorsion_Master_Synthesis:** `negative_retorsion_master_synthesis` (`formal/Logos/NegativeRetorsionAudit.lean`) — Master Synthesis Theorem of the Negative Retorsion Campaign: Collects the definitive machine-checked mathematical conclusions: 1. Bare NoI is satisfiable in isolation (M0, M1).
* **Performed_Denial_Gradient:** `performed_denial_gradient` (`formal/Logos/NegativeRetorsionAudit.lean`) — Master Ladder Theorem of Performed Denial: Demonstrates the exact gradient where retorsion takes effect.
* **Regime_M5_Is_Provably_Incoherent:** `regime_M5_is_provably_incoherent` (`formal/Logos/NegativeRetorsionAudit.lean`) — REGIME M5 AUDIT: "NoI is true and someone attempts to mean it." As mandated by the adversarial review advisory, this regime is PROVABLY EMPTY / INCOHERENT: The conjunction `NoI ∧ (∃ s, Means s NoI)` is logically unsatisfiable due to Level 1 retorsion.
* **Context_Normative_Truth_Exists:** `context_normative_truth_exists` (`formal/Logos/NormativeTruth.lean`) — Theorem: Context-packaged form of the retorsion theorem.
* **Necessary_Normative_Truth_Exists:** `necessary_normative_truth_exists` (`formal/Logos/NormativeTruth.lean`) — Modal Retorsion Theorem: In any modal semantics where the retorsive self-application holds across worlds, normative truth necessarily exists in every world.
* **No_Normative_Truth_Is_Self_Refuting:** `no_normative_truth_is_self_refuting` (`formal/Logos/NormativeTruth.lean`) — Theorem: Under self-application, the universal denial of normative truth is strictly self-refuting.
* **Normative_Truth_Exists:** `normative_truth_exists` (`formal/Logos/NormativeTruth.lean`) — Theorem: Direct derivation that normative truth necessarily exists from the retorsive self-application.
* **Judgment_Of_No_Act_Proves_Act:** `judgment_of_no_act_proves_act` (`formal/Logos/Order.lean`) — The Retorsive Cogito: even the skeptic's denial that any act occurs strictly witnesses that an act occurs. The act cannot be denied without providing the witness that refutes the denial.
* **Asserting_No_Personal_Source_Instantiates_Only_Judging_Subject:** `asserting_no_personal_source_instantiates_only_judging_subject` (`formal/Logos/OughtRetorsion.lean`) — Theorem: Retorsion Boundary on Personal Source.
* **Deny_Right_Self_Contradicts:** `deny_right_self_contradicts` (`formal/Logos/PersonalGroundOfReality.lean`) — Denying Right is performatively self-contradictory: no agent can present NoRight as correct while NoRight is true. Footprint: `{Initiates, Means, State, Subject}` (zero substantive axioms). Re-export of the retorsion boundary.
* **Discovery_Independent_Of_Grounding:** `discovery_independent_of_grounding` (`formal/Logos/PersonalNormativeGround.lean`) — Non-Circularity Architectural Theorem: The retorsive discovery proof of Free Will (`indubitable_normative_free_will`) does NOT require or depend upon any grounding bridge.
* **Proof_Criticism_Nihilism_Self_Refuting:** `proof_criticism_nihilism_self_refuting` (`formal/Logos/ProofPresentationRetorsion.lean`) — Dialectical Retorsion: Any skeptic attempting to deny objective correctness in formal derivations by claiming normative nihilism (`NoRight`) refutes itself constructively.
* **Retorsion_Proof_Derives_F1B:** `retorsion_proof_derives_F1b` (`formal/Logos/ProofSpecificContrast.lean`) — The Existential Free Will Theorem (F1b) derived from the performative retorsion proof!
* **Claims_Correct_Disconnection_Never_Factive:** `claims_correct_disconnection_never_factive` (`formal/Logos/RealityHookAudit.lean`) — No claim of correctness over the disconnection thesis is ever veridical.
* **Bigo_Bigs_Intentional_Synthesis:** `bigO_bigS_intentional_synthesis` (`formal/Logos/Retorsion.lean`) — Synthesis of Big-O / Big-S Retorsion with Intentional Subject: Both absolutes are self-defeating, establishing the irreducible co-existence of the Objective realm, the Subjective realm, and an active IntentionalSubject.
* **Deterministic_Transcendental_Subject_Refutes_Freewill:** `deterministic_transcendental_subject_refutes_freewill` (`formal/Logos/Retorsion.lean`) — Hostile Separation Theorem 1: Weakened retorsion CANNOT derive FreeWill.
* **Deterministic_Transcendental_Subject_Refutes_Person:** `deterministic_transcendental_subject_refutes_person` (`formal/Logos/Retorsion.lean`) — Hostile Separation Theorem 2: Weakened retorsion CANNOT derive Personhood.
* **Exists_Intentional_Subject_Of_Retorsion:** `exists_intentional_subject_of_retorsion` (`formal/Logos/Retorsion.lean`) — Primary Retorsive Theorem: Existence of an Intentional Subject via Retorsion.
* **Exists_Objective_Of_Retorsion:** `exists_objective_of_retorsion` (`formal/Logos/Retorsion.lean`) — Positive Existential Consequence 1 (Something Objective Exists): The objective status of the universal thesis witnesses an intentional-subject-independent item.
* **Exists_Subjective_Of_Retorsion:** `exists_subjective_of_retorsion` (`formal/Logos/Retorsion.lean`) — Positive Existential Consequence 2 (Something Subjective Exists): The performative representation of universal objectivity witnesses a Subjective item.
* **Not_Everything_Objective:** `not_everything_objective` (`formal/Logos/Retorsion.lean`) — Big-O Retorsion Theorem: It cannot be the case that everything is Objective.
* **Not_Everything_Subjective:** `not_everything_subjective` (`formal/Logos/Retorsion.lean`) — Big-S Retorsion Theorem: It cannot be that everything is Subjective (IntentionalSubject-dependent).
* **Pig_Retorsion_Exposes_Premise_Smuggling:** `pig_retorsion_exposes_premise_smuggling` (`formal/Logos/Retorsion.lean`) — Separation Theorem: Bare transcendental reflection does NOT force arbitrary predicates (such as Winged Pig).
* **Retorsion_Boundary_Principle:** `retorsion_boundary_principle` (`formal/Logos/Retorsion.lean`) — Retorsion Boundary Theorem: A retorsion argument succeeds in establishing P from an assertion of denial Q if and only if Q performatively instantiates P.
* **Retorsion_Establishes_Affirmation:** `retorsion_establishes_affirmation` (`formal/Logos/Retorsion.lean`) — The fundamental theorem of performative retorsion: If asserting a content `Q` forces `P`, then no agent can consistently assert `Q` if `Q` entails `¬P`.
* **Retorsion_No_Act:** `retorsion_no_act` (`formal/Logos/Retorsion.lean`) — Retorsion 1 (DEFINITIONAL): Denying action is performatively self-refuting.
* **Retorsion_No_Choicefield:** `retorsion_no_choiceField` (`formal/Logos/Retorsion.lean`) — Retorsion 5 (DEFINITIONAL): Denying the choice field is performatively self-refuting.
* **Retorsion_No_Subject:** `retorsion_no_subject` (`formal/Logos/Retorsion.lean`) — Retorsion 4 (DEFINITIONAL): Denying the subject is performatively self-refuting.
* **Retorsion_No_Truth:** `retorsion_no_truth` (`formal/Logos/Retorsion.lean`) — Retorsion 3 (LOGICAL): Denying truth is logically and performatively self-refuting.
* **Retorsion_No_Weak_Act:** `retorsion_no_weak_act` (`formal/Logos/Retorsion.lean`) — Retorsion 2 (DEFINITIONAL): Denying weak action is performatively self-refuting.
* **Retorsion_Refutes_Denial:** `retorsion_refutes_denial` (`formal/Logos/Retorsion.lean`) — Performative self-defeat: holding `denialContent` as an actual assertion refutes the denial's content.
* **Weakened_Retorsion_Derives_Intentional_Subject:** `weakened_retorsion_derives_intentional_subject` (`formal/Logos/Retorsion.lean`) — Theorem: Weakened retorsion legitimately derives the existence of an Intentional Subject.
* **Winged_Pig_Derived_Of_Pig_Reflection:** `winged_pig_derived_of_pig_reflection` (`formal/Logos/Retorsion.lean`) — Trivial Retorsion Derivation of Winged Pig: If one adopts the question-begging premise, retorsion "proves" the existence of a Winged Pig.
* **Claiming_Denial_Presupposes_Genuine_Normativity:** `claiming_denial_presupposes_genuine_normativity` (`formal/Logos/RetorsiveNormativity.lean`) — The Fundamental Retorsive Presupposition: Claiming the denial of normativity as correct directly instantiates GenuineNormativity.
* **Claims_Correct_Is_Act:** `claims_correct_is_act` (`formal/Logos/RetorsiveNormativity.lean`) — Extraction of the intentional act from a claim of correctness.
* **Claims_Correct_Means_Content:** `claims_correct_means_content` (`formal/Logos/RetorsiveNormativity.lean`) — Extraction of the primary meant content from a claim of correctness.
* **Claims_Correct_Presupposes_Normativity:** `claims_correct_presupposes_normativity` (`formal/Logos/RetorsiveNormativity.lean`) — Performative Presupposition of Assertion: Asserting p as correct constitutively instantiates genuine normative governance between p and ¬p for subject s.
* **Denial_Of_Genuine_Normativity_Is_Self_Refuting:** `denial_of_genuine_normativity_is_self_refuting` (`formal/Logos/RetorsiveNormativity.lean`) — Theorem: Non-vacuous self-refutation of the denial of GenuineNormativity.
* **Denial_Requires_Meaning_Genuine_Normativity:** `denial_requires_meaning_genuine_normativity` (`formal/Logos/RetorsiveNormativity.lean`) — To claim the denial of genuine normativity as correct, the subject must mean the denial: the retorsion never lets the denier avoid grasping the very content denied (no mere string, no bare phonetic emission; cf. Attack A).
* **Normative_Claiming_Denial_Presupposes_Normativity:** `normative_claiming_denial_presupposes_normativity` (`formal/Logos/RetorsiveNormativity.lean`) — The Fundamental Normative Retorsive Presupposition: Claiming the denial of normativity under the normative correctness stance instantiates GenuineNormativity on the judicative poles (Correct vs Incorrect) WITHOUT AxJudicativeBipolarity and without requiring
* **Normative_Denial_Of_Normativity_Is_Self_Refuting:** `normative_denial_of_normativity_is_self_refuting` (`formal/Logos/RetorsiveNormativity.lean`) — Non-vacuous self-refutation of the denial of GenuineNormativity under the normative correctness stance.
* **Normative_Retorsion_Derives_Free_Will:** `normative_retorsion_derives_free_will` (`formal/Logos/RetorsiveNormativity.lean`) — Master Retorsion Route to Free Will without AxJudicativeBipolarity: Normative Denial of GN ⇒ GenuineNormativity ⇒ Chooses ⇒ FreeWill.
* **Normative_Retorsion_Derives_Genuine_Normativity:** `normative_retorsion_derives_genuine_normativity` (`formal/Logos/RetorsiveNormativity.lean`) — Performative Derivation Theorem: Under an actual performed denial event with normative correctness awareness, GenuineNormativity is inescapably established with ZERO substantive axioms.
* **Normative_Retorsion_Same_Structure_Type:** `normative_retorsion_same_structure_type` (`formal/Logos/RetorsiveNormativity.lean`) — Structure-identity: the axiom-free normative route terminates in the SAME GenuineNormativity type (horns = the judicative normative poles Correct vs Incorrect) as the AxJudicativeBipolarity route; the downstream chain GN → Chooses → FreeWill is therefore
* **Retorsion_Address_Uses_Only_Means:** `retorsion_address_uses_only_means` (`formal/Logos/RetorsiveNormativity.lean`) — The address component of the instantiated GenuineNormativity is built solely from the primitive Means relation: its canonical witness is exactly the pair `⟨Means s NoGN, Means s (¬ NoGN)⟩`. No Correct, Incorrect, Ought, or deontic primitive occurs in the
* **Retorsion_Conclusion_Is_The_Very_Genuine_Normativity_Structure:** `retorsion_conclusion_is_the_very_genuine_normativity_structure` (`formal/Logos/RetorsiveNormativity.lean`) — The performed denial of genuine normativity instantiates the very GenuineNormativity structure the downstream chain consumes: same definition, same Means-level address, opposition by pure logic. No stronger notion of normativity is introduced at this step
* **Retorsion_Derives_Free_Will:** `retorsion_derives_free_will` (`formal/Logos/RetorsiveNormativity.lean`) — The Complete Master Retorsion Route: Denial of GN ⇒ Assertion as Correct ⇒ GenuineNormativity ⇒ Chooses ⇒ FreeWill.
* **Retorsion_Derives_Genuine_Normativity:** `retorsion_derives_genuine_normativity` (`formal/Logos/RetorsiveNormativity.lean`) — Performative Derivation Theorem: Under an actual performed denial event, GenuineNormativity is inescapably established.
* **Retorsion_Opposition_Is_Pure_Logic:** `retorsion_opposition_is_pure_logic` (`formal/Logos/RetorsiveNormativity.lean`) — The opposition component of the instantiated GenuineNormativity is pure logic: its canonical witness is exactly `⟨Incompatible NoGN (¬ NoGN), prop_neq_neg NoGN⟩` (incompatibility with one's negation + propositional non-triviality). The opposition conjunct
* **Nostrongtruth_Selfrefutes:** `noStrongTruth_selfRefutes` (`formal/Logos/Semantics.lean`) — Denying strong truth refutes itself: it cannot be the case that no formula is necessarily true — the act of denying strong truth is destroyed by strong truth (performative retorsion of C59, footprint {CL}).
* **Denial_Of_Genuine_Choice_Is_Self_Refuting:** `denial_of_genuine_choice_is_self_refuting` (`formal/Logos/StrongActionChoice.lean`) — Theorem: Under RetorsiveAvailability and deliberative settlement, the denial of genuine choice is self-refuting.
* **Denial_Of_No_Metaphysical_Alternative_Is_Self_Refuting:** `denial_of_no_metaphysical_alternative_is_self_refuting` (`formal/Logos/StrongActionChoice.lean`) — Theorem: Under the RetorsiveAvailability principle, performing a denial of availability is self-refuting.
* **Bridge_C_Performative_Judge_Yields_Choice_Field:** `bridge_c_performative_judge_yields_choice_field` (`formal/Logos/UndeniableNormativeDerivation.lean`) — Bridge C: Performative Retorsion Bridge (Judging Act) derives ChoiceField.
* **Bridge_D_Retorsion_Derives_Free_Will:** `bridge_d_retorsion_derives_free_will` (`formal/Logos/UndeniableNormativeDerivation.lean`) — Bridge D: Transcendental Retorsion of Genuine Normativity derives Free Will under Judicative Bipolarity (`AxJudicativeBipolarity`).
* **D1_D2_Denial_Contradicts_Core_Retorsion:** `d1_d2_denial_contradicts_core_retorsion` (`formal/Logos/UndeniableNormativeDerivation.lean`) — D1 & D2: Denial of Existence — denying extensional Right/Wrong directly contradicts core retorsion.
</details>

* [Right and Wrong, Bivalence, and Retorsion](investigations/right-and-wrong.md) — LOGICAL (`{CL}`) / ZERO SUBSTANTIVE AXIOMS

### Countermodels & Independence

<details>
<summary>Countermodel catalogue — 6 independence frontiers (click to expand)</summary>

* **consequence_A_reasoning ⇏ libertarian:** `consequence_A_reasoning_not_entails_libertarian` (`formal/Logos/AgencyDeterminismConsequences.lean:405`) — Consequence A: Reasoning does NOT logically entail libertarian freedom.
* **consequence_B_first_person ⇏ libertarian:** `consequence_B_first_person_not_entails_libertarian` (`formal/Logos/AgencyDeterminismConsequences.lean:430`) — Consequence B: First-person subjectivity does NOT entail libertarian freedom.
* **consequence_C_intentionality ⇏ libertarian:** `consequence_C_intentionality_not_entails_libertarian` (`formal/Logos/AgencyDeterminismConsequences.lean:438`) — Consequence C: Intentionality does NOT entail libertarian freedom.
* **consequence_D_normativity ⇏ libertarian:** `consequence_D_normativity_not_entails_libertarian` (`formal/Logos/AgencyDeterminismConsequences.lean:446`) — Consequence D: Normativity does NOT entail libertarian freedom.
* **D1_discrimination ⇏ choice:** `D1_discrimination_not_entails_choice` (`formal/Logos/CognitiveDiscrimination.lean:207`) — Property D1 (FAILS): Discrimination does NOT entail Choice! Hostile model: s discriminates p from q, but makes no choice.
* **D2_discrimination ⇏ meaning:** `D2_discrimination_not_entails_meaning` (`formal/Logos/CognitiveDiscrimination.lean:216`) — Property D2 (FAILS): Discrimination does NOT entail Representation/Meaning of q! Hostile model: s discriminates p from an external contrast boundary q without meaning q.
</details>

* [Complete Catalog of Hostile Models Across Γ](investigations/countermodels.md) — INDEPENDENCE & SEPARATION THEOREMS (Footprint `{}`)

### Detailed Investigations

* [Contrastive Choice, Action, and Axiom A14](investigations/contrastive-choice.md) — SEMANTIC BRIDGE A14 (`AxIntentionalChoice`, Tag: SEM) / INDEPENDENCE THEOREMS (`{}`)
* [Contingent Creation and Teleology](investigations/creation.md) — SPLIT INTO TWO — **existence** is `PROVEN` (C350 `CosmicExistence.contingent_realm_obtains`, `{propext, Subject}`, no bridge) and **meaning** is `PROVEN↑` (C367 `CosmicExistence.cosmos_obtains`, under the plurality bridge `AxTwoSubjects`) / PRODUCTION (F9 lane L3) DEFERRED / COUNTERMODEL ON THE *ENTAILMENT* ONLY (C110)
* [Personal Agency and the Rejection of Impersonalism](investigations/divine-personhood.md) — THEOREMS OF CONSTITUTIVE PERSONAL AGENCY (`{Initiates, Means, State, Subject, CL}`, 0 Substantive Axioms)
* [The Normative Route to Free Will](investigations/free-will.md) — LOGICAL derivation from CONSTITUTIVE SEMANTICS (`{Means, Subject}`, 0 substantive axioms)
* [Constructive Personal Ground of Normativity and Reality](investigations/grounding.md) — THEOREMS T7 & T8 (0 Substantive Axioms / Minimal Classical Logic)
* [The Incarnation — The Builder Entering the House](investigations/incarnation.md) — DEFERRED THEOLOGICAL BRIDGE / UNINCARNATE MODEL (`{}`)
* [Plurality of Divine Persons and Eternal Love](investigations/plurality-and-love.md) — THEOREMS T12, T13, T14 (`{Means, Subject, AxTwoSubjects}`); T30 (GAPMAP Level 21, C322–C354)
* [The Trinity and the Condilectus Principle](investigations/trinity.md) — DEFERRED THEOLOGICAL BRIDGE / BINITARIAN SEPARATION MODEL (`{}`)

### Technical

* [Technical Appendix: Kernel Audit, Consistency & Code Annex](investigations/kernel-audit.md) — Complete kernel audit, transitive axiom footprints, dependency ledger, and consistency checks.
* [Formal Dependency Graph (JSON)](formal/depgraph.json) / [(DOT)](formal/depgraph.dot) — LeanDepViz transitive kernel dependency DAG.
* [Theorem Ledger (GAPMAP)](formal/GAPMAP.md) — Formal correspondence mapping across formal and prose corpora.
