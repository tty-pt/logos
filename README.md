# Γ — The Deduction

> **Γ is a machine-checked deduction**: genuine normativity — an objective right/wrong
> binding our judgments — forces a *personal* ground. Free will is *derived, never
> assumed* (`GenuineNormativity ⇒ Chooses ⇒ FreeWill ⇒ FreeSubject ⇒ Person`);
> wherever right/wrong is real, its ground-type is personal (`RightWrong ⇒ Person`).
> A necessary Divine Being/Ground — eternal (everlasting and atemporal) and possessing Canonical Aseity (`conditional_canonical_aseity`) — is **proven** (✅); Divine Personhood and monotheism are **deferred** (⏸); every other claim is
> definitional, derived, or a declared axiom.

Every section below answers the same question — *what is the status of this claim?*

> **The Dialectical Inevitability Architecture** — Why every rational attack fails:
> 1. **Performative Retorsion (The Trap):** Any attempt to deny objective correctness must claim that its denial is *correct* (`ClaimsCorrect s NoRight`). In the Lean kernel, claiming denial as correct while true yields a direct constructive contradiction (`claims_correct_no_right_self_refuting` → ⊥, 0 substantive axioms). The skeptic cannot even enter the debate without triggering the normative partition.
> 2. **Constitutive Semantics (The Deduction):** Rational address between incompatible alternatives is *definitionally* Choice (`Chooses`), having choice is *definitionally* Free Will (`FreeWill`), and a free choosing subject is *definitionally* a Person in the classical Boethian-Thomistic sense (`person_iff_thomisticCore`), all verified with 0 substantive axioms.
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
        │ [discovery · constitutive theorem [Person := FreeSubject]]
        ▼
PERSON
  A free subject is constitutively an authoritative Person.
  ⊢ Person s : Prop := FreeSubject s
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
  The machine-proved dependence: wherever Right/Wrong is real, its ground-type is personal (`∀ s, RightWrong s → Person s`). The `GroundsRightWrong` record merely registers that same dependence (see §8).
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

📘 · [Agency.lean#Act](formal/Logos/Agency.lean#L155)

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

📘 · [Choice.lean#FreeSubject](formal/Logos/Choice.lean#L170)

§15 — freedom (DEFINITION; freedom/choice fix, 2026-09-18): a subject is free iff it genuinely chooses between some incompatible pair. The implication choice → freedom is definitional (`chooses_implies_freeWill`).

    ∴ FreeWill ≡ ∃ p, q, Chooses(s, p, q)

📘 · [Choice.lean#FreeWill](formal/Logos/Choice.lean#L163)

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

Person: a subject possessing a numerically distinct free will.

    ∴ Person ≡ FreeSubject(s)

📘 · [Person.lean#Person](formal/Logos/Person.lean#L29)

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

✅ · [Choice.lean#deliberateChoice_implies_chooses](formal/Logos/Choice.lean#L446)

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

📘 · [Choice.lean#Chooses](formal/Logos/Choice.lean#L102)

Every proposition is incompatible with its own negation.

    ∴ Incompatible(p, ¬p)

✅ · [Choice.lean#incompatible_self_negation](formal/Logos/Choice.lean#L110)

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

✅ · [Choice.lean#freeWillExists_of_chooses](formal/Logos/Choice.lean#L206)

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
> **Machine-Checked Kernel Rebuttal —** [`freeSubject_iff_freeWill`](formal/Logos/Choice.lean#L173) (Footprint: 0 substantive axioms):
> `⊢ FreeSubject s ↔ FreeWill s`
</details>

<details>
<summary>Definitions used in this section (2; 0 new, 2 already shown)</summary>

    ∴ FreeSubject ≡ FreeWill(s) — defined in §3. Genuine Choice.

    ∴ FreeWill ≡ ∃ p, q, Chooses(s, p, q) — defined in §3. Genuine Choice.

</details>

FreeSubject and FreeWill are definitionally equivalent.

    ∴ FreeSubject(s) ↔ FreeWill(s)

✅ · [Choice.lean#freeSubject_iff_freeWill](formal/Logos/Choice.lean#L173)

<details>
<summary>Formal Derivation (1 step, natural deduction, 0 substantive axioms)</summary>

    1. FreeSubject(s) ↔ FreeWill(s)  (definitional equality / reflection)

    ∴ FreeSubject(s) ↔ FreeWill(s)

</details>

<details>
<summary>Supporting Infrastructure — 1 auxiliary theorem(s) beneath this step</summary>

Genuine choice entails a free subject — by definition.

    Chooses(s, p, q) → FreeSubject(s)

✅ · [Choice.lean#chooses_implies_freeSubject](formal/Logos/Choice.lean#L187)

</details>

> ➔ **Linear Forward Transition to Step 6 (Person):** [▲ Discovery · *constitutive theorem [Person := FreeSubject]*]

---

## 6. Person

In the unified Γ ontology, Personhood is defined constitutively in the classical sense of Boethius and Aquinas — an *individual substance of a rational nature*, with *dominion over its own acts* — formalized as a subject possessing genuine free will (`Person(s) := FreeSubject(s)`); the equivalence with the explicit Thomistic person core (`IndividualSubstance ∧ RationalNature ∧ DominionOverActs`) is proved below (`person_iff_thomisticCore`, 0 substantive axioms). Personhood is therefore not an opaque or unprovable predicate: every Free Subject is an authoritative Person by pure deduction (`free_subject_is_person`). This is the first point at which the personal subject properly enters the main deduction.

*(Detailed technical proof & model analysis: [investigations/divine-personhood.md](investigations/divine-personhood.md))*

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** A loaded, theological word smuggled into the deduction.
> **The reply / the frontier —** Classical, not novel: the term follows Boethius and Aquinas rather than theological invention. Nothing theological is *assumed*; theology would enter only downstream, in the branches — and is then explicitly bounded by countermodels.
>
> **Machine-Checked Kernel Rebuttal —** [`person_iff_thomisticCore`](formal/Logos/Person.lean#L137) (Footprint: 0 substantive axioms):
> `⊢ Person s ↔ IndividualSubstance s ∧ RationalNature s ∧ DominionOverActs s`
</details>

<details>
<summary>Definitions used in this section (4; 1 new, 3 already shown)</summary>

Thomistic person core: the Boethius–Aquinas conditions of personhood — "individual substance of a rational nature" possessed of dominion over its own acts — formalized through their operative distinguishing features.

    ∴ ThomisticPersonCore ≡ IndividualSubstance(s) ∧ RationalNature(s) ∧ DominionOverActs(s)

📘 · [Person.lean#ThomisticPersonCore](formal/Logos/Person.lean#L83)

    ∴ FreeSubject ≡ FreeWill(s) — defined in §3. Genuine Choice.

    ∴ FreeWill ≡ ∃ p, q, Chooses(s, p, q) — defined in §3. Genuine Choice.

    ∴ Person ≡ FreeSubject(s) — defined in §3. Genuine Choice.

</details>

Master Theorem: Every Free Subject is a Person.

    FreeSubject(s) → Person(s)

✅ · [Person.lean#free_subject_is_person](formal/Logos/Person.lean#L33)

<details>
<summary>Formal Derivation (1 step, natural deduction, 0 substantive axioms)</summary>

Assume FreeSubject(s):

    1. Person(s)  (definitional identity via h)

    ∴ Person(s)

</details>

Master Correspondence: Personhood is constitutively equivalent to the Thomistic person core.

    ∴ Person(s) ↔ ThomisticPersonCore(s)

✅ · [Person.lean#person_iff_thomisticCore](formal/Logos/Person.lean#L137)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

    1. split into forward and reverse directions (↔ / ∧)  (split equivalence/conjunction into forward (mp) and reverse (mpr) goals)
    2. assume hp  (hypothesis assumption for conditional/reductio proof)
    3. assume hc  (hypothesis assumption for conditional/reductio proof)

    ∴ Person(s) ↔ ThomisticPersonCore(s)

</details>

<details>
<summary>Supporting Infrastructure — 2 auxiliary theorem(s) beneath this step</summary>

Master Equivalence: Personhood is constitutively equivalent to Free Subjecthood.

    ∴ Person(s) ↔ FreeSubject(s)

✅ · [Person.lean#person_iff_freeSubject](formal/Logos/Person.lean#L38)

<details>
<summary>Formal Derivation (1 step, natural deduction, 0 substantive axioms)</summary>

    1. Person(s) ↔ FreeSubject(s)  (definitional equality / reflection)

    ∴ Person(s) ↔ FreeSubject(s)

</details>

Every Person possesses Free Will.

    Person(s) → FreeWill(s)

✅ · [Person.lean#person_has_free_will](formal/Logos/Person.lean#L48)

<details>
<summary>Formal Derivation (1 step, natural deduction, 0 substantive axioms)</summary>

Assume Person(s):

    1. FreeWill(s)  (definitional identity via h)

    ∴ FreeWill(s)

</details>

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
> **Machine-Checked Kernel Rebuttal —** [`person_iff_freeIndependentWill`](formal/Logos/Person.lean#L117) (Footprint: 0 substantive axioms):
> `⊢ Person s ↔ FreeIndependentWill s`
</details>

<details>
<summary>Definitions used in this section (4; 2 new, 2 already shown)</summary>

Free, Independent Will: a subject endowed with both the capacity of free choice (`FreeWill s`) and an independently individuated volitional faculty (`IndependentWill s`).

    ∴ FreeIndependentWill ≡ FreeWill(s) ∧ IndependentWill(s)

📘 · [Person.lean#FreeIndependentWill](formal/Logos/Person.lean#L59)

Independent Will: the faculty of will possessed by subject s is uniquely its own, numerically distinct from the will of any distinct subject.

    ∴ IndependentWill ≡ ∀ s', s' ≠ s → subjectWill(s') ≠ subjectWill(s)

📘 · [Person.lean#IndependentWill](formal/Logos/Person.lean#L54)

    ∴ Person ≡ FreeSubject(s) — defined in §3. Genuine Choice.

    ∴ ThomisticPersonCore ≡ IndividualSubstance(s) ∧ RationalNature(s) ∧ DominionOverActs(s) — defined in §6. Person.

</details>

Master Equivalence: Personhood is constitutively equivalent to Free, Independent Will.

    ∴ Person(s) ↔ FreeIndependentWill(s)

✅ · [Person.lean#person_iff_freeIndependentWill](formal/Logos/Person.lean#L117)

<details>
<summary>Formal Derivation (5 steps, natural deduction, 0 substantive axioms)</summary>

    1. split into forward and reverse directions (↔ / ∧)  (split equivalence/conjunction into forward (mp) and reverse (mpr) goals)
    2. assume hp  (hypothesis assumption for conditional/reductio proof)
    3. hp  (conjunction conjunct 1: hp)
    4. independent_will_of_subject s  (conjunction conjunct 2: independent_will_of_subject s)
    5. assume ⟨hFW, _⟩  (hypothesis assumption for conditional/reductio proof)

    ∴ Person(s) ↔ FreeIndependentWill(s)

</details>

<details>
<summary>Supporting Infrastructure — 3 auxiliary theorem(s) beneath this step</summary>

Numerical individuation guarantees that every subject possesses an independent will.

    ∴ IndependentWill(s)

✅ · [Person.lean#independent_will_of_subject](formal/Logos/Person.lean#L110)

Master Theorem: Every Person possesses a Free, Independent Will.

    Person(s) → FreeIndependentWill(s)

✅ · [Person.lean#person_has_free_independent_will](formal/Logos/Person.lean#L126)

Master Equivalence: free, independent will is equivalent to the Thomistic person core.

    ∴ FreeIndependentWill(s) ↔ ThomisticPersonCore(s)

✅ · [Person.lean#freeIndependentWill_iff_thomisticCore](formal/Logos/Person.lean#L102)

<details>
<summary>Formal Derivation (1 step, natural deduction, 0 substantive axioms)</summary>

    1. split into forward and reverse directions (↔ / ∧)  (split equivalence/conjunction into forward (mp) and reverse (mpr) goals)

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
> **Machine-Checked Kernel Rebuttal —** [`will_identity_collapses_normativity`](formal/Logos/PersonalNormativeGround.lean#L261) (Footprint: 0 substantive axioms):
> `⊢ Wills s p = Ought s p → NormativeViolation s p → ⊥`
</details>

<details>
<summary>Definitions used in this section (6; 3 new, 3 already shown)</summary>

GroundedNormativePolarity: Normative polarity is ontologically grounded in a subject endowed with free, independent will, witnessing the personal ontological ground-type.

    ∴ GroundedNormativePolarity ≡ FreeIndependentWill(s) ∧ GroundsRightWrong s

📘 · [PersonalNormativeGround.lean#GroundedNormativePolarity](formal/Logos/PersonalNormativeGround.lean#L231)

GroundsRightWrong: Objective Right/Wrong is ontologically grounded in an agential basis of a personal kind/type.

    ∴ structure GroundsRightWrong (s : Subject) : Prop where

📘 · [PersonalNormativeGround.lean#GroundsRightWrong](formal/Logos/PersonalNormativeGround.lean#L199)

Right/Wrong Distinction at contents p and q for subject s: The subject is addressed by an objective deontic opposition between Right (p) and Wrong (q).

    ∴ RightWrongAt ≡ GenuineNormativity s p q

📘 · [PersonalNormativeGround.lean#RightWrongAt](formal/Logos/PersonalNormativeGround.lean#L148)

    ∴ Chooses ≡ Means(s, p) ∧ Means(s, q) ∧ Incompatible(p, q) — first shown in §3. Genuine Choice.

    ∴ FreeWill ≡ ∃ p, q, Chooses(s, p, q) — defined in §3. Genuine Choice.

    ∴ Person ≡ FreeSubject(s) — defined in §3. Genuine Choice.

</details>

Direct Derivation: The derived subject s instantiates the personal ground of the normative datum.

    RightWrongAt(s, p, q) → Person(s) ∧ GroundsRightWrong s

✅ · [PersonalNormativeGround.lean#person_grounds_original_normative_datum](formal/Logos/PersonalNormativeGround.lean#L471)

Master Grounding Theorem from Personhood (Historical Compatibility Name): Personhood supplies the ontological ground-type required by the normative order.

    Person(s) → GroundsRightWrong s

✅ · [PersonalNormativeGround.lean#person_grounds_normative_polarity](formal/Logos/PersonalNormativeGround.lean#L385)

<details>
<summary>Supporting Infrastructure — 3 auxiliary theorem(s) beneath this step</summary>

Master Realization Theorem: Any Person realizes GroundedNormativePolarity, showing that normative polarity is grounded in a personal ontological basis.

    Person(s) → GroundedNormativePolarity(s)

✅ · [PersonalNormativeGround.lean#person_realizes_grounded_polarity](formal/Logos/PersonalNormativeGround.lean#L401)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

Assume Person(s):

    1. FreeIndependentWill(s)  (modus ponens via (person_iff_freeIndependentWill)
    2. hFW  (conjunction conjunct 1: hFW)
    3. person_grounds_right_wrong s hPerson  (conjunction conjunct 2: person_grounds_right_wrong s hPerson)

    ∴ GroundedNormativePolarity(s)

</details>

The Non-Reversal Architectural Principle: 1. Deductive Discovery runs forward: RightWrongAt s p q ⇒ ... ⇒ Person s ⇒ GroundsRightWrong s.

    ∴ (RightWrongAt(s, p, q) → Person(s) ∧ GroundsRightWrong s) ∧ (Person(s) → GroundsRightWrong s)

✅ · [PersonalNormativeGround.lean#non_reversal_discovery_and_grounding](formal/Logos/PersonalNormativeGround.lean#L515)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

    1. fun h => forward_modus_ponens_derivation s p q h  (component witness 1: fun h => forward_modus_ponens_derivation s p q h)
    2. fun hp => person_grounds_right_wrong s hp  (component witness 2: fun hp => person_grounds_right_wrong s hp)

    ∴ (RightWrongAt(s, p, q) → Person(s) ∧ GroundsRightWrong s) ∧ (Person(s) → GroundsRightWrong s)

</details>

Non-Circularity Architectural Theorem: The retorsive discovery proof of Free Will (`indubitable_normative_free_will`) does NOT require or depend upon any grounding bridge.

    GenuineNormativity s p q → Chooses(s, p, q) ∧ FreeWill(s)

✅ · [PersonalNormativeGround.lean#discovery_independent_of_grounding](formal/Logos/PersonalNormativeGround.lean#L587)

</details>

<details>
<summary>Obstruction / Formal Boundary: `model_b_separation`</summary>

### Obstruction / Formal Boundary: `model_b_separation`

Theorem: Separation Theorem from Model B.

    model_b_separation ⇏ Independence

🧱 model_b_separation ⇏ Independence · [PersonalNormativeGround.lean#model_b_separation](formal/Logos/PersonalNormativeGround.lean#L674)

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

✅ · [NecessaryPersonalGround.lean#step1_necessary_truth_exists](formal/Logos/NecessaryPersonalGround.lean#L191)

> ➔ **Linear Forward Transition to Step 10 (Constructive Personal Ground):** [▲ Discovery · *constructive discovery [ObjectiveNormativity ⇒ Person]*]

---

## 10. Constructive Personal Ground

The dependence `RightWrong ⇒ Person` was proved in §8. Its constructive form needs no grounding axiom: the ontological direction is encoded in the definition — `ObjectiveNormativity ⇒ Person` is discovery, `Person ⇒ Right/Wrong` is RightWrong indexed by Person (the `GroundsRightWrong` record).

The headline — 'the Person supports the reality of Right' — asserts that the RightWrong-reality, the objective correctness structure governing judgments about what is the case, has a personal ontological ground-type. The four distinctions of §8 apply unchanged; in particular, grounding the correctness order is not producing reality (§8, distinction 4).

*(Detailed technical proof & model analysis: [investigations/divine-personhood.md](investigations/divine-personhood.md))*

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** You still quietly pick a contingent author of morality — some particular person who happens to ground Right/Wrong.
> **The reply / the frontier —** The indexing encodes *dependence without nomination*: RightWrong is indexed by a personal kind/type, not by any arbitrary contingent individual — objective Normativity ⇒ Person is discovery, Person ⇒ Right/Wrong is the typed index. And Branch C below marks exactly what is NOT forced: trinity, contingent creation, and incarnation all remain countermodel frontiers (⇏).
>
> **Machine-Checked Kernel Rebuttal —** [`discover_person`](formal/Logos/PersonalNormativeGround.lean#L103) (Footprint: 0 substantive axioms):
> `⊢ ObjectiveNormativity → Σ' p, RightWrong p`
</details>

<details>
<summary>Definitions used in this section (10; 3 new, 7 already shown)</summary>

The Invariant Necessity of the Objective Normative Order: holds across all possible worlds via Logos.Necessity.Necessity.

    ∴ NecessaryNormativeOrder ≡ ∀ w, NormativeOrderAt(w)

📘 · [NecessaryPersonalGround.lean#NecessaryNormativeOrder](formal/Logos/NecessaryPersonalGround.lean#L105)

Objective Normativity: the existence of a person whose judgment carries Right/Wrong.

    ∴ ObjectiveNormativity ≡ ∃ p, RightWrong(p)

📘 · [PersonalNormativeGround.lean#ObjectiveNormativity](formal/Logos/PersonalNormativeGround.lean#L97)

Right and Wrong distinction indexed by Person: The normative distinction is genuinely addressed to and held by the person.

    ∴ RightWrong ≡ ∃ a, b, GenuineNormativity p.subject a b

📘 · [PersonalNormativeGround.lean#RightWrong](formal/Logos/PersonalNormativeGround.lean#L93)

    ∴ ClaimsCorrect ≡ Act s p ∧ Means(s, Correct s p) — defined in §1. Objective Right and Wrong.

    ∴ EstablishedRightWrong ≡ ¬N_T ∧ ¬N_F — first shown in §1. Objective Right and Wrong.

    ∴ structure GroundsRightWrong (s : Subject) : Prop where — defined in §8. Personal Agency as Ontological Ground of Normativity.

    ∴ IsFalse ≡ ¬T(p) — defined in §2. Ought and Normative Polarity.

    ∴ NoRight ≡ ¬NormativeRightExists — defined in §1. Objective Right and Wrong.

    ∴ Person ≡ FreeSubject(s) — defined in §3. Genuine Choice.

    ∴ T ≡ p — defined in §2. Ought and Normative Polarity.

</details>

The ontology in one universal: wherever Right/Wrong is real, its ground-type is personal (the 'simple thing'). The elaborated `GroundsRightWrong` record is its record-form (DEFINITIONAL).

    ∴ RightWrong(s) → Person(s)

✅ · [PersonalGroundOfReality.lean#personal_ground_of_right_wrong](formal/Logos/PersonalGroundOfReality.lean#L98)

Constructive direction of discovery: Objective Normativity ⇒ Person.

    ∴ ObjectiveNormativity → ∃ p, RightWrong(p)

✅ · [PersonalNormativeGround.lean#discover_person](formal/Logos/PersonalNormativeGround.lean#L103)

<details>
<summary>Formal Derivation (1 step, natural deduction, 0 substantive axioms)</summary>

    1. assume h  (hypothesis assumption for conditional/reductio proof)

    ∴ ObjectiveNormativity → ∃ p, RightWrong(p)

</details>

HEADLINE — THE PERSON SUPPORTS THE REALITY OF RIGHT.

    ∴ (¬∃ s, ClaimsCorrect(s, NoRight) ∧ NoRight) ∧ EstablishedRightWrong ∧ (∀ p, T(p) ∨ IsFalse(p)) ∧ NecessaryNormativeOrder ∧ (∀ s, RightWrong(s) → Person(s)) ∧ (∀ s, Person(s) → GroundsRightWrong s)

✅ · [PersonalGroundOfReality.lean#the_person_supports_the_reality_of_right](formal/Logos/PersonalGroundOfReality.lean#L150)

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

✅ · [PersonalNormativeGround.lean#objective_normativity_holds](formal/Logos/PersonalNormativeGround.lean#L127)

<details>
<summary>Formal Derivation (6 steps, natural deduction, 0 substantive axioms)</summary>

Assume ∃ s, a, b, GenuineNormativity s a b:

    1. witness components ⟨s, a, b, h⟩  (existential elimination from hDatum)
    2. s  (conjunction conjunct 1: s)
    3. (Logos.IndubitableNormativeFreeWill.indubitable_normative_free_will h).2  (conjunction conjunct 2: (Logos.IndubitableNormativeFreeWill.indubitable_normative_free_will h).2)
    4. a  (conjunction conjunct 3: a)
    5. b  (conjunction conjunct 4: b)
    6. h  (conjunction conjunct 5: h)

    ∴ ObjectiveNormativity

</details>

HEADLINE (instance form, datum-guarded). The personal ontological ground is the necessary ground of the objective normative/truth order governing judgments about Γ-reality (Right/Wrong, truth/falsity, Ought/OughtNot under TruthNorm): it grounds the correctness of propositions *about* what is the case, not the fact of what exists.

    Person(s) → Person(s) ∧ GroundsRightWrong s ∧ NecessaryNormativeOrder

✅ · [PersonalGroundOfReality.lean#person_yields_personal_grounding_of_reality](formal/Logos/PersonalGroundOfReality.lean#L196)

<details>
<summary>Formal Derivation (3 steps, natural deduction, 0 substantive axioms)</summary>

Assume Person(s):

    1. hPerson  (component witness 1: hPerson)
    2. person_grounds_right_wrong s hPerson  (component witness 2: person_grounds_right_wrong s hPerson)
    3. necessary_normative_order  (component witness 3: necessary_normative_order)

    ∴ Person(s) ∧ GroundsRightWrong s ∧ NecessaryNormativeOrder

</details>

</details>

### Branch A: Necessity and Eternity of the Divine Being (Ground)

Live theorem: the ground is world-rigid (`NecessaryEntity Entity.ofGround`, `∀ w, ExistsAt w .ofGround`, definitional `EntityExistsAt w .ofGround := True`, footprint `{Means, Subject}`), **everlasting**, **atemporal**, and possesses **Canonical Aseity** (`conditional_canonical_aseity`, `{Means, Subject}`: `¬ ∃ g, ExternalGrounding g .ofGround`). Claim E is the *non-hypostatic* pairing (`∃ g s, NecessaryEntity g ∧ NecessaryGroundOfReality g ∧ Person s ∧ GroundsRightWrong s`): entity-necessity conjunct PROVEN; personal-kind conjunct honestly `{AxTwoSubjects, Means, Subject}` (PROVEN↑ under META `AxTwoSubjects`). Hypostatic identity, a 'necessary Person', Trinity and monotheism are NOT claimed — `ofGround_ne_ofSubject` blocks the identity line.

HEADLINE — the necessary ground of reality exists: `Entity.ofGround` is a necessary entity and the ontological ground of reality.

    ∴ NecessaryGroundOfReality Entity.ofGround

✅ · [NecessityEternity.lean#ofGround_necessary_ground_of_reality](formal/Logos/NecessityEternity.lean#L148)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

    1. ofGround_necessary  (component witness 1: ofGround_necessary)
    2. ofGround_ground_of_reality  (component witness 2: ofGround_ground_of_reality)

    ∴ NecessaryGroundOfReality Entity.ofGround

</details>

### Branch B: Divine Uniqueness and Monotheism

Annotated surface only — not a theorem of this repository. The strict-monotheism theorems (`monotheism_of_god_and_uniqueness`, `monotheism_compatible_with_trinity`) are deferred out of the live kernel (see `NecessaryPersonalGround.lean`); no compiled declaration exists. The trinity-compatibility claim is not a theorem of the current build.

> ⏸ **DEFERRED** — annotated surface only; the strict-monotheism theorems carry the same deferral as Branch A: no compiled declaration exists in the live kernel.

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

Acosmic Divine Model: A necessary divine ground exists with zero contingent created reality.

    necessary_ground ⇏ contingent_creation

🧱 necessary_ground ⇏ contingent_creation · [ConditionalTheology.lean#necessary_ground_not_entails_contingent_creation](formal/Logos/ConditionalTheology.lean#L420)

<details>
<summary>Formal Derivation (2 steps, natural deduction, 0 substantive axioms)</summary>

    1. witness tuple ⟨Empty, Unit, fun _ p => p, fun _ => True, ?_⟩  (existential/conjunction refinement with Empty, Unit, fun _ p => p, fun _ => True, ?_)
    2. witness tuple ⟨⟨(), trivial, fun _ hp => hp⟩  (existential/conjunction refinement with ⟨(), trivial, fun _ hp => hp)

    ∴ ∃ Subj, Ent, Ground, Nec, -- Necessary ground exists (∃ e, Nec e ∧ ∀ p, p → Ground e p) ∧ -- Zero contingent subjects exist ¬(∃ _c, True)

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

* **`C78`** (`T7 — Modal.contingent_ground`) — Contingent ground is retired: manufactured witness destroyed under hostile semantics.
* **`C79`** (`T7 — Modal.ultimateGround_exists`) — Ultimate ground existence is blocked: infinite descending chains have no ultimate element without a well-foundedness axiom.
* **`C87`** (`T7 — Modal.origin_is_necessary`) — Origin necessity is retired: manufactured origin witness destroyed.
* **`C88`** (`T7 — Modal.transcendental_quantifier_swap`) — Transcendental quantifier swap is retired: the manufactured origin quantifier swap was destroyed under hostile semantics; the declaration is absent from the live kernel.
* **`C89`** (`T7 — Modal.ultimateGroundInit_exists`) — Ultimate ground by initiation is blocked: non-entailed without well-foundedness.
* **`C90`** (`T8 — GroundPerson.personal_ultimate_ground_exists`) — Personal ultimate ground is blocked: ultimate grounding does not entail personal nature.
* **`F2`** (`§21 teleology (`Ought → Goal`) — `) — Deontic teleology is deferred: how norms point at goals is not yet derived.
* **`F6`** (`§28 Trinity — `) — The Trinity is deferred: no argument exists yet.
* **`C69`** (`§15/F1b — `) — Free will of origin is retired: manufactured constructor split destroyed.
* **`C70`** (`§15/F1b — `) — Posited content non-freedom is retired: manufactured witness destroyed.
* **`C71`** (`§15/F1b — `) — Origin freedom denial self-refuting is retired: manufactured witness destroyed.
* **`C72`** (`§15/F1b — `) — Judge is free is retired: act does not entail free will; `judge_commits` yields only the choice field.
* **`C73`** (`P5/P7 — Person.twoPersonsFromSubject`) — Plurality without bridges is blocked: unit countermodel settles that 1 act does not entail plurality; requires AxTwoSubjects.
* **`C75`** (`P7 — Person.everyContentIsAPerson`) — Propositional personhood is blocked: content existence does not entail personhood.
* **`C76`** (`P8 — Love.T14_canonicalRigid`) — Canonical rigid love is retired: plurality does not entail love without substantive relational bridges.
* **`C77`** (`P5/P8 — Love.necessaryPersonExists_conditional`) — Conditional necessary-person claim is deferred: the theorem Love.necessaryPersonExists_conditional was removed from the live kernel (commit ae7f4bd); retained as annotated conditional surface only, never a derived divine Person.
* **`C92`** (`P8/§27 — Love.necessary_entity_exists_conditional`) — Conditional necessary-entity claim is deferred: the theorem Love.necessary_entity_exists_conditional was removed from the live kernel (commit ae7f4bd); retained as annotated conditional surface only.
* **`C64`** (`§1 — Initiation.originates_not_transfer`) — Movement not transfer is retired: initiation constructor evaluation excised.
* **`C65`** (`§1/T5 — Initiation.person_iff_originates`) — Person iff originates is retired: manufactured initiation identity excised.
* **`C66`** (`§1 fnd — Initiation.Cogito_Init`) — Cogito as initiation is retired: manufactured initiation witness excised.
* **`C67`** (`§1 fnd — Initiation.noInitiation_selfRefutes`) — Denial of initiation self-refuting is retired: manufactured witness excised.
* **`C80`** (`§1 — Initiation.posited_not_branch`) — Posited content deterministic transfer is retired: constructor evaluation excised.
* **`C81`** (`§1 — Initiation.origin_branches`) — Origin branching is retired: constructor evaluation excised.
* **`C82`** (`§1/§12 — Initiation.origin_is_initiating_person`) — Origin initiating person is retired: constructor evaluation excised.
* **`F8`** (`Trinity — `) — The Trinity is not attempted.
* **`F9`** (`Incarnation / creation — `) — Incarnation and creation are faith data from the poem, deferred.

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

| Classical characteristic | Scope | Status | Exact sense established by the current theory (reference) |
|---|---|---|---|
| **Personal** — the ground-type is personal | Personal ground / person-type | ✅ PROVEN | `RightWrong ⇒ Person` (`∀ s, RightWrong s → Person s`). Established of the personal ground/type, not of a particular divine person. — [PersonalGroundOfReality.lean#personal_ground_of_right_wrong](formal/Logos/PersonalGroundOfReality.lean#L98), footprint {Means, Subject} |
| **Psychological personality** (humanoid consciousness, stream of experience) | Personal ground / person-type | 🧱 INDEPENDENT | Minimal constitutive personhood in Γ is functional: the locus of non-derived normative discrimination (`Person := FreeSubject`). Substantive psychological personhood (ordinary humanoid mind, emotional states, stream of consciousness) is provably independent: `faithful_model_satisfies_free_will_without_opaque_person` (footprint `{}`) satisfies free will without substantive psychological personality. The text explicitly disclaims ordinary psychological personality (`README-OLD.md:179-187`). — [PersonhoodOntologyAudit.lean#faithful_model_satisfies_free_will_without_opaque_person](formal/Logos/PersonhoodOntologyAudit.lean#L182), footprint {} ; [PersonhoodOntologyAudit.lean#faithful_contingent_person_fails_necessary_subject](formal/Logos/PersonhoodOntologyAudit.lean#L221), footprint {} |
| **Rational** — formally equivalent to the Thomistic core containing RationalNature | Personal ground / person-type | ✅ PROVEN | `Person(s) ↔ ThomisticPersonCore(s)`, whose conjunct `RationalNature s ≡ Intentional s ∧ FreeWill s` is definitional (`📘`). Established of the person-type. — [Person.lean#person_iff_thomisticCore](formal/Logos/Person.lean#L137), footprint {Means, Subject, Will, subjectWill, will_individuation} ; [Person.lean#RationalNature](formal/Logos/Person.lean#L70), footprint {Means, Subject} |
| **Free** — genuine normativity yields genuine choice and free will | Personal ground / person-type | ✅ PROVEN | `GenuineNormativity ⇒ Chooses ⇒ FreeWill`; `FreeWill s ≡ ∃ p q, Chooses s p q` is definitional (`📘`). — [IndubitableNormativeFreeWill.lean#indubitable_normative_free_will](formal/Logos/IndubitableNormativeFreeWill.lean#L115), footprint {Means, Subject} ; [Choice.lean#FreeWill](formal/Logos/Choice.lean#L163), footprint {Means, Subject} |
| **Independent will** — with numerical individuation | Personal ground / person-type | ✅ PROVEN | `Person(s) ↔ FreeIndependentWill(s)`; `subjectWill s₁ ≠ subjectWill s₂` — distinct persons have numerically distinct wills. The meaning-postulate status is kernel-verified: `will_individuation` is not derivable from the pre-will spine (`WillIndividuationAudit.will_individuation_not_forced_by_prewill_spine`, `{}`). — [Person.lean#person_iff_freeIndependentWill](formal/Logos/Person.lean#L117), footprint {Means, Subject, Will, subjectWill, will_individuation} ; [Person.lean#IndependentWill](formal/Logos/Person.lean#L54), footprint {Subject, Will, subjectWill} |
| **Dominion over acts** / authoritative personhood | Personal ground / person-type | ✅ PROVEN | the Thomistic-personcore conjunct `DominionOverActs s ≡ FreeWill s` is definitional (`📘`); present inside `person_iff_thomisticCore`. — [Person.lean#DominionOverActs](formal/Logos/Person.lean#L74), footprint {Means, Subject} |
| **Ground of objective normativity (Right and Wrong)** | Personal ground / person-type | ✅ PROVEN | `Person s → GroundsRightWrong s`, and the headline that "the person supports the reality of Right". Established of the personal ground. — [PersonalNormativeGround.lean#person_grounds_normative_polarity](formal/Logos/PersonalNormativeGround.lean#L385), footprint {Means, Subject} ; [PersonalGroundOfReality.lean#the_person_supports_the_reality_of_right](formal/Logos/PersonalGroundOfReality.lean#L150), footprint {Initiates, Means, State, Subject, CL} |
| **Non-relative core** — strict architectural invariance only | Proof architecture (not divine scope) | ✅ PROVEN | `(∀ l, AgentInvariant l → FreeWillInvariant l) ∧ ∃ l, FreeWillInvariant l ∧ ¬ AgentInvariant l` (GAPMAP C180; prose T18): the dependency-layer core admissible in every proof regime — including the non-agentive structural regime — is strictly contained in the core admissible across all agentive regimes (footprint `{}`, pure logic). This is proof architecture only: it does not establish that the Divine Being / Ground, a divine person, or the ultimate foundation is invariant across systems, perspectives, or worlds. — [HardenedInvariance.lean#agent_invariant_core_is_strictly_inside_freewill_invariant_core](formal/Logos/HardenedInvariance.lean#L226), footprint {} ; [HardenedInvariance.lean#strict_core_inclusion](formal/Logos/HardenedInvariance.lean#L173), footprint {} ; [HardenedInvariance.lean#agent_invariant_iff_agent_neutral_core](formal/Logos/HardenedInvariance.lean#L118), footprint {} ; [HardenedInvariance.lean#freewill_invariant_iff_freewill_neutral_core](formal/Logos/HardenedInvariance.lean#L153), footprint {} |
| **Necessary Divine Being / Ground** | Divine Being / Ground | ✅ PROVEN | The ground itself is world-rigid: `NecessaryEntity Entity.ofGround` (`∀ w, ExistsAt w .ofGround`, definitional `EntityExistsAt w .ofGround := True`, footprint `{Means, Subject}` — VOCAB only). Claim E is now a **live theorem** as a *non-hypostatic* pairing: the entity-necessity conjunct is PROVEN, the personal-kind conjunct is `{AxTwoSubjects, Means, Subject}` (PROVEN↑ under the declared META axiom `AxTwoSubjects`), and the hypostatic identity is blocked (`ofGround_ne_ofSubject`: `ofGround ≠ EntityOf s`). NO 'necessary Person' theorem exists — this row is the entity-level ground, distinct from the necessary-*order* row above. — [NecessityEternity.lean#ofGround_necessary_ground_of_reality](formal/Logos/NecessityEternity.lean#L148), footprint {Means, Subject} ; [NecessityEternity.lean#claimE](formal/Logos/NecessityEternity.lean#L291), footprint {AxTwoSubjects, Means, Subject} ; [NecessaryPersonalGround.lean#step1_necessary_truth_exists](formal/Logos/NecessaryPersonalGround.lean#L191), footprint {CL} ; [NecessaryPersonalGround.lean#necessary_normative_order](formal/Logos/NecessaryPersonalGround.lean#L110), footprint {Initiates, Means, State, Subject} |
| **Aseity** — non-derived / non-dependent | Divine Being / Ground | ✅ PROVEN | In the canonical ontology of entities, `conditional_canonical_aseity` (`CanonicalAseity.lean`, footprint `{Means, Subject}` — VOCAB only) establishes that `Entity.ofGround` has Canonical Aseity (`¬ ∃ g, ExternalGrounding g .ofGround`), conditional on all subjects being discriminating (`∀ s, ∃ p, ¬ Means s p`). Atomic entities are unconditionally excluded (`atom_cannot_ground_the_ground`, `{Means, Subject}`). At the generic modal frontier, C182 and C184 establish two-way logical independence between bare `Aseity` and volitional alternatives (footprint `{}`); that generic separation is not a proof or disproof of aseity for `Entity.ofGround` or the ultimate foundation. — [CanonicalAseity.lean#conditional_canonical_aseity](formal/Logos/CanonicalAseity.lean#L133), footprint {Means, Subject} ; [CanonicalAseity.lean#atom_cannot_ground_the_ground](formal/Logos/CanonicalAseity.lean#L96), footprint {Means, Subject} ; [CanonicalAseity.lean#canonical_aseity_implies_modal_aseity](formal/Logos/CanonicalAseity.lean#L73), footprint {Means, Subject} ; [ModalPossibilityFrontier.lean#aseity_does_not_force_any_volition_alternatives](formal/Logos/ModalPossibilityFrontier.lean#L463), footprint {} ; [ModalPossibilityFrontier.lean#volitional_alternative_does_not_force_aseity](formal/Logos/ModalPossibilityFrontier.lean#L485), footprint {} |
| **One God / strict monotheism** (unity of the Divine Being) | Divine Being / Ground | ⏸ DEFERRED | Strict monotheism (`monotheism_of_god_and_uniqueness`, `monotheism_compatible_with_trinity`) is deferred out of the live kernel (Branch B, `⏸`); unity concerns the Divine Being, not numerical identity of Personhood. Uniqueness is provably NOT a kernel consequence: the machine-witnessed separation `TheologicalModalHardening.necessary_existence_not_entails_uniqueness` (`¬ (∀ S, UniqueExists S.NecessaryEntity)`, L406-414, footprint `{}`) and the deferred `universal_ground_unique` (`NecessaryPersonalGround.lean:24`) mark it as an interpretive layer. |
| **Perfect (moral) goodness** | Divine Being / Ground | 🧱 INDEPENDENT | GAPMAP ledger row `F3 §28 (Good)` = COUNTERMODEL (🧱) via C175: the `M_amoral` model (`{}`) satisfies epistemic agential normativity with no practical obligation — the separation is permanent (`moral_pole_postulate_is_not_a_consequence`, vocabulary-only), so the moral pole is never *read off* the normative structure. Right/Wrong here is epistemic correctness, explicitly distinguished from moral good/evil. The *positive pole itself* is nevertheless obtained: `Good` is a fair definition (helping another person; `{Means, Subject}` — the definition smuggles nothing) and `moral_good_obtains` (C178) is PROVEN↑ under the single disclosed META bridge `AxBenevolentBearingObtains` (C177, "some person is actually helped"). The bridge is a paid commitment, not a hidden derivation: the bare value layer is machine-proven empty (`no_help_obtains`, C176, `{Subject}`), which is the bridge's own countermodel. The negative pole `Evil` remains a declared SEM datum (its fair reading needs a parallel harm bridge, not declared). What stays a countermodel frontier is the *attribution* of this goodness to the Divine Being — that remains a separate target. — [MoralFrontierAudit.lean#moral_good_obtains](formal/Logos/MoralFrontierAudit.lean#L212), footprint {AxBenevolentBearingObtains, Means, Subject} ; [MoralFrontierAudit.lean#Good](formal/Logos/MoralFrontierAudit.lean#L203), footprint {Means, Subject} ; [MoralFrontierAudit.lean#moral_pole_postulate_is_not_a_consequence](formal/Logos/MoralFrontierAudit.lean#L261), footprint {Initiates, Means, State, Subject} ; [Value.lean#AxBenevolentBearingObtains](formal/Logos/Value.lean#L183), footprint {AxBenevolentBearingObtains, Means, Subject} ; [Value.lean#no_help_obtains](formal/Logos/Value.lean#L110), footprint {Subject} |
| **Eternal — ever-present** (everlasting existence) | Divine Being / Ground | ✅ PROVEN | World-rigid existence is unmodulated by time: `NecessaryEntity e → Everlasting e` (`∀ t, ExistsAtTime t e`) is a definitional corollary of necessity via the Nat-stage layer — the deduction imports NO temporal premise, time enters only on the conclusion side. `Everlasting Entity.ofGround` is therefore PROVEN (`{Subject}` + ground footprint, VOCAB). Distinct from the eternal love-*relation* `T14_eternalRelation_conditional`. C181 supplies the generic empty-footprint necessity-to-stage transport, but deliberately does not instantiate the canonical `Entity` sort. — [NecessityEternity.lean#the_ground_everlasting](formal/Logos/NecessityEternity.lean#L182), footprint {Subject} ; [NecessityEternity.lean#necessary_implies_everlasting](formal/Logos/NecessityEternity.lean#L167), footprint {Subject} ; [NecessityEternity.lean#necessary_existence_is_stage_uniform](formal/Logos/NecessityEternity.lean#L106), footprint {} ; [NecessityEternity.lean#ofGround_necessary](formal/Logos/NecessityEternity.lean#L132), footprint {Subject} ; [Love.lean#T14_eternalRelation_conditional](formal/Logos/Love.lean#L105), footprint {AxTwoSubjects, Means, Subject} |
| **Atemporal** (existence not time-modulated; outside succession) | Divine Being / Ground | ✅ PROVEN | `NecessaryEntity e → Atemporal e` (`ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e`); the ground is also outside every initiation-act (`the_ground_not_in_succession`, `{Initiates, State, Subject}`). Separation is honest: atoms/subjects are time-modulated (`atom_has_temporal_mode`) and `Everlasting` does not collapse into necessity (`everlasting_but_contingent`). What is PROVEN is stage-unmodulated world-rigid existence — not a full theology of divine eternity. C181 makes the underlying transport explicit without instantiating the canonical `Entity` sort. — [NecessityEternity.lean#the_ground_atemporal](formal/Logos/NecessityEternity.lean#L186), footprint {Subject} ; [NecessityEternity.lean#necessary_implies_atemporal](formal/Logos/NecessityEternity.lean#L174), footprint {Subject} ; [NecessityEternity.lean#necessary_existence_is_stage_uniform](formal/Logos/NecessityEternity.lean#L106), footprint {} ; [NecessityEternity.lean#the_ground_not_in_succession](formal/Logos/NecessityEternity.lean#L191), footprint {Initiates, State, Subject} ; [NecessityEternity.lean#atom_has_temporal_mode](formal/Logos/NecessityEternity.lean#L234), footprint {Subject} ; [NecessityEternity.lean#everlasting_but_contingent](formal/Logos/NecessityEternity.lean#L259), footprint {Subject} |
| **Divine simplicity** | Divine Being / Ground | ✅ PROVEN | In `DivineSimplicity.lean` (footprint `{Means, Subject, propext}` — VOCAB + CL), `ofGround_divine_simplicity` proves that `Entity.ofGround` satisfies classical Divine Simplicity under finite subjectivity (`∀ s, ∃ p, ¬ Means s p`): (1) Mereological Non-Compositeness (`NonComposite e ↔ CanonicalAseity e`, no proper grounding parts); (2) Structural Inextension (`ofGround_has_no_internal_components`, atomic nullary constructor with zero internal decomposition); (3) Intentional Simplicity (`ofGround_undivided_meaning`, uniform meaning capacity across all propositions); (4) Ontological Transcendence (`ofGround_transcendent`, distinct from all atomic worldly states and finite subjects). Composite entities provably fail simplicity (`composite_entity_fails_simplicity`, `{}`). Honest boundary: this establishes mereological, structural, and intentional simplicity — not identity of essence and existence. — [DivineSimplicity.lean#ofGround_divine_simplicity](formal/Logos/DivineSimplicity.lean#L179), footprint {Means, Subject, CL} ; [DivineSimplicity.lean#ofGround_has_no_internal_components](formal/Logos/DivineSimplicity.lean#L100), footprint {Subject} ; [DivineSimplicity.lean#ofGround_undivided_meaning](formal/Logos/DivineSimplicity.lean#L118), footprint {Means, Subject} ; [DivineSimplicity.lean#ofGround_transcendent](formal/Logos/DivineSimplicity.lean#L151), footprint {Subject} ; [DivineSimplicity.lean#non_composite_iff_canonical_aseity](formal/Logos/DivineSimplicity.lean#L69), footprint {Means, Subject} ; [DivineSimplicity.lean#composite_entity_fails_simplicity](formal/Logos/DivineSimplicity.lean#L202), footprint {} |
| **Scholastic simplicity** (strict identity of essence and existence) | Divine Being / Ground | ❌ NOT ESTABLISHED | The theory proves mereological, structural, and intentional simplicity (`DivineSimplicity.lean`). The traditional scholastic doctrine asserting the strict identity of essence and existence or collapsing all divine attributes into undifferentiated identity is not derived. |
| **Divine immutability** (ontological, temporal, and process unchangeability) | Divine Being / Ground | ✅ PROVEN | In `DivineImmutability.lean` (footprint `{Initiates, Means, State, Subject}` — VOCAB only), `ofGround_divine_immutability` establishes Classical Divine Immutability (Aquinas *ST* I, q. 9) for `Entity.ofGround`: (1) Modal Invariance (`ofGround_modal_invariance`, `{Subject}`, unchanging existence across all worlds); (2) Stage Invariance (`ofGround_stage_invariance`, `{Subject}`, unchanging existence across all temporal stages); (3) Transition Invariance (`ofGround_transition_invariance`, `{Initiates, State, Subject}`, outside all initiation and state becoming); (4) Capacity Invariance (`ofGround_capacity_invariance`, `{Means, Subject}`, uniform intentional capacity across reality). The Thomistic principle is proven: necessity, atemporality, and non-succession entail immutability. Contingent entities provably fail immutability (`contingent_entity_fails_immutability`, `{}`). Honest boundary: establishes modal, temporal, process, and capacity unchangeability in Γ; does not claim psychological impassibility or constrain relational intentionality. — [DivineImmutability.lean#ofGround_divine_immutability](formal/Logos/DivineImmutability.lean#L151), footprint {Initiates, Means, State, Subject} ; [DivineImmutability.lean#ofGround_modal_invariance](formal/Logos/DivineImmutability.lean#L69), footprint {Subject} ; [DivineImmutability.lean#ofGround_stage_invariance](formal/Logos/DivineImmutability.lean#L88), footprint {Subject} ; [DivineImmutability.lean#ofGround_transition_invariance](formal/Logos/DivineImmutability.lean#L105), footprint {Initiates, State, Subject} ; [DivineImmutability.lean#ofGround_capacity_invariance](formal/Logos/DivineImmutability.lean#L122), footprint {Means, Subject} ; [DivineImmutability.lean#necessity_and_atemporality_yield_immutability](formal/Logos/DivineImmutability.lean#L167), footprint {Initiates, Means, State, Subject} ; [DivineImmutability.lean#contingent_entity_fails_immutability](formal/Logos/DivineImmutability.lean#L187), footprint {} |
| **Psychological impassibility** (incapacity for relational affect or compassion) | Divine Being / Ground | ❌ NOT ESTABLISHED | The ground is immutable in its modal existence, temporal stages, process transitions, and capacity (`DivineImmutability.lean`). Impassibility in the sense of relational indifference or incapacity for compassion is not established; Γ explicitly proves the eternal relationality of love (`T14_eternalRelation_conditional`). — [Love.lean#T14_eternalRelation_conditional](formal/Logos/Love.lean#L105), footprint {AxTwoSubjects, Means, Subject} |
| **Foundational omnipresence** (sustaining presence to all beings across modal reality) | Divine Being / Ground | ✅ PROVEN | In `FoundationalOmnipresence.lean` (footprint `{Means, Subject}` — VOCAB only), `ofGround_foundational_omnipresence` establishes Classical Foundational Omnipresence (Aquinas *ST* I, q. 8) for `Entity.ofGround`: (1) World-Rigid Presence (`ofGround_world_rigid_presence`, `{Subject}`, present across all possible worlds); (2) Universal Modal Grounding (`ofGround_universal_modal_ground`, `{Means, Subject}`, grounds every entity in every possible world); (3) Non-Reciprocal Grounding (`ofGround_non_reciprocal_ground`, `{Means, Subject}`, asymmetric sustenance, ungrounded by atoms or finite subjects); (4) Maximal Intentional Capacity (`ofGround_maximal_capacity`, `{Means, Subject}`, exhaustive meaning capacity). The Thomistic principle is proven: universal modal grounding, presence, and aseity entail omnipresence. Finite entities provably fail universal grounding (`finite_entity_fails_omnipresence`, `{}`). Honest boundary: establishes foundational sustaining presence across modal reality in Γ; explicitly distinguishes foundational omnipresence from physical spatial omnipresence or quantitative metric infinity. — [FoundationalOmnipresence.lean#ofGround_foundational_omnipresence](formal/Logos/FoundationalOmnipresence.lean#L154), footprint {Means, Subject} ; [FoundationalOmnipresence.lean#ofGround_world_rigid_presence](formal/Logos/FoundationalOmnipresence.lean#L88), footprint {Subject} ; [FoundationalOmnipresence.lean#ofGround_universal_modal_ground](formal/Logos/FoundationalOmnipresence.lean#L70), footprint {Means, Subject} ; [FoundationalOmnipresence.lean#ofGround_non_reciprocal_ground](formal/Logos/FoundationalOmnipresence.lean#L108), footprint {Means, Subject} ; [FoundationalOmnipresence.lean#ofGround_maximal_capacity](formal/Logos/FoundationalOmnipresence.lean#L125), footprint {Means, Subject} ; [FoundationalOmnipresence.lean#omnipresence_from_universal_ground_and_aseity](formal/Logos/FoundationalOmnipresence.lean#L170), footprint {Means, Subject} ; [FoundationalOmnipresence.lean#finite_entity_fails_omnipresence](formal/Logos/FoundationalOmnipresence.lean#L190), footprint {} |
| **Physical omnipresence** (spatial presence throughout physical spacetime coordinates) | Divine Being / Ground | ❌ NOT ESTABLISHED | Spatial extension and physical spacetime coordinates are absent from the primitive ontology of Γ. The ground is omnipresent foundationally (sustaining all beings across all possible worlds, `FoundationalOmnipresence.lean`), not by physical diffusion or spatial location. |
| **Quantitative metric infinity** (infinite physical magnitude or cardinal size) | Divine Being / Ground | ❌ NOT ESTABLISHED | The foundation is universal in foundational scope (grounding all reality, `FoundationalOmnipresence.lean`), but quantitative metric infinity (spatial magnitude or cardinal size) is not derived and is explicitly disclaimed (`CHARACTERISTICS.md` §11; `CHARS.md` §11). |
| **Omniscience** | Divine Being / Ground | ❌ NOT ESTABLISHED | `Omniscience_AllTruths` / `Omniscience_Counterfactuals` (`DeepModalFrontier`) are frontier vocabulary definitions, not theorems. — [DeepModalFrontier.lean#Omniscience_AllTruths](formal/Logos/DeepModalFrontier.lean#L313), footprint {} ; [DeepModalFrontier.lean#Omniscience_Counterfactuals](formal/Logos/DeepModalFrontier.lean#L317), footprint {} |
| **Omnipotence** | Divine Being / Ground | ❌ NOT ESTABLISHED | No live theorem. |
| **Creator of contingent reality** | Divine Being / Ground | 🧱 INDEPENDENT | `necessary_ground ⇏ contingent_creation` (Acosmic model, footprint `{}`): a necessary divine ground is consistent with zero contingent created reality. (Ledger target F9 DEFERRED.) — [ConditionalTheology.lean#necessary_ground_not_entails_contingent_creation](formal/Logos/ConditionalTheology.lean#L420), footprint {} |
| **Three Divine Persons (Trinity)** | Divine Personhood | 🧱 INDEPENDENT | `preceding_theory ⇏ trinity` (Binitarian separation model, footprint `{}`). A separate claim, distinct from necessity and from unity. (F6/F8 DEFERRED; plurality `T12_twoPersons` is at most generic persons under `AxTwoSubjects`.) — [ConditionalTheology.lean#preceding_theory_not_entails_trinity](formal/Logos/ConditionalTheology.lean#L336), footprint {} |
| **Incarnation** | Divine Personhood | 🧱 INDEPENDENT | `preceding_theory ⇏ incarnation` (Unincarnate model, footprint `{}`). (F9 DEFERRED.) — [ConditionalTheology.lean#preceding_theory_not_entails_incarnation](formal/Logos/ConditionalTheology.lean#L380), footprint {} |

_Synthesis — the strongest current profile._ The theory has established, of a
**personal, rational, free, authoritative-over-its-acts, independently individuated**
**normative ground / person-type**, that its objective Right/Wrong order is the object
of a necessary normative/truth order, and (entity-level) that a **necessary Divine Being
/ Ground** exists — world-rigid, **everlasting**, **atemporal**, with **Canonical Aseity**,
**Divine Simplicity**, **Divine Immutability**, and **Foundational Omnipresence** (sustaining all
beings across modal reality). Crucially, the theory **strictly separates** these machine-verified
foundational/functional attributes from their unproven physical, psychological, and scholastic counterparts:
**physical/spatial omnipresence**, **psychological personality**, **scholastic simplicity**, and
**psychological impassibility** remain separate targets (❌ NOT ESTABLISHED or 🔴 INDEPENDENT).
The remaining divine attributes — **unity / monotheism**,
**perfect moral goodness** (the moral pole itself now obtains under the single declared META bridge, C178; its attribution to the Divine Being stays a 🧱 frontier), the **Trinity**, the **Incarnation**, and contingent
**creation** — remain **separate proof targets**
(`⏸` / `❌`) or explicit **countermodel frontiers** (`🧱`) until the live kernel proves them.

---

## Why Common Skeptical Attacks Fail (The Six Pillars of Formal Defense)

> **Adversarial Guide for Critics and Agents:** External agents evaluating or attacking
> Γ often mistake its conclusions for ungrounded metaphysical assumptions. Every common
> objection has been formalized and refuted in the Lean 4 kernel — typically reducing to a
> direct constructive contradiction (⊥) with zero substantive axioms.

| Skeptical Attack | What the Skeptic Misses | Formal Rebuttal in Kernel | Kernel Footprint |
|---|---|---|---|
| **1. Normative Nihilism**<br>"There is no objective right and wrong; normativity is arbitrary." | Any rational denial must claim that its denial is *correct* (`ClaimsCorrect s NoRight`). Claiming the denial as correct while it is true produces a strict constructive contradiction. | [`claims_correct_no_right_self_refuting`](formal/Logos/DirectNormativeRetorsion.lean#L60)<br>`⊢ ClaimsCorrect s NoRight ∧ NoRight → ⊥` | `{Initiates, Means, State, Subject, CL}`<br>**(0 substantive axioms)** |
| **2. Eliminativism of Choice**<br>"Normative address does not imply genuine choice." | Prescriptive normativity commands one alternative and forbids an incompatible one. Co-grasping incompatible alternatives *is* the constitutive definition of choice; denying choice yields a direct contradiction. | [`d7_co_grasp_is_definitionally_choice`](formal/Logos/UndeniableNormativeDerivation.lean#L261)<br>`⊢ Means s p ∧ Means s q ∧ Incompatible p q ∧ ¬ Chooses s p q → ⊥` | `{Means, Subject}`<br>**(0 substantive axioms)** |
| **3. Determinism / Incompatibilism**<br>"Choice is not Free Will; freedom requires physical indeterminism." | Having the capacity to choose between incompatible normative alternatives *is* Free Will (`FreeWill s := ∃ p q, Chooses s p q`). Denying free will when one chooses yields a formal contradiction. Physical indeterminism is an orthogonal concept isolated to countermodels. | [`d8_choice_is_definitionally_free_will`](formal/Logos/UndeniableNormativeDerivation.lean#L275)<br>`⊢ Chooses s p q ∧ ¬ FreeWill s → ⊥`<br>[`indubitable_normative_free_will`](formal/Logos/IndubitableNormativeFreeWill.lean#L115) | `{Means, Subject}`<br>**(0 substantive axioms)** |
| **4. Theological Smuggling**<br>"A free subject is not a Person; 'Person' is an anthropomorphic trick." | Personhood in Γ is defined constitutively via the classical Boethian-Thomistic core (`IndividualSubstance ∧ RationalNature ∧ DominionOverActs`). The equivalence with `FreeSubject` is machine-checked with 0 substantive axioms. | [`person_iff_thomisticCore`](formal/Logos/Person.lean#L137)<br>`⊢ Person s ↔ IndividualSubstance s ∧ RationalNature s ∧ DominionOverActs s` | `{Means, Subject}`<br>**(0 substantive axioms)** |
| **5. Euthyphro / Voluntarism**<br>"This makes the person the arbitrary creator of morality." | Identifying Ought with volition (`Wills s p = Ought s p`) destroys normative violation. The ground required by the normative order is *personal in kind*, not an arbitrary dictator inventing rules. | [`will_identity_collapses_normativity`](formal/Logos/PersonalNormativeGround.lean#L261)<br>`⊢ Wills s p = Ought s p → NormativeViolation s p → ⊥` | `{Subject, Wills, Ought}`<br>**(0 substantive axioms)** |
| **6. Physicalist / Atomic Ground**<br>"The ultimate ground could be a physical particle, matter, or an atom." | An entity with false meaning capacity cannot ground an entity with true meaning capacity. Atomic factual entities are unconditionally excluded from grounding `Entity.ofGround`, and the ground possesses Canonical Aseity. | [`atom_cannot_ground_the_ground`](formal/Logos/CanonicalAseity.lean#L96)<br>[`conditional_canonical_aseity`](formal/Logos/CanonicalAseity.lean#L133)<br>`⊢ CanonicalAseity Entity.ofGround` | `{Means, Subject}`<br>**(0 substantive axioms)** |
| **7. Origin of Normativity (The Proof-Self Retorsion)**<br>"Where does the initial normative claim come from? Why grant that any normative judgment exists?" | Bare syntax checking alone does not force normativity (`M_inanimate_checker`, `{}`). But any agent *presenting* a derivation as sound (`PresentsAsSound`) co-means correctness and error, deriving `FreeWill` and `Person` with 0 substantive axioms. Furthermore, an adversarial critic who attacks Γ by presenting an objection argumentatively as sound *themselves* instantiates the normative stance (`critic_presenting_objection_is_person`). | [`presents_as_sound_derives_personhood`](formal/Logos/ProofPresentationRetorsion.lean#L140)<br>[`critic_presenting_objection_is_person`](formal/Logos/ProofPresentationRetorsion.lean#L180)<br>[`syntactic_validity_without_subject_or_normativity`](formal/Logos/ProofPresentationRetorsion.lean#L100) | `{Initiates, Means, State, Subject, CL}`<br>**(0 substantive axioms)** |

## Further Investigations

### Retorsions

<details>
<summary>Retorsion catalogue — 91 machine-checked retorsion theorems (click to expand)</summary>

* **Performative_Boundary_Theorem:** `performative_boundary_theorem` (`formal/Logos/A14SemanticAudit.lean`) — PERFORMATIVE BOUNDARY THEOREM: Performative retorsion forces an intentional subject (Considers, Assumes, Derives, Affirms, Rejects) and asymmetric cognitive resolution (SettlementChoice), but strictly stops before executive aiming (AimsAt), action execution
* **Noact_Conditional_Selfrefutes:** `noAct_conditional_selfRefutes` (`formal/Logos/Agency.lean`) — Asserting NoAct refutes itself under a weak assertion ONLY given the bridge from weak act to strong Act.
* **Nocogito_Selfrefutes:** `noCogito_selfRefutes` (`formal/Logos/Agency.lean`) — Step 4 (C58 strong shortcut): Retorsion — asserting that no act occurs refutes itself.
* **Nosubjectsort_Selfrefutes:** `noSubjectSort_selfRefutes` (`formal/Logos/Agency.lean`) — Denying the domain of discourse refutes itself whenever a speaker asserts it.
* **Nosubject_Performative_Selfrefutes:** `noSubject_performative_selfRefutes` (`formal/Logos/Agency.lean`) — C57: Retorsion — asserting that no subject exists refutes itself.
* **Nosubject_Selfrefutes:** `noSubject_selfRefutes` (`formal/Logos/Agency.lean`) — C57 canonical theorem name in Agency.
* **Noweakact_Selfrefutes:** `noWeakAct_selfRefutes` (`formal/Logos/Agency.lean`) — Step 4 (weak retorsion): Asserting that no performed event occurs refutes itself directly.
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
* [Contingent Creation and Teleology](investigations/creation.md) — CONTINGENT FACT / METAPHYSICAL BRIDGE / ACOSMIC MODEL
* [Personal Agency and the Rejection of Impersonalism](investigations/divine-personhood.md) — THEOREMS OF CONSTITUTIVE PERSONAL AGENCY (`{Initiates, Means, State, Subject, CL}`, 0 Substantive Axioms)
* [The Normative Route to Free Will](investigations/free-will.md) — LOGICAL derivation from CONSTITUTIVE SEMANTICS (`{Means, Subject}`, 0 substantive axioms)
* [Constructive Personal Ground of Normativity and Reality](investigations/grounding.md) — THEOREMS T7 & T8 (0 Substantive Axioms / Minimal Classical Logic)
* [The Incarnation — The Builder Entering the House](investigations/incarnation.md) — DEFERRED THEOLOGICAL BRIDGE / UNINCARNATE MODEL (`{}`)
* [Plurality of Divine Persons and Eternal Love](investigations/plurality-and-love.md) — THEOREMS T12, T13, T14 (`{Means, Subject, AxTwoSubjects}`)
* [The Trinity and the Condilectus Principle](investigations/trinity.md) — DEFERRED THEOLOGICAL BRIDGE / BINITARIAN SEPARATION MODEL (`{}`)

### Technical

* [Technical Appendix: Kernel Audit, Consistency & Code Annex](investigations/kernel-audit.md) — Complete kernel audit, transitive axiom footprints, dependency ledger, and consistency checks.
* [Formal Dependency Graph (JSON)](formal/depgraph.json) / [(DOT)](formal/depgraph.dot) — LeanDepViz transitive kernel dependency DAG.
* [Theorem Ledger (GAPMAP)](formal/GAPMAP.md) — Formal correspondence mapping across formal and prose corpora.
