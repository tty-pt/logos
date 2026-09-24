# Γ — The Deduction

> **Γ is a machine-checked deduction**: genuine normativity — an objective right/wrong
> binding our judgments — forces a *personal* ground. Free will is *derived, never
> assumed* (`GenuineNormativity ⇒ Chooses ⇒ FreeWill ⇒ FreeSubject ⇒ Person`);
> wherever right/wrong is real, its ground-type is personal (`RightWrong ⇒ Person`).
> A necessary Divine Being/Ground — eternal (everlasting and atemporal) — is **proven** (✅); Divine Personhood and monotheism are **deferred** (⏸); every other claim is
> definitional, derived, or a declared axiom.

Every section below answers the same question — *what is the status of this claim?*

> **The arc in one breath** — try to deny any step of the cascade. Either the denial
> refutes itself (a *retorsion*: denying Right/Wrong, Ought, or genuine
> normativity while relying on it), or the claim is definitional, or it is a
> freely-chosen axiom whose footprint is declared out loud, or it simply is not
> claimed at all (a *countermodel frontier*, marked `⇏`).

**Two directions, not one.** The chart distinguishes *epistemic discovery* (▲ — what
the argument must prove upward: no free subject precedes free will) from *ontological
grounding* (▼ — what the established order then entails downward: a personal free
agency grounds Right/Wrong). The kernel proves the one dependence
`RightWrong ⇒ Person`; the downward `▼` ontological-grounding arrow is the
interpretive reading of that same proved subjunction, not an additional theorem —
the direction is not machine-decidable.

> **What this proof does and does not show**
>
> 1. The machine-verified chain above — clean, established **under** the
>    normative-judicative stance — the self-given performative datum (irrefutable in
>    the act of denying it), validated by the retorsion with 0 substantive axioms.
>    Zero-input free will is *not* claimed — §3 states the boundary and the machine
>    witnesses.
> 2. That same dependence — *wherever the normative order is real, its ground-type
>    is personal* — is machine-proved with 0 substantive axioms. Reading the
>    subjunction as a direction of ontology is interpretive, as 'Two directions, not
>    one.' above explains.
> 3. Divine Personhood and Strict Monotheism — **DEFERRED** (⏸), not proved here; a necessary
>    Divine Being/Ground (world-rigid, everlasting, atemporal) is its entity-level **PROVEN** claim (✅).
> 4. Moral good/evil — machine-separated from epistemic normativity (countermodel 
>    frontier 🧱, C175): the faithful model `M_amoral` satisfies the whole epistemic 
>    agential reality-hook with zero practical obligation; a positive close requires 
>    a declared moral datum (price sheet §5.4). The epistemic reality-hook itself is 
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
        │
        │ [discovery · PURE LOGIC · 0 substantive axioms]
        ▼
FREE WILL
  Freedom is derived by pure logic from genuine normativity and choice.
  ⊢ Chooses s p q ∧ FreeWill(s)
  *[✅]*
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

Terminology: 'Right'/'Wrong' here denote the objective truth/correctness polarity — a proposition's being true (so that affirming it is correct) vs. being false (so that affirming it is incorrect) — not a moral evaluation of good vs. evil (moral good/evil is machine-separated from epistemic normativity: countermodel frontier 🧱, C175; a positive bridge would cost the declared SEM poles Good/Evil, price sheet §5.4). The extensional distinction (¬N_T ∧ ¬N_F) and the agential stance-conditional form RightWrong s (bridge open, M_inanimate C167) are two distinct formal objects.

*(Detailed technical proof & model analysis: [investigations/right-and-wrong.md](investigations/right-and-wrong.md))*

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** Deny Right/Wrong at all — adopt NoRight, claiming 'there is no correct standard' as if that were itself correct.
> **The reply / the frontier —** Retorsive: claiming the denial as *correct* while it is true is a constructive contradiction (claims_correct_no_right_self_refuting); downplaying to a mere assertion forfeits the claim to correctness. Under classical meta-logic {CL} objective Right necessarily exists — with zero substantive axioms.
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

The Established Right/Wrong Distinction: The binary normative distinction is real.

    ∴ EstablishedRightWrong ≡ ¬N_T ∧ ¬N_F

📘 · [IndubitableNormativeFreeWill.lean#EstablishedRightWrong](formal/Logos/IndubitableNormativeFreeWill.lean#L53)

### Retorsive Defense Against Skeptical Denial

The attempted denial of objective Right and Wrong (NoRight := ¬NormativeRightExists) refutes itself performatively. Claiming the denial as correct (ClaimsCorrect s NoRight) while the denial is true produces a strict constructive contradiction (claims_correct_no_right_self_refuting). Classical double-negation elimination (Classical.not_not, footprint {CL}) derives that objective Right necessarily exists (performative_normative_denial_establishes_normative_right).

The Fundamental Diagonal Retorsion Theorem: Claiming NoRight as correct while NoRight is true produces a strict, constructive contradiction.

    ClaimsCorrect(s, NoRight) ∧ NoRight → ⊥

✅ · [DirectNormativeRetorsion.lean#claims_correct_no_right_self_refuting](formal/Logos/DirectNormativeRetorsion.lean#L60)

Unassertability Theorem: No agent can claim NoRight as correct if NoRight is true.

    ∴ ¬∃ s, ClaimsCorrect(s, NoRight) ∧ NoRight

✅ · [DirectNormativeRetorsion.lean#cannot_claim_correct_no_right_and_true](formal/Logos/DirectNormativeRetorsion.lean#L70)

Performative Derivation Theorem: If any agent actually performs a normative correctness claim on NoRight, the thesis NoRight is strictly false.

    ∃ s, ClaimsCorrect(s, NoRight) → ¬NoRight

✅ · [DirectNormativeRetorsion.lean#performative_normative_denial_establishes_normative_right](formal/Logos/DirectNormativeRetorsion.lean#L79)

---

## 2. Ought and Normative Polarity

From objective Right and Wrong, the normative standard is expressed as agential Ought and Ought-Not. Under the objective epistemic TruthNorm, correct judgment implies what the subject ought to affirm, and incorrect judgment implies what the subject ought not to affirm. Correctness and incorrectness constitute a strict deontic opposition between what ought and what ought not to be judged.

Terminology: the Ought/Ought-Not here are derived from the epistemic TruthNorm — they govern whether a judgment about reality is correct to affirm (true) or incorrect (false). They are not the irreducible practical deontic Ought of actions (`OughtRetorsion.Ought`, a separate VOCAB primitive).

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** 'Ought' is nothing but a relabel of 'correct' — no genuinely normative force is added.
> **The reply / the frontier —** The deontic opposition here is derived under the objective epistemic TruthNorm (correct → ought to affirm; incorrect → ought not to affirm) — a genuinely new normative relation, not a relabel; the irreducible practical Ought of actions stays a separate primitive (see the terminology note above).
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

---

## 3. Genuine Choice

Step glossary, aligned with the definitions. THE core: `Chooses s p q` (co-meaning) — the agent cognitively grasps both incompatible contents in thought; it is the vocabulary level at which freedom is defined (`FreeWill s := ∃ p q, Chooses s p q`, definitional). Commitment ('committing to one') is NOT inside `Chooses`: a contemplative subject who co-means without settling still satisfies it (`contemplatesWithoutSettling_implies_freeWill`). Settlement is carried by the normative-judicative stance, whose bundle is the new definition `CommittedChoice s p q r := Act s p ∧ Chooses s q r` — the stance instantiates it on the judicative poles with zero substantive axioms (`claims_normative_correctness_implies_committed_choice`, footprint {Initiates, Means, State, Subject, CL}). Boundaries: weak choice = choice field (representability only, `ChoiceField`); contemplative co-meaning does count as `Chooses`/`FreeWill` (the honest boundary); real deliberation (`Selects`/`DeliberateChoice`) demands the truth-laden assertion and is not forced; the libertarian-grade notions (`StrongChooses`, `GenuineChooses`) remain the incompatibilist frontier, available only under the constitutive deontic semantics (conditional T6/T7). Executive selection (`Selects`/`Choice`/`FreeAgency`) is separated from the deliberative `Chooses` line with no bridge axioms (`M_det`, `ExecutiveDeliberativeFrontier` Track A–H): committing bundles settlement via the `Act` conjunct but derives no executive causation or sourcehood, while `ContemplatesWithoutSettling` still implies `FreeWill`.

*(Detailed technical proof & model analysis: [investigations/contrastive-choice.md](investigations/contrastive-choice.md))*

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** Genuine Normativity is a stipulation — the chain GN → Chooses → FreeWill may be valid but empty.
> **The reply / the frontier —** Retorsive: claiming the denial of genuine normativity as correct (ClaimsCorrect s NoGN) yields a literal term of the identical GenuineNormativity structure (denial_of_genuine_normativity_is_self_refuting); the axiom-free stance-level derivation is set out in the retorsion block below.
</details>

<details>
<summary>Definitions used in this section (14; 10 new, 4 already shown)</summary>

`Act s p`: strong act: meaningful initiation of movement.

    ∴ Act ≡ Means(s, p) ∧ ∃ w, w', Initiates s w w' p

📘 · [Agency.lean#Act](formal/Logos/Agency.lean#L155)

Committed choice: the subject is committed to p (performs the act on p) while co-meaning the incompatible alternatives q and r in thought.

    ∴ CommittedChoice ≡ Act s p ∧ Chooses(s, q, r)

📘 · [NormativeOrder.lean#CommittedChoice](formal/Logos/NormativeOrder.lean#L236)

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

📘 · [MoralFrontierAudit.lean#Means](formal/Logos/MoralFrontierAudit.lean#L64)

The skeptical denial proposition: There is no genuine normativity anywhere.

    ∴ NoGN ≡ ¬GenuineNormativityExists

📘 · [RetorsiveNormativity.lean#NoGN](formal/Logos/RetorsiveNormativity.lean#L123)

Voice: act plus grasp of the positive pole `Correct s p` — nothing more; this is all `ClaimsCorrect` gives in Γ.

    ∴ VoiceSig ≡ JudSigAct(sig, s, p) ∧ sig.Means(s, JudSigCorrect(sig, s, p))

📘 · [BipolarityRetorsion.lean#VoiceSig](formal/Logos/BipolarityRetorsion.lean#L272)

    ∴ Correct ≡ A(s, p) ∧ T(p) — defined in §2. Ought and Normative Polarity.

    ∴ Incorrect ≡ A(s, p) ∧ IsFalse(p) — defined in §2. Ought and Normative Polarity.

    ∴ N_F ≡ ∀ p, T(p) — defined in §1. Objective Right and Wrong.

    ∴ N_T ≡ ∀ p, ¬T(p) — defined in §1. Objective Right and Wrong.

</details>

Deliberate choice entails genuine choice in the co-meaning sense.

    DeliberateChoice(s, p, q) → Chooses(s, p, q)

✅ · [Choice.lean#deliberateChoice_implies_chooses](formal/Logos/Choice.lean#L446)

<details>
<summary>Supporting Infrastructure — 2 auxiliary theorem(s) beneath this step</summary>

`Chooses s p q`: strong choice: the subject co-means incompatible alternatives.

    ∴ Chooses ≡ Means(s, p) ∧ Means(s, q) ∧ Incompatible(p, q)

📘 · [Choice.lean#Chooses](formal/Logos/Choice.lean#L102)

Every proposition is incompatible with its own negation.

    ∴ Incompatible(p, ¬p)

✅ · [Choice.lean#incompatible_self_negation](formal/Logos/Choice.lean#L110)

</details>

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

Free-will corollary: the combined result `(¬ NoGN) ∧ (∃ s, FreeWill s)` falls out by pure logic — the stance yields GenuineNormativity (refuting NoGN), and co-grasp of incompatible alternatives is definitionally choice, which is definitionally free will (`d8_choice_is_definitionally_free_will`).

    ∃ s, p, ClaimsNormativeCorrectness(s, p) → (¬NoGN) ∧ (∃ s, FreeWill(s))

✅ · [RetorsiveNormativity.lean#attack_inviable_without_axioms](formal/Logos/RetorsiveNormativity.lean#L309)

**Independence witnesses — what the retorsion does NOT force:**

In primitive Γ, voicing a judgment does NOT force the normative-judicative stance: M_oneway voices `True` as correct (act plus grasp of the positive pole) while failing to mean `Incorrect () True` — machine witness of the voice↔stance gap.

    ∴ ∃ sig, s, p, VoiceSig(sig, s, p) ∧ ¬sig.Means(s, JudSigIncorrect(sig, s, p))

✅ · [BipolarityRetorsion.lean#voice_without_normative_stance](formal/Logos/BipolarityRetorsion.lean#L319)

Direct witness (`M_inanimate`): an inanimate universe is extensionally bivalent (`¬N_T ∧ ¬N_F`) yet realizes NO instance of the genuine-normativity shape — incompatible alternatives plus agential address via a means relation.

    ∴ ∃ U, MeansRel, (¬N_T ∧ ¬N_F) ∧ ¬∃ s,(p q : Prop), Incompatible(p, q) ∧ p ≠ q ∧ MeansRel s p ∧ MeansRel s q

✅ · [UndeniableNormativeDerivation.lean#inanimate_universe_satisfies_bivalence_and_no_genuine_normativity](formal/Logos/UndeniableNormativeDerivation.lean#L93)

### Committed Choice — the stance carries settlement (2026-09-24)

The reader-facing gloss 'apprehending incompatible alternatives and committing to one' had no defendant: `Chooses` is only the cognitive co-meaning core, and a purely contemplative subject satisfies it. The strengthening locates commitment in the existing normative-judicative stance: `ClaimsNormativeCorrectness s p` performs the judgment act on p (the commitment) AND co-means the incompatible judicative poles `Correct s p` / `Incorrect s p` (the grasp). That bundle, defined as `CommittedChoice`, entails `Chooses`, `FreeWill`, and `FreeSubject` at the unchanged footprint {Initiates, Means, State, Subject, CL} — zero substantive axioms, no added hypotheses. `ClaimsNormativeCorrectness` itself is **defined** (`NormativeOrder.lean`), not assumed: instantiating it by grasping the negative pole is the performative datum, and a bare voice that never co-means `Incorrect` does not force it (`M_oneway`, C166).

**Stance instantiates CommittedChoice — zero substantive axioms (footprint {Initiates, Means, State, Subject, CL}):**

The normative judicative stance is, by construction, a committed choice: the stance performs the judgment act on p (commitment) and co-means the two judicative normative poles `Correct s p` and `Incorrect s p` (grasp), which are incompatible.

    ClaimsNormativeCorrectness(s, p) → CommittedChoice s p (Correct(s, p)) (Incorrect(s, p))

✅ · [NormativeOrder.lean#claims_normative_correctness_implies_committed_choice](formal/Logos/NormativeOrder.lean#L269)

Master committed-choice theorem from the stance: committed choice, co-meaning, and free will all hold of the judicative stance at the unchanged footprint.

    ClaimsNormativeCorrectness(s, p) → CommittedChoice s p (Correct(s, p)) (Incorrect(s, p)) ∧ Chooses(s, Correct(s, p), Incorrect(s, p)) ∧ FreeWill(s)

✅ · [NormativeOrder.lean#claims_normative_correctness_derives_committed_free_will](formal/Logos/NormativeOrder.lean#L277)

Whenever a normative judicative stance exists (any Act-judged content claimed correct against a prohibited alternative), committed choice exists.

    ∃ s, p, ClaimsNormativeCorrectness(s, p) → ∃ s,(p q r : Prop), CommittedChoice s p q r

✅ · [NormativeOrder.lean#committed_choice_exists_of_stance](formal/Logos/NormativeOrder.lean#L287)

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

Committed choice entails free subjectivity, definitionally (`FreeSubject s := FreeWill s`).

    CommittedChoice s p q r → FreeSubject(s)

✅ · [NormativeOrder.lean#committedChoice_implies_freeSubject](formal/Logos/NormativeOrder.lean#L259)

---

## 4. Free Will

We did not assume a free subject. Free Will is derived, not assumed: from the reality of genuine normative address and rational choice, Free Will follows from Genuine Normativity by pure logic with zero substantive axioms — a subject endowed with the capacity to choose between incompatible alternatives possesses Free Will by definition.

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** You assumed freedom — a free will was smuggled in as a premise.
> **The reply / the frontier —** No — the starting point is normative address, not a free subject: see the derivation in the section text (`indubitable_normative_free_will`).
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
<summary>Supporting Infrastructure — 1 auxiliary theorem(s) beneath this step</summary>

Freedom exists as soon as a genuine choice witness is supplied. This is the formal shape of the target `freeWillExists`; it is *conditional* because the unconditional witness is exactly the blocked `rejectedHornCoMeant`.

    ∃ s, p, q, Chooses(s, p, q) → ∃ s, FreeWill(s)

✅ · [Choice.lean#freeWillExists_of_chooses](formal/Logos/Choice.lean#L206)

</details>

---

## 5. The Free Subject

A subject is definitionally a free subject iff it possesses free will (`FreeSubject(s) ↔ FreeWill(s)`, Iff.rfl). The recognition runs strictly forward: free will first, the free subject only after it.

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** A definitional manoeuvre — the free subject is bought by a definition, not proven.
> **The reply / the frontier —** Precisely — the 'manoeuvre' *is* the theorem: the equivalence is `Iff.rfl`, which is exactly why nothing can precede free will.
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
<summary>Supporting Infrastructure — 1 auxiliary theorem(s) beneath this step</summary>

Genuine choice entails a free subject — by definition.

    Chooses(s, p, q) → FreeSubject(s)

✅ · [Choice.lean#chooses_implies_freeSubject](formal/Logos/Choice.lean#L187)

</details>

---

## 6. Person

In the unified Γ ontology, Personhood is defined constitutively in the classical sense of Boethius and Aquinas — an *individual substance of a rational nature*, with *dominion over its own acts* — formalized as a subject possessing genuine free will (`Person(s) := FreeSubject(s)`); the equivalence with the explicit Thomistic person core (`IndividualSubstance ∧ RationalNature ∧ DominionOverActs`) is proved below (`person_iff_thomisticCore`, 0 substantive axioms). Personhood is therefore not an opaque or unprovable predicate: every Free Subject is an authoritative Person by pure deduction (`free_subject_is_person`). This is the first point at which the personal subject properly enters the main deduction.

*(Detailed technical proof & model analysis: [investigations/divine-personhood.md](investigations/divine-personhood.md))*

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** A loaded, theological word smuggled into the deduction.
> **The reply / the frontier —** Classical, not novel: the term follows Boethius and Aquinas rather than theological invention. Nothing theological is *assumed*; theology would enter only downstream, in the branches — and is then explicitly bounded by countermodels.
</details>

<details>
<summary>Definitions used in this section (4; 2 new, 2 already shown)</summary>

Person: a subject possessing a numerically distinct free will.

    ∴ Person ≡ FreeSubject(s)

📘 · [Person.lean#Person](formal/Logos/Person.lean#L29)

Thomistic person core: the Boethius–Aquinas conditions of personhood — "individual substance of a rational nature" possessed of dominion over its own acts — formalized through their operative distinguishing features.

    ∴ ThomisticPersonCore ≡ IndividualSubstance(s) ∧ RationalNature(s) ∧ DominionOverActs(s)

📘 · [Person.lean#ThomisticPersonCore](formal/Logos/Person.lean#L83)

    ∴ FreeSubject ≡ FreeWill(s) — defined in §3. Genuine Choice.

    ∴ FreeWill ≡ ∃ p, q, Chooses(s, p, q) — defined in §3. Genuine Choice.

</details>

Master Theorem: Every Free Subject is a Person.

    FreeSubject(s) → Person(s)

✅ · [Person.lean#free_subject_is_person](formal/Logos/Person.lean#L33)

Master Correspondence: Personhood is constitutively equivalent to the Thomistic person core.

    ∴ Person(s) ↔ ThomisticPersonCore(s)

✅ · [Person.lean#person_iff_thomisticCore](formal/Logos/Person.lean#L137)

<details>
<summary>Supporting Infrastructure — 2 auxiliary theorem(s) beneath this step</summary>

Master Equivalence: Personhood is constitutively equivalent to Free Subjecthood.

    ∴ Person(s) ↔ FreeSubject(s)

✅ · [Person.lean#person_iff_freeSubject](formal/Logos/Person.lean#L38)

Every Person possesses Free Will.

    Person(s) → FreeWill(s)

✅ · [Person.lean#person_has_free_will](formal/Logos/Person.lean#L48)

</details>

---

## 7. Personal and Independent Will

We distinguish carefully between: (1) the subject possessing a Will; (2) the faculty of will (subjectWill s); (3) the act of willing (Wills s p); and (4) the capacity of free choice (FreeWill s). By the principle of numerical individuation (will_individuation), distinct subjects possess numerically distinct faculties of will (subjectWill s₁ ≠ subjectWill s₂). A Person is constitutively a subject with a free will that is genuinely its own, not numerically identical with another subject's will (Person(s) ↔ FreeIndependentWill(s), 0 substantive axioms). The postulate status is machine-witnessed: `will_individuation` is not derivable from the pre-will spine — the hostile model `Subject := Bool`, `Will := Unit`, `subjectWill := fun _ => ()` satisfies the spine yet the law refutes there (`WillIndividuationAudit.will_individuation_not_forced_by_prewill_spine`, `{}`).

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** Two persons could share one will — individuation is not forced.
> **The reply / the frontier —** Individuation is a constitutive meaning-postulate, not a derived construction: `will_individuation` (A18, VOCAB — a **declared** injectivity law `subjectWill s₁ ≠ subjectWill s₂`, not a theorem) assigns each subject its own numerically distinct will-faculty, so two Persons cannot share one will; given that postulate, `Person ↔ FreeIndependentWill` follows with 0 substantive axioms. Its status as a declared postulate — not a theorem — is **kernel-verified**: the hostile model `Subject := Bool`, `Will := Unit`, `subjectWill := fun _ => ()` satisfies the pre-will spine (performative act included), and there the law **arrives at a contradiction** — forcing injectivity demands `subjectWill true ≠ subjectWill false` while both wills are `()`; spine+law is inconsistent, spine alone satisfiable ⇒ the law cannot be derived (`WillIndividuationAudit.will_individuation_not_forced_by_prewill_spine`, footprint `{}`).
</details>

<details>
<summary>Definitions used in this section (4; 2 new, 2 already shown)</summary>

Free, Independent Will: a subject endowed with both the capacity of free choice (`FreeWill s`) and an independently individuated volitional faculty (`IndependentWill s`).

    ∴ FreeIndependentWill ≡ FreeWill(s) ∧ IndependentWill(s)

📘 · [Person.lean#FreeIndependentWill](formal/Logos/Person.lean#L59)

Independent Will: the faculty of will possessed by subject s is uniquely its own, numerically distinct from the will of any distinct subject.

    ∴ IndependentWill ≡ ∀ s', s' ≠ s → subjectWill(s') ≠ subjectWill(s)

📘 · [Person.lean#IndependentWill](formal/Logos/Person.lean#L54)

    ∴ Person ≡ FreeSubject(s) — defined in §6. Person.

    ∴ ThomisticPersonCore ≡ IndividualSubstance(s) ∧ RationalNature(s) ∧ DominionOverActs(s) — defined in §6. Person.

</details>

Master Equivalence: Personhood is constitutively equivalent to Free, Independent Will.

    ∴ Person(s) ↔ FreeIndependentWill(s)

✅ · [Person.lean#person_iff_freeIndependentWill](formal/Logos/Person.lean#L117)

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

</details>

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

    ∴ Person ≡ FreeSubject(s) — defined in §6. Person.

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

The Non-Reversal Architectural Principle: 1. Deductive Discovery runs forward: RightWrongAt s p q ⇒ ... ⇒ Person s ⇒ GroundsRightWrong s.

    ∴ (RightWrongAt(s, p, q) → Person(s) ∧ GroundsRightWrong s) ∧ (Person(s) → GroundsRightWrong s)

✅ · [PersonalNormativeGround.lean#non_reversal_discovery_and_grounding](formal/Logos/PersonalNormativeGround.lean#L515)

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

</details>

---

## 9. Necessary Truth

After normative reality and its personal grounding have been established, §9 reaches Necessary Truth (∃ τ, □ τ) as the *logical* continuation of the objective logical order — `Semantics.strongTruthExists` (C59, `{CL}`), the classical meta-logic resident in Core/Semantics. This world-level modality is NOT derived from the normative chain: the normative world-level continuation is the separate, stronger claim `NecessaryNormativeOrder : ∀ w, NormativeOrderAt w` (anchored in `Core.rightWrongDistinction`), and no theorem states `NecessaryNormativeOrder → ∃ τ, □ τ`. The two continuations are kept apart.

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** Quietly assumes modal metaphysics — necessity is a contested fragment, not a consequence.
> **The reply / the frontier —** The world-level necessity of §9 is the *logical* continuation — classical meta-logic resident in Core/Semantics (`Semantics.strongTruthExists`, C59, footprint `{CL}`) — not a theorem derived from the normative chain. The normative world-level continuation is recorded separately (`NecessaryNormativeOrder : ∀ w, NormativeOrderAt w`) and is never claimed to entail `∃ τ, □ τ`. Neither continuation presupposes an ungrounded modal metaphysics.
</details>

Step 1: Strong Necessary Truth exists (resident in the Core/Semantics machinery).

    ∴ ∃ τ, □ τ

✅ · [NecessaryPersonalGround.lean#step1_necessary_truth_exists](formal/Logos/NecessaryPersonalGround.lean#L191)

---

## 10. Constructive Personal Ground

The dependence `RightWrong ⇒ Person` was proved in §8. Its constructive form needs no grounding axiom: the ontological direction is encoded in the definition — `ObjectiveNormativity ⇒ Person` is discovery, `Person ⇒ Right/Wrong` is RightWrong indexed by Person (the `GroundsRightWrong` record).

The headline — 'the Person supports the reality of Right' — asserts that the RightWrong-reality, the objective correctness structure governing judgments about what is the case, has a personal ontological ground-type. The four distinctions of §8 apply unchanged; in particular, grounding the correctness order is not producing reality (§8, distinction 4).

*(Detailed technical proof & model analysis: [investigations/divine-personhood.md](investigations/divine-personhood.md))*

<details>
<summary>The skeptic's attack & the reply</summary>

> **The skeptic tries —** You still quietly pick a contingent author of morality — some particular person who happens to ground Right/Wrong.
> **The reply / the frontier —** The indexing encodes *dependence without nomination*: RightWrong is indexed by a personal kind/type, not by any arbitrary contingent individual — objective Normativity ⇒ Person is discovery, Person ⇒ Right/Wrong is the typed index. And Branch C below marks exactly what is NOT forced: trinity, contingent creation, and incarnation all remain countermodel frontiers (⇏).
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

    ∴ Person ≡ FreeSubject(s) — defined in §6. Person.

    ∴ T ≡ p — defined in §2. Ought and Normative Polarity.

</details>

The ontology in one universal: wherever Right/Wrong is real, its ground-type is personal (the 'simple thing'). The elaborated `GroundsRightWrong` record is its record-form (DEFINITIONAL).

    ∴ RightWrong(s) → Person(s)

✅ · [PersonalGroundOfReality.lean#personal_ground_of_right_wrong](formal/Logos/PersonalGroundOfReality.lean#L98)

Constructive direction of discovery: Objective Normativity ⇒ Person.

    ∴ ObjectiveNormativity → ∃ p, RightWrong(p)

✅ · [PersonalNormativeGround.lean#discover_person](formal/Logos/PersonalNormativeGround.lean#L103)

HEADLINE — THE PERSON SUPPORTS THE REALITY OF RIGHT.

    ∴ (¬∃ s, ClaimsCorrect(s, NoRight) ∧ NoRight) ∧ EstablishedRightWrong ∧ (∀ p, T(p) ∨ IsFalse(p)) ∧ NecessaryNormativeOrder ∧ (∀ s, RightWrong(s) → Person(s)) ∧ (∀ s, Person(s) → GroundsRightWrong s)

✅ · [PersonalGroundOfReality.lean#the_person_supports_the_reality_of_right](formal/Logos/PersonalGroundOfReality.lean#L150)

<details>
<summary>Supporting Infrastructure — 2 auxiliary theorem(s) beneath this step</summary>

Objective Normativity holds from any agential normative address.

    ∃ s, a, b, GenuineNormativity s a b → ObjectiveNormativity

✅ · [PersonalNormativeGround.lean#objective_normativity_holds](formal/Logos/PersonalNormativeGround.lean#L127)

HEADLINE (instance form, datum-guarded). The personal ontological ground is the necessary ground of the objective normative/truth order governing judgments about Γ-reality (Right/Wrong, truth/falsity, Ought/OughtNot under TruthNorm): it grounds the correctness of propositions *about* what is the case, not the fact of what exists.

    Person(s) → Person(s) ∧ GroundsRightWrong s ∧ NecessaryNormativeOrder

✅ · [PersonalGroundOfReality.lean#person_yields_personal_grounding_of_reality](formal/Logos/PersonalGroundOfReality.lean#L196)

</details>

### Branch A: Necessity and Eternity of the Divine Being (Ground)

Live theorem: the ground is world-rigid (`NecessaryEntity Entity.ofGround`, `∀ w, ExistsAt w .ofGround`, definitional `EntityExistsAt w .ofGround := True`, footprint `{Means, Subject}`) and thereby **everlasting** and **atemporal** (definitional corollaries of necessity — no temporal premise; time enters only on the conclusion side via the Nat-stage layer). Claim E is the *non-hypostatic* pairing (`∃ g s, NecessaryEntity g ∧ NecessaryGroundOfReality g ∧ Person s ∧ GroundsRightWrong s`): entity-necessity conjunct PROVEN; personal-kind conjunct honestly `{AxTwoSubjects, Means, Subject}` (PROVEN↑ under META `AxTwoSubjects`). Hypostatic identity, a 'necessary Person', Trinity and monotheism are NOT claimed — `ofGround_ne_ofSubject` blocks the identity line.

HEADLINE — the necessary ground of reality exists: `Entity.ofGround` is a necessary entity and the ontological ground of reality.

    ∴ NecessaryGroundOfReality Entity.ofGround

✅ · [NecessityEternity.lean#ofGround_necessary_ground_of_reality](formal/Logos/NecessityEternity.lean#L126)

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

</details>

<details>
<summary>Obstruction / Formal Boundary: `necessary_ground_not_entails_contingent_creation`</summary>

Acosmic Divine Model: A necessary divine ground exists with zero contingent created reality.

    necessary_ground ⇏ contingent_creation

🧱 necessary_ground ⇏ contingent_creation · [ConditionalTheology.lean#necessary_ground_not_entails_contingent_creation](formal/Logos/ConditionalTheology.lean#L420)

</details>

<details>
<summary>Obstruction / Formal Boundary: `preceding_theory_not_entails_incarnation`</summary>

Unincarnate Hostile Model: The existing theory (necessary divine ground, human agency, free will) is completely consistent with God remaining purely transcendent and unincarnate.

    preceding_theory ⇏ incarnation

🧱 preceding_theory ⇏ incarnation · [ConditionalTheology.lean#preceding_theory_not_entails_incarnation](formal/Logos/ConditionalTheology.lean#L380)

</details>

---

## Formal Frontiers

The frontier is the set of claims that are not currently derived. An **OPEN** claim has no kernel node (blocked, deferred, answered, or a missing lemma) and is listed below. A **COUNTERMODEL** claim is a proposed inference that a hostile model refutes: the step is *withdrawn*, and what survives is recorded in Appendix C.2. The premier open frontier is deontic teleology (F2); moral good (F3) is no longer open — the faithful model `M_amoral` machine-separates practical bindingness from epistemic agential normativity (`MoralFrontierAudit.epistemic_normativity_without_practical_obligation`, C175, `{}`), making F3 a countermodel frontier, not a gap.

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
> and ledger (never from intentions). The three scopes are kept apart: the **Divine
> Being / Ground**, **Divine Personhood**, and the **personal normative ground /**
> **person-type** — what §1–§10 actually establish. "Necessity" concerns the
> Being/Ground, not each Divine Person; "Personal", "Three Persons", and "One God"
> are separate claims and are reported separately. Nothing here claims a "necessary
> Person": "He is necessary" is a claim about the Divine Being / Ground, "He is
> personal" a claim about the ground-type — two different rows, never conjoined.

Status vocabulary used here (extends the badge legend above): `✅` PROVEN (machine-verified, footprint stated) · `📘` DEFINITIONAL · `⏸` DEFERRED (target not in the live kernel) · `❌` NOT ESTABLISHED (no current theorem; distinct from the ledger's `✖` BLOCKED) · `🧱` INDEPENDENT / FRONTIER (explicit countermodel: the preceding theory does not entail it).

| Classical characteristic | Scope | Status | Exact sense established by the current theory (reference) |
|---|---|---|---|
| **Personal** — the ground-type is personal | Personal ground / person-type | ✅ PROVEN | `RightWrong ⇒ Person` (`∀ s, RightWrong s → Person s`). Established of the personal ground/type, not of a particular divine person. — [PersonalGroundOfReality.lean#personal_ground_of_right_wrong](formal/Logos/PersonalGroundOfReality.lean#L98), footprint {Means, Subject} |
| **Rational** — formally equivalent to the Thomistic core containing RationalNature | Personal ground / person-type | ✅ PROVEN | `Person(s) ↔ ThomisticPersonCore(s)`, whose conjunct `RationalNature s ≡ Intentional s ∧ FreeWill s` is definitional (`📘`). Established of the person-type. — [Person.lean#person_iff_thomisticCore](formal/Logos/Person.lean#L137), footprint {Means, Subject, Will, subjectWill, will_individuation} ; [Person.lean#RationalNature](formal/Logos/Person.lean#L70), footprint {Means, Subject} |
| **Free** — genuine normativity yields genuine choice and free will | Personal ground / person-type | ✅ PROVEN | `GenuineNormativity ⇒ Chooses ⇒ FreeWill`; `FreeWill s ≡ ∃ p q, Chooses s p q` is definitional (`📘`). — [IndubitableNormativeFreeWill.lean#indubitable_normative_free_will](formal/Logos/IndubitableNormativeFreeWill.lean#L115), footprint {Means, Subject} ; [Choice.lean#FreeWill](formal/Logos/Choice.lean#L163), footprint {Means, Subject} |
| **Independent will** — with numerical individuation | Personal ground / person-type | ✅ PROVEN | `Person(s) ↔ FreeIndependentWill(s)`; `subjectWill s₁ ≠ subjectWill s₂` — distinct persons have numerically distinct wills. The meaning-postulate status is kernel-verified: `will_individuation` is not derivable from the pre-will spine (`WillIndividuationAudit.will_individuation_not_forced_by_prewill_spine`, `{}`). — [Person.lean#person_iff_freeIndependentWill](formal/Logos/Person.lean#L117), footprint {Means, Subject, Will, subjectWill, will_individuation} ; [Person.lean#IndependentWill](formal/Logos/Person.lean#L54), footprint {Subject, Will, subjectWill} |
| **Dominion over acts** / authoritative personhood | Personal ground / person-type | ✅ PROVEN | the Thomistic-personcore conjunct `DominionOverActs s ≡ FreeWill s` is definitional (`📘`); present inside `person_iff_thomisticCore`. — [Person.lean#DominionOverActs](formal/Logos/Person.lean#L74), footprint {Means, Subject} |
| **Ground of objective normativity (Right and Wrong)** | Personal ground / person-type | ✅ PROVEN | `Person s → GroundsRightWrong s`, and the headline that "the person supports the reality of Right". Established of the personal ground. — [PersonalNormativeGround.lean#person_grounds_normative_polarity](formal/Logos/PersonalNormativeGround.lean#L385), footprint {Means, Subject} ; [PersonalGroundOfReality.lean#the_person_supports_the_reality_of_right](formal/Logos/PersonalGroundOfReality.lean#L150), footprint {Initiates, Means, State, Subject, CL} |
| **Necessary Divine Being / Ground** | Divine Being / Ground | ✅ PROVEN | The ground itself is world-rigid: `NecessaryEntity Entity.ofGround` (`∀ w, ExistsAt w .ofGround`, definitional `EntityExistsAt w .ofGround := True`, footprint `{Means, Subject}` — VOCAB only). Claim E is now a **live theorem** as a *non-hypostatic* pairing: the entity-necessity conjunct is PROVEN, the personal-kind conjunct is `{AxTwoSubjects, Means, Subject}` (PROVEN↑ under the declared META axiom `AxTwoSubjects`), and the hypostatic identity is blocked (`ofGround_ne_ofSubject`: `ofGround ≠ EntityOf s`). NO 'necessary Person' theorem exists — this row is the entity-level ground, distinct from the necessary-*order* row above. — [NecessityEternity.lean#ofGround_necessary_ground_of_reality](formal/Logos/NecessityEternity.lean#L126), footprint {Means, Subject} ; [NecessityEternity.lean#claimE](formal/Logos/NecessityEternity.lean#L269), footprint {AxTwoSubjects, Means, Subject} ; [NecessaryPersonalGround.lean#step1_necessary_truth_exists](formal/Logos/NecessaryPersonalGround.lean#L191), footprint {CL} ; [NecessaryPersonalGround.lean#necessary_normative_order](formal/Logos/NecessaryPersonalGround.lean#L110), footprint {Initiates, Means, State, Subject} |
| **One God / strict monotheism** (unity of the Divine Being) | Divine Being / Ground | ⏸ DEFERRED | Strict monotheism (`monotheism_of_god_and_uniqueness`, `monotheism_compatible_with_trinity`) is deferred out of the live kernel (Branch B, `⏸`); unity concerns the Divine Being, not numerical identity of Personhood. Uniqueness is provably NOT a kernel consequence: the machine-witnessed separation `TheologicalModalHardening.necessary_existence_not_entails_uniqueness` (`¬ (∀ S, UniqueExists S.NecessaryEntity)`, L406-414, footprint `{}`) and the deferred `universal_ground_unique` (`NecessaryPersonalGround.lean:24`) mark it as an interpretive layer. |
| **Perfect (moral) goodness** | Divine Being / Ground | 🧱 INDEPENDENT | GAPMAP ledger row `F3 §28 (Good)` = COUNTERMODEL (🧱) via C175: the `M_amoral` model (`{}`) satisfies epistemic agential normativity with no practical obligation. Right/Wrong here is epistemic correctness, explicitly distinguished from moral good/evil; a positive moral bridge would cost the declared SEM poles `Good`/`Evil` (price sheet §5.4). |
| **Eternal — ever-present** (everlasting existence) | Divine Being / Ground | ✅ PROVEN | World-rigid existence is unmodulated by time: `NecessaryEntity e → Everlasting e` (`∀ t, ExistsAtTime t e`) is a definitional corollary of necessity via the Nat-stage layer — the deduction imports NO temporal premise, time enters only on the conclusion side. `Everlasting Entity.ofGround` is therefore PROVEN (`{Subject}` + ground footprint, VOCAB). Distinct from the eternal love-*relation* `T14_eternalRelation_conditional`. — [NecessityEternity.lean#the_ground_everlasting](formal/Logos/NecessityEternity.lean#L160), footprint {Subject} ; [NecessityEternity.lean#necessary_implies_everlasting](formal/Logos/NecessityEternity.lean#L145), footprint {Subject} ; [NecessityEternity.lean#ofGround_necessary](formal/Logos/NecessityEternity.lean#L110), footprint {Subject} ; [Love.lean#T14_eternalRelation_conditional](formal/Logos/Love.lean#L98), footprint {AxTwoSubjects, Means, Subject} |
| **Atemporal** (existence not time-modulated; outside succession) | Divine Being / Ground | ✅ PROVEN | `NecessaryEntity e → Atemporal e` (`ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e`); the ground is also outside every initiation-act (`the_ground_not_in_succession`, `{Initiates, State, Subject}`). Separation is honest: atoms/subjects are time-modulated (`atom_has_temporal_mode`) and `Everlasting` does not collapse into necessity (`everlasting_but_contingent`). What is PROVEN is stage-unmodulated world-rigid existence — not a full theology of divine eternity. — [NecessityEternity.lean#the_ground_atemporal](formal/Logos/NecessityEternity.lean#L164), footprint {Subject} ; [NecessityEternity.lean#necessary_implies_atemporal](formal/Logos/NecessityEternity.lean#L152), footprint {Subject} ; [NecessityEternity.lean#the_ground_not_in_succession](formal/Logos/NecessityEternity.lean#L169), footprint {Initiates, State, Subject} ; [NecessityEternity.lean#atom_has_temporal_mode](formal/Logos/NecessityEternity.lean#L212), footprint {Subject} ; [NecessityEternity.lean#everlasting_but_contingent](formal/Logos/NecessityEternity.lean#L237), footprint {Subject} |
| **Divine simplicity** | Divine Being / Ground | ❌ NOT ESTABLISHED | No live theorem. |
| **Omniscience** | Divine Being / Ground | ❌ NOT ESTABLISHED | `Omniscience_AllTruths` / `Omniscience_Counterfactuals` (`DeepModalFrontier`) are frontier vocabulary definitions, not theorems. — [DeepModalFrontier.lean#Omniscience_AllTruths](formal/Logos/DeepModalFrontier.lean#L313), footprint {} ; [DeepModalFrontier.lean#Omniscience_Counterfactuals](formal/Logos/DeepModalFrontier.lean#L317), footprint {} |
| **Omnipotence** | Divine Being / Ground | ❌ NOT ESTABLISHED | No live theorem. |
| **Creator of contingent reality** | Divine Being / Ground | 🧱 INDEPENDENT | `necessary_ground ⇏ contingent_creation` (Acosmic model, footprint `{}`): a necessary divine ground is consistent with zero contingent created reality. (Ledger target F9 DEFERRED.) — [ConditionalTheology.lean#necessary_ground_not_entails_contingent_creation](formal/Logos/ConditionalTheology.lean#L420), footprint {} |
| **Three Divine Persons (Trinity)** | Divine Personhood | 🧱 INDEPENDENT | `preceding_theory ⇏ trinity` (Binitarian separation model, footprint `{}`). A separate claim, distinct from necessity and from unity. (F6/F8 DEFERRED; plurality `T12_twoPersons` is at most generic persons under `AxTwoSubjects`.) — [ConditionalTheology.lean#preceding_theory_not_entails_trinity](formal/Logos/ConditionalTheology.lean#L336), footprint {} |
| **Incarnation** | Divine Personhood | 🧱 INDEPENDENT | `preceding_theory ⇏ incarnation` (Unincarnate model, footprint `{}`). (F9 DEFERRED.) — [ConditionalTheology.lean#preceding_theory_not_entails_incarnation](formal/Logos/ConditionalTheology.lean#L380), footprint {} |

_Synthesis — the strongest current profile._ The theory has established, of a
**personal, rational, free, authoritative-over-its-acts, independently individuated**
**normative ground / person-type**, that its objective Right/Wrong order is the object
of a necessary normative/truth order, and (entity-level) that a **necessary Divine Being
/ Ground** exists — world-rigid, **everlasting** and **atemporal**, a definitional
corollary of necessity with time entering only on the conclusion side. The remaining
divine attributes — **unity / monotheism**, **simplicity**, **omniscience**, **omnipotence**,
**perfect moral goodness**, the **Trinity**, the **Incarnation**, and contingent
**creation** — remain **separate proof targets**
(`⏸` / `❌`) or explicit **countermodel frontiers** (`🧱`) until the live kernel proves them.

## Further Investigations

### Retorsions

<details>
<summary>Retorsion catalogue — 89 machine-checked retorsion theorems (click to expand)</summary>

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
* [The Incarnation — The Builder Entering the House](investigations/incarnation.md) — THEOLOGICAL TELEOLOGICAL BRIDGE / UNINCARNATE MODEL
* [Plurality of Divine Persons and Eternal Love](investigations/plurality-and-love.md) — THEOREMS T12, T13, T14 (`{Means, Subject, AxTwoSubjects}`)
* [The Trinity and the Condilectus Principle](investigations/trinity.md) — CONDITIONAL METAPHYSICAL BRIDGE / BINITARIAN SEPARATION MODEL

### Technical

* [Technical Appendix: Kernel Audit, Consistency & Code Annex](investigations/kernel-audit.md) — Complete kernel audit, transitive axiom footprints, dependency ledger, and consistency checks.
* [Formal Dependency Graph (JSON)](formal/depgraph.json) / [(DOT)](formal/depgraph.dot) — LeanDepViz transitive kernel dependency DAG.
* [Theorem Ledger (GAPMAP)](formal/GAPMAP.md) — Formal correspondence mapping across formal and prose corpora.
