# Γ — The Deduction

> **Γ is a machine-checked deduction.** Right and wrong are real — and satisfaction is free:
> `¬N_T ∧ ¬N_F` needs no one. But being *true* is being true **to** someone, right and wrong
> require meaning, meaning requires a subject, and a subject that means both poles of an
> incompatibility is free. So the order forces a person
> (`Order ⇒ Meaning ⇒ Free Subject ⇒ Person`), and its ground-type is personal
> (`RightWrong ⇒ Person`) — the epistemic poles, not the deontic ones.
>
> Nothing can be epistemologically right or wrong without a Free being **for which meaning can mean** (C553, the FACT — zero substantive axioms).

**How to read a step.** Claim in words first, machine rendering beneath:
- `∴` introduces the symbolic rendering that follows. `≡` reads "by definition" (`📘`);
  `→` and `↔` mean implication and equivalence; `⇒` chains steps into one argument;
  `⇏` marks a demonstrated *non-consequence* (a countermodel frontier, `🧱`).
- a **backticked name** is the Lean declaration that verifies the line; footers like
  `✅ · File.lean#name` link to it under `formal/Logos/`.
- each section reads: claim → the skeptic's move → the reply → one theorem row.
- the chain `Order ⇒ Meaning ⇒ Free Subject ⇒ Person` is the same argument the numbered
  sections build link by link; the earlier *deontic* route is kept whole in the ledger.

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
| **426 affirmative claims derived** out of **558** ledger claims — 362 ✅ kernel-verified, 64 ⚠️ derived under a substantive (`SEM`/`META`) axiom, each ⚠️ row naming the bridge it rests on. | **14 blocked** ✖ — named individually |
| **60 countermodel boundaries** 🧱 — a hostile model in which the claim *fails*. These are won results about the limit of the theory, not gaps. | &nbsp;&nbsp;· **C228** — any entity that grounds Right/Wrong is a Personal Entity |
| **965 of 1790 theorems in `formal/Logos/` rest on no Γ axiom at all** (54%) — counted from `formal/axiom_audit.json`, not claimed. | &nbsp;&nbsp;· **C462** — BLOCKED, with no declaration, and deliberately so: the ground does not initiate is not refutable in Gamma and is not evidence of non-agency either |
| **The whole price is 35 declared axioms**: 17 are `VOCAB` (the vocabulary the statements need in order to be sayable) and 18 are substantive. Only the 18 are philosophical commitments; the rest are the theory's definitions of its own words, which is a different thing from a premise. | &nbsp;&nbsp;· **C503** — A love-lane step for deriving the Good from a second person is BLOCKED, with no declaration (lote OTHER, 2026-09-29; plan OTHER.md): the step 'the… |
| **10 attribute corollaries became unconditional theorems** (C389–C398) — they were conditional on a `def` until F15 was declared, so this is a *strengthening*: fewer hidden premises, same conclusions. | &nbsp;&nbsp;· **C73** — Plurality without bridges is blocked: unit countermodel settles that 1 act does not entail plurality; requires AxTwoSubjects |
|  | &nbsp;&nbsp;· **C75** — Propositional personhood is blocked: content existence does not entail personhood |
|  | &nbsp;&nbsp;· **C79** — Ultimate ground existence is blocked: infinite descending chains have no ultimate element without a well-foundedness axiom |
|  | &nbsp;&nbsp;· **C89** — Ultimate ground by initiation is blocked: non-entailed without well-foundedness |
|  | &nbsp;&nbsp;· **C90** — Personal ultimate ground is blocked: ultimate grounding does not entail personal nature |
|  | &nbsp;&nbsp;· **F11** — The bare rejected horn is BLOCKED, and now nameable: Logos.AsieticChoice.bareRejectedHornCoMeant : (∃ s : Subject, ∃ p : Prop, Means s p) → ∃ s… |
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
of the ground and lost the soteriology.** Established: genuine normativity has a
personal ground; that ground is unique and necessary; it possesses canonical
aseity, simplicity, and pure actuality. What is *not* free: the three divine
Persons of the Trinity (three declared META premises, C510), and what is still
open: the Incarnation, contingent creation as such, and the entity-level
projection C228. Strict monotheism — the ground as a *single* person — is no
longer on this list: it is refuted as a consequence (one ground, and every ground
bears at least two distinct persons). Each open row is named above with its
missing lemma rather than absorbed into an average, and the left column is
larger because the ground-theory was proved, not because the open rows were
rounded down.

Four qualifications, stated rather than hidden:

1. **A ✅ means "kernel-verified on declared vocabulary", not "free of metaphysical assumption".** The vocabulary axioms are real axioms; they are merely the ones the statements need in order to be said at all. The substantive ones are the 18 `SEM`/`META` bridges.
2. **The 35 declared axioms are inputs, not wins.** Counting them as results would be the same error as counting a hypothesis as a proof. They are listed so the reader can price Γ exactly, and `VOCAB` is separated from `SEM`/`META` because only the latter are commitments.
3. **A 🧱 is a win about a boundary, not about the claim.** Γ building a model in which monotheism fails is a real theorem — and a theorem *against* monotheism. The columns keep those apart on purpose.
4. **The 15 retired routes are counted as neither won nor open.** Their ledger notes say the step was destroyed under hostile semantics; that is a settled negative. Filing them under "still open" would overstate the debt, and filing them as won would overstate the theory, so they get their own line.

<sub>Declaration count excludes 5 parsed names with no `#print axioms` footprint; they are `parse_lean_sources` artefacts and are excluded from the denominator rather than scored axiom-free.</sub>

## The Argument in Ten Steps

One row per step, every status derived from the kernel — never transcribed. Click any name for its Lean source.

| # | Step | Core formula | Derived status |
|---|---|---|---|
| **1** | **SATISFACTION** — Satisfaction Is Free | `¬N_T ∧ ¬N_F · bivalence: ∀ p, T p ∨ IsFalse p` | ✅ **PROVEN** · 0 substantive axioms · [Core.lean#rightWrongDistinction](formal/Logos/Core.lean#L145), footprint {} |
| **2** | **DISCLOSURE** — Being True Is Being True To Someone | `Correct s p → TrueTo s p → T p,  where TrueTo s p := Means s p ∧ T p` | ✅ **PROVEN** · 0 substantive axioms · [EpistemicNecessity.lean#being_true_is_being_true_to](formal/Logos/EpistemicNecessity.lean#L406), footprint {Initiates, Means, State, Subject} |
| **3** | **MEANING** — Right and Wrong Cannot Obtain Without Meaning | `(∃ s p, Correct s p) ∨ (∃ s p, Incorrect s p) → ∃ p, Meaning_I p` | ✅ **PROVEN** · 0 substantive axioms · [Order.lean#rightWrong_implies_meaning](formal/Logos/Order.lean#L89), footprint {Initiates, Means, State, Subject} |
| **4** | **SUBJECT** — Meaning Requires a Subject | `Meaning_I p → ∃ s, Means s p` | ✅ **PROVEN** · 0 substantive axioms · [Choice.lean#meaning_I_needs_subject](formal/Logos/Choice.lean#L139), footprint {Means, Subject} |
| **5** | **INCOMPATIBILITY** — The Two Poles Cannot Both Be Correct | `Incompatible (Correct s p) (Incorrect s p)` | ✅ **PROVEN** · 0 substantive axioms · [NormativeOrder.lean#correctness_incompatible](formal/Logos/NormativeOrder.lean#L135), footprint {Initiates, Means, State, Subject} |
| **6** | **FREE WILL** — Co-Meaning Both Poles Is Free Will | `ClaimsNormativeCorrectness s p → Chooses s (Correct s p) (Incorrect s p) ∧ FreeWill s` | ✅ **PROVEN** · 0 substantive axioms · [NormativeOrder.lean#claims_normative_correctness_derives_free_will](formal/Logos/NormativeOrder.lean#L190), footprint {Initiates, Means, State, Subject, CL} |
| **7** | **PERSON** — Free Will Is a Person | `FreeWill s → Person s` | ✅ **PROVEN** · 0 substantive axioms · [Person.lean#freeWill_implies_person](formal/Logos/Person.lean#L135), footprint {Means, Subject, Will, subjectWill, will_individuation} |
| **8** | **GROUNDING** — That Person Grounds the Poles | `GroundsRightWrongAt s (Correct s p) (Incorrect s p) ∧ Person s` | ✅ **PROVEN** · 0 substantive axioms · [EpistemicPersonalGround.lean#epistemic_polarity_is_personally_grounded](formal/Logos/EpistemicPersonalGround.lean#L107), footprint {Initiates, Means, State, Subject, CL} |
| **9** | **THE FACT** — The Fact | `ClaimsNormativeCorrectness s p → (∃ w, w = subjectWill s) ∧ FreeWill s ∧ FreeSubject s ∧ Person s ∧ Means s (C` | ✅ **PROVEN** · 0 substantive axioms · [EpistemicNecessity.lean#epistemic_right_wrong_requires_a_free_being_for_which_meaning_can_mean](formal/Logos/EpistemicNecessity.lean#L107), footprint {Initiates, Means, State, Subject, Will, subjectWill, will_individuation, CL} |
| **10** | **THE CHAIN, COMPOSED** — The Chain, Composed — Both Directions | `¬(∃ s, Means s p) → ¬(∃ s p, Correct s p) ∧ ¬(∃ s p, Incorrect s p)` | ✅ **PROVEN** · 0 substantive axioms · [EpistemicNecessity.lean#no_subject_who_means_no_epistemic_right_wrong](formal/Logos/EpistemicNecessity.lean#L328), footprint {Initiates, Means, State, Subject} |

Edges are typed, and the two directions are not the same move: **[distinction]** separates levels (step 1 gives the personless order away on purpose), **[discovery]** carries the chain forward, and **[grounding]** is the person→pole dependence. §13 then closes the whole thing by retorsion.

## 1. Satisfaction Is Free

Right and wrong both obtain, and every proposition is either the case or not — with no subject anywhere in either statement. The denial of the person is available at exactly this level, so the argument must earn the next step rather than assume it.

> ⚠️ **Price disclosed —** 0 substantive axioms. The concession costs nothing.

*(Detailed technical proof & model analysis: [investigations/right-and-wrong.md](investigations/right-and-wrong.md))*

> **The skeptic tries —** "Satisfaction needs nobody — on your own first line nothing binds you to a person."
> **The reply —** Agreed — and that is the point: satisfaction is free, disclosure is *to* someone. The poles are act-level, so the order is a structure someone stands in.

Right and wrong both obtain: it is false that nothing is true, and false that everything is true.

    ∴ ¬N_T ∧ ¬N_F

✅ · [Core.lean#rightWrongDistinction](formal/Logos/Core.lean#L145)

Every proposition is either true or false.

    ∴ ∀ p, T(p) ∨ IsFalse(p)

✅ · [Core.lean#bivalence](formal/Logos/Core.lean#L195)

> ➔ **Linear Forward Transition to Step 2 (Being True Is Being True To Someone):** [➔ Continuation · *satisfaction is free; disclosure is not*]
## 2. Being True Is Being True To Someone

Disclosure is right/wrong **to** someone: `Correct → TrueTo → T`, where `TrueTo s p := Means s p ∧ T p`. The epistemic poles are act-level, so the order already carries a subject in its definition. Satisfaction is free; being-true is not.

> ⚠️ **Price disclosed —** 0 substantive axioms.

*(Detailed technical proof & model analysis: [investigations/right-and-wrong.md](investigations/right-and-wrong.md))*

> **The skeptic tries —** "Truth-to-a-subject is just truth with a subject smuggled in."
> **The reply —** A definition, not an assumption — and the derivation runs from the personless order to the personful consequence. Read the next two steps before answering.

**The alethic chain: judging rightly is being-true, being-true is being-the-case.** `Correct s p → TrueTo s p` (drop the `Initiates` horn of the act) and `TrueTo s p → T p` (drop the meaning). So correctness entails truth-to, and truth-to entails truth — while the converses fail: `T p` with no…

    ∴ (Correct(s, p) → TrueTo(s, p)) ∧ (TrueTo(s, p) → T(p))

✅ · [EpistemicNecessity.lean#being_true_is_being_true_to](formal/Logos/EpistemicNecessity.lean#L406)

> ➔ **Linear Forward Transition to Step 3 (Right and Wrong Cannot Obtain Without Meaning):** [▲ Discovery · *right/wrong is right/wrong-to-someone*]
## 3. Right and Wrong Cannot Obtain Without Meaning

C62: right/wrong anywhere ⇒ something is meant. Meaning is the term in which the denial fails first — which is why the epistemic poles, not the deontic ones, carry the argument.

> ⚠️ **Price disclosed —** 0 substantive axioms.

*(Detailed technical proof & model analysis: [investigations/right-and-wrong.md](investigations/right-and-wrong.md))*

> **The skeptic tries —** "Brute facts alone can still be 'correct' — 'correct' just means 'fits the facts'."
> **The reply —** Then "correct" means conformity to a standard — and a standard is not a brute fact. It is what makes some things fit and others not, and it is meant.

Right and wrong need meaning: the normative predicates are properties of acts, so wherever right-or-wrong is realized, meaning (and thus a subject, C49) is realized.

    (∃ s, p, Correct(s, p)) ∨ (∃ s, p, Incorrect(s, p)) → ∃ p, Meaning_I(p)

✅ · [Order.lean#rightWrong_implies_meaning](formal/Logos/Order.lean#L89)

> ➔ **Linear Forward Transition to Step 4 (Meaning Requires a Subject):** [▲ Discovery · *rightWrong_implies_meaning*]
## 4. Meaning Requires a Subject

C49 `meaning_I_needs_subject`, contrapositive C560 `no_meaning_no_correctness`. Meaning is the act `Means s p`, and an act has an agent — this is why the deduction reaches a person and not merely a law.

> ⚠️ **Price disclosed —** 0 substantive axioms (`{Means, Subject}` for C49).

*(Detailed technical proof & model analysis: [investigations/contrastive-choice.md](investigations/contrastive-choice.md))*

> **The skeptic tries —** "Meaning belongs to a language or a text, not to a person."
> **The reply —** Then fill in the subject of `Means` and it is whatever does the meaning — a text means *to* someone, a language means *for* someone. The kernel has exactly one sort for this: `Subject`.

Meaning needs a subject: intentional meaning contains its subject by definition.

    Meaning_I(p) → ∃ s, Means(s, p)

✅ · [Choice.lean#meaning_I_needs_subject](formal/Logos/Choice.lean#L139)

**No meaning, no right/wrong.** If nothing means `p`, then `p` is not among the contents anyone means — `¬ Meaning_I p` — so `p` is neither correctly nor incorrectly judgable. The third leg of the author's chain, `{}`.

    ¬∃ s, Means(s, p) → ¬Meaning_I(p)

✅ · [EpistemicNecessity.lean#no_meaning_no_correctness](formal/Logos/EpistemicNecessity.lean#L307)

> ➔ **Linear Forward Transition to Step 5 (The Two Poles Cannot Both Be Correct):** [▲ Discovery · *a subject that means holds a norm*]
## 5. The Two Poles Cannot Both Be Correct

Derived, not assumed: `Incompatible (Correct s p) (Incorrect s p)` from `Ought`/`OughtNot`. It is what makes step 6 a determination rather than a verbal flourish.

> ⚠️ **Price disclosed —** 0 substantive axioms.

*(Detailed technical proof & model analysis: [investigations/contrastive-choice.md](investigations/contrastive-choice.md))*

> **The skeptic tries —** "'Incompatible' is just logical disjointness — and holding a disjunction is trivial."
> **The reply —** Then the triviality is of an ought and an ought-not being exclusive — that is normativity, not logic. Meaning both poles is holding a norm that must be settled one way or the other.

Correctness and incorrectness are mutually incompatible, derived directly from the incompatibility of Ought and OughtNot under TruthNorm.

    ∴ Incompatible(Correct s p, Incorrect s p)

✅ · [NormativeOrder.lean#correctness_incompatible](formal/Logos/NormativeOrder.lean#L135)

> ➔ **Linear Forward Transition to Step 6 (Co-Meaning Both Poles Is Free Will):** [▲ Discovery · *co-meaning an incompatibility IS choice*]
## 6. Co-Meaning Both Poles Is Free Will

C140: a stance co-meaning both poles emits `Chooses` and `FreeWill`. Capital-F *Free* is non-determinism between incompatible alternatives — not absence of cause, and not 'axiom-free'.

> ⚠️ **Price disclosed —** conditional on `ClaimsNormativeCorrectness`; **0 substantive axioms**. Unconditional existence of a free subject is §11's third row.

*(Detailed technical proof & model analysis: [investigations/free-will.md](investigations/free-will.md))*

> **The skeptic tries —** "Definitional inflation — you renamed 'grasping a dilemma' as free will."
> **The reply —** `Chooses` is the *constitutive* condition of choice: deny the co-grasp while accepting the choice and you have a contradiction (`d7_co_grasp_is_definitionally_choice`). The critic owes an account of choice in which that is not so.

Master derivation from the normative judicative stance to Choice and Free Will.

    ClaimsNormativeCorrectness(s, p) → Chooses(s, Correct(s, p), Incorrect(s, p)) ∧ FreeWill(s)

✅ · [NormativeOrder.lean#claims_normative_correctness_derives_free_will](formal/Logos/NormativeOrder.lean#L190)

> ➔ **Linear Forward Transition to Step 7 (Free Will Is a Person):** [▲ Discovery · *priced theorem [Person := ThomisticPersonCore; via will_individuation]*]
## 7. Free Will Is a Person

C221 `freeWill_implies_person`; `Person := ThomisticPersonCore` (substance, rational nature, dominion over acts). The price is the VOCAB law `will_individuation`, and the kernel *checks* it is underivable (`SharedWillModel`, `{}`).

> ⚠️ **Price disclosed —** priced on the declared VOCAB law `will_individuation`; 0 substantive axioms. The price is checked to be underivable (`SharedWillModel`, `{}`).

*(Detailed technical proof & model analysis: [investigations/divine-personhood.md](investigations/divine-personhood.md))*

> **The skeptic tries —** "That is the anthropomorphic smuggling you promised to avoid."
> **The reply —** The price is named, tagged VOCAB and machine-separated. If personhood were free the theorem would need no axiom; it needs exactly one, and `SharedWillModel` exhibits where it fails.

HEADLINE (AC2): Free will implies Personhood — as a theorem, not a definition.

    FreeWill(s) → Person(s)

✅ · [Person.lean#freeWill_implies_person](formal/Logos/Person.lean#L135)

Master Correspondence: Personhood IS the Thomistic person core — honestly `rfl` now, since that is the definition (AC1′).

    ∴ Person(s) ↔ ThomisticPersonCore(s)

✅ · [Person.lean#person_iff_thomisticCore](formal/Logos/Person.lean#L183)

> ➔ **Linear Forward Transition to Step 8 (That Person Grounds the Poles):** [▼ Ontological Grounding · *the Person grounds the epistemic pole pair*]
## 8. That Person Grounds the Poles

C525/C527: what grounds right/wrong **at the epistemic poles** is a person. Grounding is neither identity nor causation; the Person is indexed at the pole pair and the reverse direction is stance-guarded by design.

> ⚠️ **Price disclosed —** 0 substantive axioms; the `def` bridge `EntityMeans ofGround := True` is disclosed in §13.

*(Detailed technical proof & model analysis: [investigations/grounding.md](investigations/grounding.md))*

> **The skeptic tries —** "Grounding a distinction is just being an instance of it — a category dressed as a cause."
> **The reply —** It refuses identity (`GroundsRightWrong` is not `=`) and causation (`EntityMeans ofGround := True`). The Person grounds the *pole pair* — narrower than a cause, stronger than an instance.

The epistemic right/wrong — `Correct s p` and `Incorrect s p`, which under the epistemic `TruthNorm` are `T p` and `IsFalse p` (`NormativeOrder.lean:72-75`) — is ontologically grounded, and the ground is the *indexed* one at that very pole pair. This is C171 (`grounding_forced_at_datum`)…

    ClaimsNormativeCorrectness(s, p) → GroundsRightWrongAt s (Correct(s, p)) (Incorrect(s, p))

✅ · [EpistemicPersonalGround.lean#epistemic_polarity_is_personally_grounded](formal/Logos/EpistemicPersonalGround.lean#L107)

HEADLINE. The epistemic right/wrong has a grounding of a personal kind, at its own poles.

    ClaimsNormativeCorrectness(s, p) → GroundsRightWrongAt s (Correct(s, p)) (Incorrect(s, p)) ∧ Person(s)

✅ · [EpistemicPersonalGround.lean#the_person_grounds_the_epistemic_right_wrong](formal/Logos/EpistemicPersonalGround.lean#L165)

> ➔ **Linear Forward Transition to Step 9 (The Fact):** [➔ Continuation · *THE FACT — the composed statement*]
## 9. The Fact

C553 pointwise-conditional, C555 existential, C556 propositional (`{}`). Three strengths, one sentence: the order entails a free being for which meaning can mean.

> ⚠️ **Price disclosed —** **0 substantive axioms.** Existence *from Γ's primitives alone* is §11's third row, priced on one META bridge (`AxTwoSubjects`).

*(Detailed technical proof & model analysis: [investigations/grounding.md](investigations/grounding.md))*

> **The skeptic tries —** "A conditional on an inserted stance is not a conclusion."
> **The reply —** Then use C556: no stance, and in every model some subject is free and some content is meant. The unconditional existence row is §11's third — one META bridge, named.

**THE FACT.** Nothing can be epistemologically right or wrong without a non-mechanical (Free) being for which meaning can mean.

    ClaimsNormativeCorrectness(s, p) → (∃ w, w = subjectWill(s)) ∧ FreeWill(s) ∧ FreeSubject(s) ∧ Person(s) ∧ Means(s, Correct s p) ∧ Means(s, Incorrect s p)

✅ · [EpistemicNecessity.lean#epistemic_right_wrong_requires_a_free_being_for_which_meaning_can_mean](formal/Logos/EpistemicNecessity.lean#L107)

**Existential form of the FACT.** If the epistemic stance obtains *somewhere* — some subject claims normative correctness of some content — then a non-mechanical personal being exists.

    ∃ s, p, ClaimsNormativeCorrectness(s, p) → ∃ s, FreeWill(s) ∧ FreeSubject(s) ∧ Person(s) ∧ (∃ p, Means(s, Correct s p) ∧ Means(s, Incorrect s p))

✅ · [EpistemicNecessity.lean#epistemic_normativity_somewhere_yields_a_free_being](formal/Logos/EpistemicNecessity.lean#L163)

The FACT on the propositional side, at `{}`: the `T`/`IsFalse` order, once non-vacuous, entails a non-mechanical being for which meaning can mean.

    ∴ ∀ M,.Signature, ∃ s,.Subject, M.Free s ∧ ∃ c,.Content, M.Means(s, c)

✅ · [EpistemicPersonalGround.lean#epistemic_order_requires_a_free_meaning_being](formal/Logos/EpistemicPersonalGround.lean#L276)

> ➔ **Linear Forward Transition to Step 10 (The Chain, Composed — Both Directions):** [➔ Continuation · *contrapositives composed [C557 entailment, C561 retraction]*]
## 10. The Chain, Composed — Both Directions

C561 (no subject who means → no right/wrong anywhere) and C557 (the order *entails* the act). The single TRANS axiom pays for the unconditional `∃ s, Act s p` — a different question. `F1bUncond`: SUPERSEDED.

> ⚠️ **Price disclosed —** 0 substantive axioms in both directions.

*(Detailed technical proof & model analysis: [investigations/right-and-wrong.md](investigations/right-and-wrong.md))*

> **The skeptic tries —** "A contrapositive about meaning. Nothing here touches physics."
> **The reply —** It does not need to: the claim is that the meaningless world is not a world with different physics but a world with no such state. The countermodels that could show otherwise are §12's bounded rows.

**No subject who means, no epistemic right/wrong.** If `¬ ∃ s, ∃ p, Means s p`, then `¬ ∃ s, ∃ p, Correct s p` and `¬ ∃ s, ∃ p, Incorrect s p`.

    ¬∃ s, p, Means(s, p) → ¬(∃ s, p, Correct(s, p)) ∧ ¬(∃ s, p, Incorrect(s, p))

✅ · [EpistemicNecessity.lean#no_subject_who_means_no_epistemic_right_wrong](formal/Logos/EpistemicNecessity.lean#L328)

**The act datum is necessary.** If the epistemic order obtains — someone holds the stance that makes right and wrong meaningful — then someone acts, at `{}`.

    ∃ s, p, ClaimsNormativeCorrectness(s, p) → ∃ s, p, Act s p

✅ · [EpistemicNecessity.lean#epistemic_order_makes_the_act_datum_necessary](formal/Logos/EpistemicNecessity.lean#L235)

## 11. Necessity, and Exactly What It Costs

Three rows, because they are three different facts. **The order is necessary with no premise at all.** A free subject exists on **one** META bridge. A necessary *person* is a **second** META axiom. Merging them into one claim is how an honest price becomes a dishonest boast.

The price attaches to the route, never to the name: `FreeSubject` is *defined* as `FreeWill` (`Choice.lean:185`, `freeSubject_iff_freeWill` is `Iff.rfl`), so `freeSubject_exists` and `freeWill_exists` carry the same footprint.

Before 2026-09-30 the surface priced the Free Subject dearer than free will for one identical predicate.

Necessity is the ground's, and the ground is not a subject-correlate: `ofGround_ne_ofSubject` (`{}`).

So "the Free Subject is necessarily true" is true of the *order* and of the *subject's existence* — and the necessary-person row is the one that would need C404. Say which, and the sentence is true.

| What it costs | What it settles | Derived status · footprint · source |
|---|---|---|
| The normative order is **necessary** | ∀ w, NormativeOrderAt w — at every world, unconditionally. | ✅ **PROVEN** · 0 substantive axioms · `{Initiates, Means, State, Subject}` · [NecessaryPersonalGround.lean#necessary_normative_order](formal/Logos/NecessaryPersonalGround.lean#L110), footprint {Initiates, Means, State, Subject} |
| The ground is **necessary** | `Entity.ofGround` is modal-fragile-free; a `def` bridge (`NecessarySubjectKind`) is disclosed in §13. | ✅ **PROVEN** · 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}` · [NecessityEternity.lean#ofGround_necessary_ground_of_reality](formal/Logos/NecessityEternity.lean#L161), footprint {Means, NecessarySubjectKind, Subject} |
| A **free subject exists** | Unconditional existence, via `freeWill_exists`. The one META bridge is `AxTwoSubjects` — plural personal reality. | ⚠️ **AXIOMATIC (AxTwoSubjects)** · `{Means, Subject, Will, subjectWill, AxTwoSubjects}` · [AsieticChoice.lean#freeSubject_exists](formal/Logos/AsieticChoice.lean#L489), footprint {AxTwoSubjects, Means, Subject, Will, subjectWill} |
| **Free will** exists | The same predicate under the other name; identical footprint by construction, not by coincidence. | ⚠️ **AXIOMATIC (AxTwoSubjects)** · `{Means, Subject, Will, subjectWill, AxTwoSubjects}` · [AsieticChoice.lean#freeWill_exists](formal/Logos/AsieticChoice.lean#L472), footprint {AxTwoSubjects, Means, Subject, Will, subjectWill} |
| A **person** has free will | `Person s → FreeWill s`: 0 substantive axioms. Dominion over acts *is* free will (`Person.lean:56`). | ✅ **PROVEN** · 0 substantive axioms · `{Means, Subject, Will, subjectWill}` · [Person.lean#person_has_free_will](formal/Logos/Person.lean#L157), footprint {Means, Subject, Will, subjectWill} |
| A **necessary person** exists | C404/C407: the second META bridge (`necessaryPersonalSubjectExists`). This is the row that would have to be paid for a necessary Free Subject. | ⚠️ **AXIOMATIC (necessaryPersonalSubjectExists)** · `{Means, NecessarySubjectKind, Subject, Will, subjectWill, necessaryPersonalSubjectExists}` · [Plurality.lean#necessarySubject_exists](formal/Logos/Plurality.lean#L189), footprint {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} |
| The ground is **not** a subject-correlate | `Entity.ofGround ≠ EntityOf s` for every `s`. The two necessities above are not identified. | ✅ **PROVEN** · 0 substantive axioms · `{Subject}` · [NecessityEternity.lean#ofGround_ne_ofSubject](formal/Logos/NecessityEternity.lean#L168), footprint {Subject} |

| Claim | Derived status | What it settles |
|---|---|---|
| `C404` | ◆ **AXIOM** — rests on `necessaryPersonalSubjectExists` · [Plurality.lean#necessaryPersonalSubjectExists](formal/Logos/Plurality.lean#L185), footprint {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} | Metaphysical bridge: the necessary kind of subject is inhabited by a person. |
| `C407` | ⚠️ **AXIOMATIC** — rests on `necessaryPersonalSubjectExists` · [Plurality.lean#necessarySubject_exists](formal/Logos/Plurality.lean#L189), footprint {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} | A necessary subject exists, from the bridge. Footprint: `{Means, NecessarySubjectKind, Subject, Will, necessaryPersonalSubjectExists, subjectWill}`. |
| `C494` | ⚠️ **AXIOMATIC** — rests on `necessaryPersonalSubjectExists` · [NecessaryKindAudit.lean#the_ground_is_not_the_only_necessary_being](formal/Logos/NecessaryKindAudit.lean#L139), footprint {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} | **The ground is not the only necessary being (C494)** — the refutation of *ST* I q.19 a.4 in its extensional reading. The claim that every property of God is shared by every necessary being is false: taking `Q := fun e = |
| `C495` | ⚠️ **AXIOMATIC** — rests on `necessaryPersonalSubjectExists` · [NecessaryKindAudit.lean#necessity_is_not_sole_bearer_of_the_ground](formal/Logos/NecessaryKindAudit.lean#L121), footprint {necessaryPersonalSubjectExists, Means, NecessarySubjectKind, Subject, Will, subjectWill} | **Necessity is not sole-bearer of the ground (C495).** No other characteristic in the corpus has this shape: `∀ e, NecessaryEntity e → e = Entity.ofGround` is **false**, because the META bridge `necessaryPersonalSubjectE |

## 12. One God, in Three Persons

**One God; three Persons; one nature.** Γ's result is not a unitarian monad and not a trinity of three gods: it is one ground, of one nature, in which there are three distinct divine Persons.

All three are divine of the *same* `divineReality` (`the_father_is_divine`, `the_beloved_is_divine`, `the_spirit_is_divine`). Distinctness is personal, not substantial: the Persons are separated, while one ground and one nature carry the unity.

This is the Catholic and Nicene reading — *unus Deus, tres Personae*: one divine being in three persons, consubstantial, distinguished by procession and not by essence. The author is a **Catholic**; this is the reading he reads Γ as supporting.

The faith supplies the Persons; the kernel prices them (C510 rests on three declared META premises) and proves at `{}` that it cannot supply them for free (C109).

**What this is not.** Not three Gods: one ground (C320/C389), one nature (C440, *actus purus*, aseity), one shared `divineReality`. And not that Γ *proves* the Trinity — it proves the three Persons on declared premises, and proves that the premises are needed.

| What it costs | What it settles | Derived status · footprint · source |
|---|---|---|
| **One ground** of reality | C320/C389: `∃! g, UniversalModalGround g`. Existence unconditional; uniqueness on the declared VOCAB bound `SemanticFinitude`. | ✅ **PROVEN** · 0 substantive axioms · `{Means, NecessarySubjectKind, Subject}` · [FoundationalUnicity.lean#exactly_one_universal_modal_ground](formal/Logos/FoundationalUnicity.lean#L301), footprint {Means, NecessarySubjectKind, Subject} |
| **One nature** (una natura, *actus purus*) | C440 divine simplicity as the sole bearer; aseity non-derived. 0 substantive axioms. | ✅ **PROVEN** · 0 substantive axioms · `{Means, Subject, CL}` · [DivineSimplicity.lean#divine_simplicity_sole_bearer](formal/Logos/DivineSimplicity.lean#L246), footprint {Means, Subject, CL} [CanonicalAseity.lean#conditional_canonical_aseity](formal/Logos/CanonicalAseity.lean#L133), footprint {Means, Subject} |
| **Three distinct Persons** | C510: `t.P1 = the_father ∧ t.P2 = the_beloved ∧ t.P3 = the_spirit ∧ IsWord the_beloved ∧ IsSpirit the_spirit`. **Priced on three declared META premises.** | ⚠️ **AXIOMATIC (AxAgapeEssence, AxProcessionSpirit, AxProcessionWord)** · `{Subject, AxAgapeEssence, AxProcessionSpirit, AxProcessionWord, CL}` · [DivineAgape.lean#agape_entails_tripersonality](formal/Logos/DivineAgape.lean#L331), footprint {AxAgapeEssence, AxProcessionSpirit, AxProcessionWord, Subject, CL} |
| All three are **God** (one `divineReality`) | Consubstantiality, the anti-tritheism half: `is_divine the_father divineReality ∧ is_divine the_beloved divineReality ∧ is_divine the_spirit divineReality`. Same price as C510. | ⚠️ **AXIOMATIC (AxAgapeEssence)** · `{Subject, AxAgapeEssence, AxProcessionSpirit, CL}` · [DivineAgape.lean#the_father_is_divine](formal/Logos/DivineAgape.lean#L274), footprint {AxAgapeEssence, Subject, CL} [DivineAgape.lean#the_beloved_is_divine](formal/Logos/DivineAgape.lean#L279), footprint {AxAgapeEssence, Subject, CL} [DivineAgape.lean#the_spirit_is_divine](formal/Logos/DivineAgape.lean#L284), footprint {AxAgapeEssence, AxProcessionSpirit, Subject, CL} |
| The Persons are **distinct** (not three gods) | Personal distinctness by personal property, not by essence: `≠` in every pair, and the Spirit is no word. | ⚠️ **AXIOMATIC (AxAgapeEssence)** · `{Subject, AxAgapeEssence, AxProcessionSpirit, AxProcessionWord, CL}` · [DivineAgape.lean#the_beloved_distinct](formal/Logos/DivineAgape.lean#L151), footprint {AxAgapeEssence, Subject, CL} [DivineAgape.lean#the_spirit_ne_father](formal/Logos/DivineAgape.lean#L210), footprint {AxAgapeEssence, AxProcessionSpirit, Subject, CL} [DivineAgape.lean#the_spirit_ne_beloved](formal/Logos/DivineAgape.lean#L218), footprint {AxAgapeEssence, AxProcessionSpirit, AxProcessionWord, Subject, CL} [DivineAgape.lean#the_spirit_ne_any_word](formal/Logos/DivineAgape.lean#L214), footprint {AxAgapeEssence, AxProcessionSpirit, Subject, CL} |
| **One Person** is forbidden | One ground, and every ground bears at least two distinct persons. The unitarian monad is a reading the countermodel forbids — which is why single-person monotheism is not merely unproven. | 🧱 **COUNTERMODEL | unicity_does_not_force_unitarian_monad ⇏ Independence** · `{}` · [FoundationalUnicity.lean#unicity_does_not_force_unitarian_monad](formal/Logos/FoundationalUnicity.lean#L317), footprint {} |
| The Trinity is **not free** | C109: the preceding theory does not entail three Persons. This is the price, stated as a countermodel. | 🧱 **COUNTERMODEL | preceding_theory ⇏ trinity** · `{}` · [ConditionalTheology.lean#preceding_theory_not_entails_trinity](formal/Logos/ConditionalTheology.lean#L336), footprint {} |
| The **Incarnation** is open | C112: the preceding theory is consistent with an unincarnate ground. The frontier, named. | 🧱 **COUNTERMODEL | preceding_theory ⇏ incarnation** · `{}` · [ConditionalTheology.lean#preceding_theory_not_entails_incarnation](formal/Logos/ConditionalTheology.lean#L380), footprint {} |

## 13. The Cremation — Every Branch of the Denial

Every branch of the denial is **derived dead on this page**: the premises it needs, the steps, and the `⊥` — or the negation of its own thesis.

Each block's price and kind are derived; where a priced route to the same death also exists, it is shown and priced separately.

Every line below is compiled from the Lean proof term. The branch, the objection, and which premise is *the thesis* are the only authored strings.

How a death is classified is derived from the audited goal and footprint, never typed: `⊥` when the goal is `False`; `⊘` when the derivation returns the denial's own negation.

💥 **COLLAPSE — INCOHERENT** when the denial, followed, destroys the very normativity it claims to keep (Euthyphro, and the D3–D6 family).

Three axes, because a countermodel makes three claims (C559): the **attack** (a derivability claim, which stands unless Γ derives the inference), the **model** (a description), and the world-datum ◈ `contingentWorldDatum`.

One former row is gone: “objectivity in a meaningless world”. Its theorem is `{}`, but its premises are `NegativeRetorsionSignature`, `S.NoI`, `S.EO` — a **free-signature artifact**, not a claim about a world (AGENTS.md, 2026-09-29).

Which models are wrong *given that the world exists*: WRONG outright (the no-meaning world, on the act datum), WRONG ONLY IF an axiom is insisted (plurality, love, choice bridges), NOT ESTABLISHED, or UNANSWERED. A signature model is never a candidate world.

The last three rows are **boundaries, not refutations**, and the second is a **win**: unicity does not force a single person, so “the ground is one person” is a consequence, not a gap.

Full normal forms: [Adversarial Denial Normal Forms (D1–D8), the catalogue, and the Pillars of formal defense](investigations/ledger.md).

**1. No right or wrong at all** — “There is no objective right and wrong.”

> **⊥ CONTRADICTION** — The Fundamental Diagonal Retorsion Theorem: Claiming NoRight as correct while NoRight is true produces a strict, constructive contradiction.

    Assume ClaimsCorrect(s, NoRight)  ← voicing the denial as correct
    Assume NoRight  ← the denial's own thesis
      1. Act s NoRight  (elimination of 1 from hClaim)
      2. Correct(s, NoRight)  (instantiation of Logos.Order.Correct from hAct, hTrue)
      3. NormativeRightExists  (existential introduction with witness s)
    ⊥

> ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, State, Subject}`
✅ · [DirectNormativeRetorsion.lean#claims_correct_no_right_self_refuting](formal/Logos/DirectNormativeRetorsion.lean#L60)

**2. No meaning** — “Reality is brute; nothing is meant.”

> **⊥ CONTRADICTION** — Dialectical Retorsion: Any skeptic attempting to deny objective correctness in formal derivations by claiming normative nihilism (`NoRight`) refutes itself constructively.

    Assume ClaimsCorrect(s, NoRight)  ← voicing the denial as correct
    Assume NoRight  ← the denial's own thesis
    ⊥

> ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, State, Subject}`
✅ · [ProofPresentationRetorsion.lean#proof_criticism_nihilism_self_refuting](formal/Logos/ProofPresentationRetorsion.lean#L199)

> A free-signature model is a separate, secondary result: it is a statement about an uninterpreted field, not about a state of affairs.

**3. No subject; the empty world** — “There is no one here.”

> **⊥ CONTRADICTION** — C57: Retorsion — asserting that no subject exists refutes itself.

    Assume Asserts speaker NoSubject  ← the denial's own thesis
      1. Act speaker NoSubject  (modus ponens via assertion_is_act)
      2. SubjectExists(speaker)  (modus ponens via act_requires_subject)
    ⊥

> ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, State, Subject}`
✅ · [Agency.lean#noSubject_performative_selfRefutes](formal/Logos/Agency.lean#L465)

**4. No act — everything is mechanical** — “No one acts; there are only events.”

> **⊥ CONTRADICTION** — Asserting NoAct refutes itself under a weak assertion ONLY given the bridge from weak act to strong Act.

    Assume weak_act_implies_strong_act
    Assume asserts speaker NoAct  ← the denial's own thesis
    ⊥

> ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, State, Subject, act}`
✅ · [Agency.lean#noAct_conditional_selfRefutes](formal/Logos/Agency.lean#L406)

**5. No choice (eliminativism)** — “Normative address does not imply genuine choice.”

> **⊥ CONTRADICTION** — D7: Denial of Choice from Co-Grasp — denying Chooses when incompatible alternatives are co-grasped is a direct formal contradiction.

    Assume Means(s, p)
    Assume Means(s, q)
    Assume Incompatible(p, q)
    Assume ¬Chooses(s, p, q)  ← the denial's own thesis
    ⊥

> ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
✅ · [UndeniableNormativeDerivation.lean#d7_co_grasp_is_definitionally_choice](formal/Logos/UndeniableNormativeDerivation.lean#L267)

**6. No choice (determinism)** — “Freedom requires physical indeterminism.”

> **⊥ CONTRADICTION** — D8: Denial of Free Will from Choice — denying FreeWill when Chooses obtains is a direct formal contradiction.

    Assume Chooses(s, p, q)
    Assume ¬FreeWill(s)  ← the denial's own thesis
    ⊥

> ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
✅ · [UndeniableNormativeDerivation.lean#d8_choice_is_definitionally_free_will](formal/Logos/UndeniableNormativeDerivation.lean#L275)

**7. Normativity is stipulative** — “Moral norms are just stipulations.”

> **⊥ CONTRADICTION** — Non-vacuous self-refutation of the denial of GenuineNormativity under the normative correctness stance.

    Assume ClaimsNormativeCorrectness(s, NoGN)  ← voicing the denial as correct
    Assume NoGN  ← the denial's own thesis
      1. GenuineNormativityExists  (existential introduction with witness s)
    ⊥

> ✅ **PROVEN** — 0 substantive axioms · `{Initiates, Means, State, Subject, choice, propext, sound}`
✅ · [RetorsiveNormativity.lean#normative_denial_of_normativity_is_self_refuting](formal/Logos/RetorsiveNormativity.lean#L193)

**Normativity is stipulative — a second, priced route**

> **⊥ CONTRADICTION** — Non-vacuous self-refutation of the denial of GenuineNormativity.

    Assume ClaimsCorrect(s, NoGN)
    Assume NoGN  ← the denial's own thesis
      1. GenuineNormativity s NoGN (¬NoGN)  (from )
      2. GenuineNormativityExists  (existential introduction with witness s)
    ⊥

> ⚠️ **AXIOMATIC (AxJudicativeBipolarity)** — 1 substantive axiom: AxJudicativeBipolarity · `{AxJudicativeBipolarity, Initiates, Means, State, Subject}`
⚠️ AxJudicativeBipolarity · [RetorsiveNormativity.lean#denial_of_genuine_normativity_is_self_refuting](formal/Logos/RetorsiveNormativity.lean#L138)
> A second, independently sufficient refutation — but priced on one SEM choice (`AxJudicativeBipolarity`), so the free route is the one read above.

**8. Voluntarism (Euthyphro)** — “Ought is just will; the person invents morality.”

> **⊥ CONTRADICTION** — Performative Incoherence of Asserting Self-Legislation.

    Assume Ought(s, s, a)  ← the denial's own thesis
    Assume SelfLegislation(s)
    Assume SubjectWills(s, a).neg
    Assume SubjectWills(s, a).neg → ¬SubjectWills(s, a)
    ⊥

> ✅ **PROVEN** — 0 substantive axioms · `{Ought, Subject, Wills}`
✅ · [OughtRetorsion.lean#self_grounded_assertion_incoherent](formal/Logos/OughtRetorsion.lean#L129)

**Voluntarism (Euthyphro) — the collapse itself**

> **COLLAPSE — INCOHERENT** — Volition Is Not Normative Ground by Identity: Identifying practical obligation with the subject's own current willing (`SelfLegislation s`) destroys the logical possibility of normative violation, collapsing normativity.

    Assume SelfLegislation(s)
    Assume PracticalAction
    Assume ∀ r, Ought(r, s, a) → r = s  ← the denial's own thesis
    Assume SubjectWills(s, a).neg → ¬SubjectWills(s, a)
    NormativeViolation(s, a) → False  — the denial, followed, destroys what it claims to keep

> ✅ **PROVEN** — 0 substantive axioms · `{Ought, Subject, Wills}`
✅ · [PersonalNormativeGround.lean#will_identity_collapses_normativity](formal/Logos/PersonalNormativeGround.lean#L347)

**9. Descriptivism (D3)** — “Truth is only descriptive; there is no deontic guidance at all.”

> **⊘ DENIAL REFUTED** — D3: Denial of Prescriptivity — asserting that Right/Wrong is merely descriptive truth lacks deontic guidance and is refuted by genuine normativity.

    Assume hDescriptiveOnly → ∀ s, ¬AgentialDeonticAddress(s, p, q)  ← the denial's own thesis
    Assume ∃ s, GenuineNormativity s p q
      1. assume hDesc  (hypothesis assumption for conditional/reductio proof)
      2. witness components ⟨s, hNormInst⟩  (existential elimination from hNorm)
    ⊘ ¬hDescriptiveOnly  — the denial's own negation

> ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
✅ · [UndeniableNormativeDerivation.lean#d3_descriptive_truth_lacks_deontic_guidance](formal/Logos/UndeniableNormativeDerivation.lean#L233)

**10. Impersonal normativity (D4)** — “An ought can bind no one; normativity needs no subject.”

> **COLLAPSE — INCOHERENT** — D4: Denial of Agential Address — impersonal ought without an addressed subject fails relationality.

    Assume ∀ s, ¬AgentialDeonticAddress(s, p, q)  ← the denial's own thesis
    ¬∃ s, GenuineNormativity s p q  — the denial, followed, destroys what it claims to keep

> ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
✅ · [UndeniableNormativeDerivation.lean#d4_impersonal_normativity_fails_relationality](formal/Logos/UndeniableNormativeDerivation.lean#L244)

**11. Monolithic command (D5)** — “A command with no alternative is still a command.”

> **COLLAPSE — INCOHERENT** — D5: Denial of Incompatible Alternatives — a monolithic command without opposition lacks choice.

    Assume ∀ q, ¬Incompatible(p, q)  ← the denial's own thesis
    ¬∃ s, q, GenuineNormativity s p q  — the denial, followed, destroys what it claims to keep

> ✅ **PROVEN** — 0 substantive axioms · `{Subject}`
✅ · [UndeniableNormativeDerivation.lean#d5_monolithic_command_lacks_opposition](formal/Logos/UndeniableNormativeDerivation.lean#L252)

**12. Ungraspable command (D6)** — “A command nobody can grasp is still a command.”

> **COLLAPSE — INCOHERENT** — D6: Denial of Cognitive Grasp — an ungraspable command fails agential address.

    Assume ¬(Means(s, p) ∧ Means(s, q))  ← the denial's own thesis
      1. ¬AgentialDeonticAddress(s, p, q)  (definitional identity via hUngraspable)
    ¬AgentialDeonticAddress(s, p, q)  — the denial, followed, destroys what it claims to keep

> ✅ **PROVEN** — 0 substantive axioms · `{Means, Subject}`
✅ · [UndeniableNormativeDerivation.lean#d6_ungraspable_command_fails_agential_address](formal/Logos/UndeniableNormativeDerivation.lean#L259)

| Branch of the denial | The objection | How it is stopped (derived) | Status · footprint · source |
|---|---|---|---|
| **The ground is just an atom** | “The ultimate ground is a particle.” | 🧱 **COUNTERMODEL · ⇏** — A countermodel is a **boundary**: it says the reading cannot ground the ground, not that the reading is incoherent. | ✅ **PROVEN** · 0 substantive axioms · `{Means, Subject}` · [CanonicalAseity.lean#atom_cannot_ground_the_ground](formal/Logos/CanonicalAseity.lean#L96), footprint {Means, Subject} |
| **The ground is a *single* Person** | “One God = one person, full stop.” | 🧱 **COUNTERMODEL · ⇏** — Refuted **as a consequence**: one ground, and every ground bears at least two distinct persons. This is why single-person monotheism is not merely unproven (§14). | 🧱 **COUNTERMODEL | unicity_does_not_force_unitarian_monad ⇏ Independence** · `{}` · [FoundationalUnicity.lean#unicity_does_not_force_unitarian_monad](formal/Logos/FoundationalUnicity.lean#L317), footprint {} |
| **A free subject's existence is open** | “No one has shown a free subject exists.” | ⌐ **DEFINITIONAL FALLACY** — Row SUPERSEDED in GAPMAP (`F1bUncond`): C278 already proved it, and the corollary `freeSubject_exists` extends it to the `FreeSubject` name at the same price. | ⚠️ **AXIOMATIC (AxTwoSubjects)** · `{Initiates, Means, State, Subject, Will, subjectWill, AxTwoSubjects}` · [AsieticChoice.lean#freeWill_exists](formal/Logos/AsieticChoice.lean#L472), footprint {AxTwoSubjects, Means, Subject, Will, subjectWill} [EpistemicNecessity.lean#epistemic_order_makes_the_act_datum_necessary](formal/Logos/EpistemicNecessity.lean#L235), footprint {Initiates, Means, State, Subject} |

## 14. What the Instrument Cannot See

`#print axioms` reads the kernel's dependency graph. It cannot see a **`def` used as a premise by name** — so the census below counts every such inherited bridge, the theorems it underwrites, and how many have been reviewed.

A `✅` therefore means *kernel-verified conditional on a bridge the kernel does not charge*.

This is disclosure, not payment: nothing is promoted to a declared axiom, and the three-way decision (promote / declare / retire) is still open.

`EntityMeans Entity.ofGround := True` — the irrelevance of causal contact to the grounding of §8 — is one of them.

| Declared-`def` bridges | Theorems they underwrite | Reviewed | Promoted to a declared axiom |
|---|---|---|---|
| **28** | **53** (largest: 7) | **0** | **0** |

Full census with each bridge, its dependents and its justification: [investigations/ledger.md](investigations/ledger.md); the open three-way decision is tracked by `scripts/census_stipulated_defs.py`.

## 15. What Is Not Established

**Single-person monotheism is not on this list, because it is refuted rather than open** (§12): one ground, and every ground bears at least two distinct persons.

What remains open is the **entity-level** projection C228 (`GenericGroundsRightWrong g → PersonalEntity g`), still `BLOCKED` — a different question, and not what stands between Γ and monotheism.

**Trinity is priced, not free** (§12): three Persons on three declared META premises, with C109 at `{}`. **Incarnation is open** (C112, `{}`).

**The Incarnation is the open frontier.** C112 (`preceding_theory_not_entails_incarnation`, `{}`): the preceding theory is consistent with an unincarnate ground. C111 shows the *structure* is available; the *entailment* is not.

Contingent creation *as existence* is a free theorem (C350, `{}`); only the realm's content is priced (C367). Nothing above should be read as claiming any of it.

| Claim | Derived status | What it settles |
|---|---|---|
| `C109` | DEMOTED **DEMOTED** · [ConditionalTheology.lean#preceding_theory_not_entails_trinity](formal/Logos/ConditionalTheology.lean#L336), footprint {} | Binitarian Separation Model (Toy Cardinality Model over Bool): Demonstrates that an unconstrained 2-element domain (`Subj := Bool`) cannot accommodate three distinct personal centers by pure cardinality (Pigeonhole Princ |
| `C112` | 🧱 **COUNTERMODEL** · [ConditionalTheology.lean#preceding_theory_not_entails_incarnation](formal/Logos/ConditionalTheology.lean#L380), footprint {} | Unincarnate Hostile Model: The existing theory (necessary divine ground, human agency, free will) is completely consistent with God remaining purely transcendent and unincarnate. |
| `C151` | ✅ **PROVEN** · [PersonalGroundOfReality.lean#the_person_supports_the_reality_of_right](formal/Logos/PersonalGroundOfReality.lean#L153), footprint {Initiates, Means, State, Subject, Will, subjectWill, will_individuation, CL} | HEADLINE — THE PERSON SUPPORTS THE REALITY OF RIGHT. |
| `C228` | ✖ **BLOCKED** · [PersonalNormativeGround.lean#normative_ground_is_personal](formal/Logos/PersonalNormativeGround.lean#L262), footprint {Means, Subject, Will, subjectWill} | BLOCKED (AC5 unmet, D1′ recorded not executed): any entity that grounds Right/Wrong is a Personal Entity — but the personalness is a THREE-STEP FIELD PROJECTION, not a free-standing theorem: `grounds_normativity` supplie |
| `C320` | ✅ **PROVEN** · [FoundationalUnicity.lean#exactly_one_universal_modal_ground](formal/Logos/FoundationalUnicity.lean#L301), footprint {Means, NecessarySubjectKind, Subject} | Master Synthesis (existential form): exactly one universal modal ground exists. |
| `C350` | ✅ **PROVEN** · [CosmicExistence.lean#contingent_realm_obtains](formal/Logos/CosmicExistence.lean#L269), footprint {NecessarySubjectKind, Subject, CL} | Contingency-overflow: something obtains, is modal-fragile, and is not the necessary ground — and Γ derives it outright, resting on nothing substantive. |
| `C367` | ✅ **PROVEN** · [CosmicExistence.lean#cosmos_obtains](formal/Logos/CosmicExistence.lean#L416), footprint {Means, NecessarySubjectKind, Subject, Will, subjectWill, CL} | **The cosmos exists** — a contingent created realm, not the necessary ground, actually obtains and bears content of its own — given a *contingent* person. |
| `C440` | ✅ **PROVEN** · [DivineSimplicity.lean#divine_simplicity_sole_bearer](formal/Logos/DivineSimplicity.lean#L246), footprint {Means, Subject, CL} | C440 — the attributes-table form: the ground is the sole bearer of Divine Simplicity, stated together with the existence half so a reader-facing row can cite a single declaration. This is the §13 Simplicity analogue of C |
| `C510` | ⚠️ **AXIOMATIC** — rests on `AxAgapeEssence`, `AxProcessionSpirit`, `AxProcessionWord` · [DivineAgape.lean#agape_entails_tripersonality](formal/Logos/DivineAgape.lean#L331), footprint {AxAgapeEssence, AxProcessionSpirit, AxProcessionWord, Subject, CL} | Agape entails tripersonality (C510, PROVEN↑): under the three disclosed Agape axioms — the datum, the procession of the Word, the procession of the Spirit — there is a `TrinitarianStructure` (C108) on the divine sort who |

---

**32 formal frontiers** — every unproved step, every countermodel separation and every open bridge, with its exact missing lemma — are listed in [investigations/ledger.md](investigations/ledger.md). Nothing in that list is established; nothing in this file claims otherwise.

## What Is Established of the Ground, and of the Person

Every row derived from the kernel, never transcribed (icons as in the legend above; `◈` = a registered `def`-as-premise, a price not a warning).

Two rows cut **against** the classical reading and are kept here: the ground is **not the only necessary being** (C494), so necessity does **not** pick the ground out (C495).

| Classical characteristic | Scope | Derived status |
|---|---|---|
| **Personal** — the ground-type is personal | Personal ground / person-type | ✅ PROVEN · [PersonalGroundOfReality.lean#personal_ground_of_right_wrong](formal/Logos/PersonalGroundOfReality.lean#L100), footprint {Means, Subject, Will, subjectWill, will_individuation} |
| **Personal** — the epistemic sibling: the ground-type is personal *at the epistemic poles* | Personal ground / person-type | ✅ PROVEN · [EpistemicPersonalGround.lean#epistemic_ground_is_personal](formal/Logos/EpistemicPersonalGround.lean#L133), footprint {Initiates, Means, State, Subject, Will, subjectWill, will_individuation} |
| **Psychological personality** (humanoid consciousness, stream of experience) | Personal ground / person-type | 🧱 INDEPENDENT · [PersonhoodOntologyAudit.lean#faithful_model_satisfies_free_will_without_opaque_person](formal/Logos/PersonhoodOntologyAudit.lean#L182), footprint {} |
| **Rational** — formally equivalent to the Thomistic core containing RationalNature | Personal ground / person-type | ✅ PROVEN · [Person.lean#person_iff_thomisticCore](formal/Logos/Person.lean#L183), footprint {Means, Subject, Will, subjectWill} |
| **Free** — genuine normativity yields genuine choice and free will | Personal ground / person-type | ✅ PROVEN · [IndubitableNormativeFreeWill.lean#indubitable_normative_free_will](formal/Logos/IndubitableNormativeFreeWill.lean#L115), footprint {Means, Subject} |
| **Asiety** — true freedom (true choice) | Personal ground / person-type | ⚠️ AXIOMATIC · [AsieticChoice.lean#asietic_summary](formal/Logos/AsieticChoice.lean#L563), footprint {AxJudicativeBipolarity, AxTwoSubjects, Initiates, Means, State, Subject, Will, subjectWill} |
| **Shared freedom of the ground** (`AsietyFreedom` — the ground's freedom, shared) | Divine Being / Ground | ✅ PROVEN ◈ · [AsietyFreedom.lean#asietyFreedom_summary](formal/Logos/AsietyFreedom.lean#L296), footprint {Means, Subject} |
| **Divine love** (the ground as lover of contingent reality) | Divine Being / Ground | ⚠️ AXIOMATIC · [LovesAsGround.lean#the_ground_is_a_necessary_and_chosen_lover](formal/Logos/LovesAsGround.lean#L580), footprint {AxGroundLovesContingentRealm, GroundBearsGood, Means, NecessarySubjectKind, Subject, CL} |
| **Independent will** — with numerical individuation | Personal ground / person-type | ✅ PROVEN · [Person.lean#person_iff_freeIndependentWill](formal/Logos/Person.lean#L166), footprint {Means, Subject, Will, subjectWill} |
| **Dominion over acts** / authoritative personhood | Personal ground / person-type | ✅ PROVEN · [Person.lean#DominionOverActs](formal/Logos/Person.lean#L56), footprint {Means, Subject} |
| **Ground of objective normativity (Right and Wrong)** | Personal ground / person-type | ✅ PROVEN · [PersonalNormativeGround.lean#person_grounds_normative_polarity](formal/Logos/PersonalNormativeGround.lean#L529), footprint {Means, Subject, Will, subjectWill} |
| **Non-relative core** — strict architectural invariance only | Proof architecture (not divine scope) | ✅ PROVEN · [HardenedInvariance.lean#agent_invariant_core_is_strictly_inside_freewill_invariant_core](formal/Logos/HardenedInvariance.lean#L226), footprint {} |
| **Necessary Divine Being / Ground** | Divine Being / Ground | ✅ PROVEN ◈ · [NecessityEternity.lean#ofGround_necessary_ground_of_reality](formal/Logos/NecessityEternity.lean#L161), footprint {Means, NecessarySubjectKind, Subject} |
| **Aseity** — non-derived / non-dependent | Divine Being / Ground | ✅ PROVEN · [CanonicalAseity.lean#conditional_canonical_aseity](formal/Logos/CanonicalAseity.lean#L133), footprint {Means, Subject} |
| **Foundational unicity** (structural unicity of the universal ground of reality) | Divine Being / Ground | ✅ PROVEN · [FoundationalUnicity.lean#ofGround_foundational_unicity](formal/Logos/FoundationalUnicity.lean#L215), footprint {Means, NecessarySubjectKind, Subject, CL} |
| **Strict monotheism** (the ground is a *single* Person — a unitarian monad) | Divine Being / Ground | 🧱 INDEPENDENT · [FoundationalUnicity.lean#unicity_does_not_force_unitarian_monad](formal/Logos/FoundationalUnicity.lean#L317), footprint {} |
| **One God** — unity of the Divine Being (one ground, one nature) | Divine Being / Ground | ✅ PROVEN · [FoundationalUnicity.lean#exactly_one_universal_modal_ground](formal/Logos/FoundationalUnicity.lean#L301), footprint {Means, NecessarySubjectKind, Subject} |
| **Perfect (moral) goodness** | Divine Being / Ground | 🧱 INDEPENDENT · — |
| **Eternal — ever-present** (everlasting existence) | Divine Being / Ground | ✅ PROVEN ◈ · [NecessityEternity.lean#the_ground_everlasting](formal/Logos/NecessityEternity.lean#L195), footprint {NecessarySubjectKind, Subject} |
| **Atemporal** (existence not time-modulated; outside succession) | Divine Being / Ground | ✅ PROVEN ◈ · [NecessityEternity.lean#the_ground_atemporal](formal/Logos/NecessityEternity.lean#L199), footprint {NecessarySubjectKind, Subject} |
| **Precedence to Right/Wrong** (the ground precedes the true/false distinction) | Divine Being / Ground | ✅ PROVEN · [Precedence.lean#ofGround_precedes_the_right_wrong_distinction](formal/Logos/Precedence.lean#L263), footprint {Means, NecessarySubjectKind, Subject} |
| **Exclusion of pantheism** (the ground is not the universe) | Divine Being / Ground | ✅ PROVEN · [CosmicExistence.lean#the_ground_is_not_the_universe](formal/Logos/CosmicExistence.lean#L739), footprint {NecessarySubjectKind, Subject} |
| **Divine simplicity** | Divine Being / Ground | ✅ PROVEN ◈ · [DivineSimplicity.lean#divine_simplicity_sole_bearer](formal/Logos/DivineSimplicity.lean#L246), footprint {Means, Subject, CL} |
| **Ontological transcendence** (neither an atomic worldly state nor any subject-correlate) | Divine Being / Ground | ✅ PROVEN · [DivineTranscendence.lean#ofGround_sole_transcendent_ground](formal/Logos/DivineTranscendence.lean#L317), footprint {Subject} |
| **Scholastic simplicity** (strict identity of essence and existence) | Divine Being / Ground | ❌ NOT ESTABLISHED · — |
| **Divine immutability** (ontological, temporal, and process unchangeability) | Divine Being / Ground | ✅ PROVEN · [DivineImmutability.lean#ofGround_divine_immutability](formal/Logos/DivineImmutability.lean#L213), footprint {Initiates, Means, NecessarySubjectKind, State, Subject} |
| **Psychological impassibility** (incapacity for relational affect or compassion) | Divine Being / Ground | ❌ NOT ESTABLISHED · — |
| **Foundational omnipresence** (sustaining presence to all beings across modal reality) | Divine Being / Ground | ✅ PROVEN · [FoundationalOmnipresence.lean#ofGround_foundational_omnipresence](formal/Logos/FoundationalOmnipresence.lean#L154), footprint {Means, NecessarySubjectKind, Subject} |
| **Physical omnipresence** (spatial presence throughout physical spacetime coordinates) | Divine Being / Ground | ❌ NOT ESTABLISHED · — |
| **Quantitative metric infinity** (infinite physical magnitude or cardinal size) | Divine Being / Ground | ❌ NOT ESTABLISHED · — |
| **Divine pure actuality** (*Actus Purus* / perfection) | Divine Being / Ground | ✅ PROVEN · [DivinePureActuality.lean#ofGround_divine_pure_actuality](formal/Logos/DivinePureActuality.lean#L195), footprint {Initiates, Means, NecessarySubjectKind, State, Subject} |
| **Physical / kinetic energy** (thermodynamic or kinetic physical motion) | Divine Being / Ground | ❌ NOT ESTABLISHED · — |
| **Foundational omniscience** (truth-exhaustive scope — the condition of all truth) | Divine Being / Ground | ✅ PROVEN ◈ · [DivineOmniscience.lean#ofGround_foundational_omniscience](formal/Logos/DivineOmniscience.lean#L200), footprint {Means, NecessarySubjectKind, Subject} |
| **Infallible / counterfactual omniscience** ("all and only truths", ordinary knowledge of all truth) | Divine Being / Ground | ❌ NOT ESTABLISHED ◈ · — |
| **Foundational omnipotence** (operative scope: no non-contradictory state of affairs is closed to the ground) | Divine Being / Ground | ✅ PROVEN ◈ · [DivineOmnipotence.lean#ofGround_foundational_omnipotence](formal/Logos/DivineOmnipotence.lean#L306), footprint {Means, NecessarySubjectKind, Subject, CL} |
| **Causal / creative omnipotence** ("can bring X about", not "is present where X obtains") | Divine Being / Ground | ◆ AXIOM · [ThomisticAct.lean#ground_produces_every_satisfiable_form](formal/Logos/ThomisticAct.lean#L247), footprint {ground_produces_every_satisfiable_form, Produces, Subject} |
| **Creator of contingent reality** | Divine Being / Ground | 🧱 INDEPENDENT · [ConditionalTheology.lean#necessary_ground_not_entails_contingent_creation](formal/Logos/ConditionalTheology.lean#L616), footprint {} |
| **Three Divine Persons (Trinity)** — one God, in three Persons | Divine Personhood | ⚠️ AXIOMATIC · [DivineAgape.lean#agape_entails_tripersonality](formal/Logos/DivineAgape.lean#L331), footprint {AxAgapeEssence, AxProcessionSpirit, AxProcessionWord, Subject, CL} |
| **Incarnation** | Divine Personhood | 🧱 INDEPENDENT · [ConditionalTheology.lean#preceding_theory_not_entails_incarnation](formal/Logos/ConditionalTheology.lean#L380), footprint {} |

The full prose for every row — the exact sense established, every reference, and the 14 step-by-step chain blocks that price each bridge — is in [investigations/ledger.md](investigations/ledger.md).

## Where the Rest of the Ledger Lives

| What was moved out of the reading path | Where it lives |
|---|---|
| Every natural-deduction proof (40 blocks), the 14 step-by-step chain blocks (206 rows), the 39 classical-attribute rows with full prose, the ASCII flowchart, and the full per-step prose | [investigations/ledger.md](investigations/ledger.md) |
| 100 retorsion theorems, the independence-frontier catalogue, the countermodel catalogue and the investigation index | [investigations/catalogues.md](investigations/catalogues.md) |
| The complete kernel audit, the axiom inventory (all 35, with tags and dependents), the dependency ledger, the consistency checks and the code annex | [investigations/kernel-audit.md](investigations/kernel-audit.md) |

Generated, not editorial: one pass over the kernel emits both files, and the superset check fails the build if anything is missing from their union. Plan of record: [READINGPATH.md](READINGPATH.md).
