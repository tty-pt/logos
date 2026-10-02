# ISSUES.md — handoff for the next context

Read this first. It is a **review of the reading path** (`README.md`) against the
kernel, plus a review of **my own review**. Nothing here has been changed yet.
Every claim is cited to `file:line` so it can be re-checked in one grep.

**User's four constraints, in force:**
1. Fix as many issues as possible.
2. Most characteristics must remain `PROVEN`.
3. Preferably: omniscience **not** refuted; the ground **not** vacuous.
4. The "thing that worries me" (issue **B**) must be *treated*, but never stated in a
   way that makes it **false** — because it is **true**.

---

## 0. Read this before trusting anything below

`AGENTS.md` records that in this project *"Six eye-checked spot-checks were all wrong
and one had a truncated string's tail filled in by hand"*, and that four assertions
added while fixing them were *themselves* wrong. `STUPID_SIMON_SAYS.md` is the
resulting post-mortem.

**This file is an eye-check.** It was produced by reading, not by `#print axioms`,
not by a probe, and not by `lake env lean`. On this project's own prior, the majority
of its confident claims are *probably wrong*. The corpus has repeatedly been more
careful than its reviewer.

So this document is written as a list of **questions to settle**, not defects to fix.
Every issue below carries:

- **The observation** — the fact on disk, re-checkable by grep.
- **What I concluded** — my inference, which is the fallible part.
- **What would settle it** — the command or proof that decides it.
- **A prior warning** — the reason I might be wrong.

The highest-value item in this file is not an issue at all. It is **§H**, a finding
the corpus does not have, which is derivable in one line and states something the
whole `DivineOmniscience` module is built around. See §H.

**Plan-doc convention (added 2026-10-02):** when an issue below is actively being
fixed, it gets its own `ISSUE_<letter>_PLAN.md` at repo root — the full plan,
rationale, and execution log live there, and this file keeps only a short summary
plus a pointer and a resolution date. This file stays the index; the plan docs are
the audit trail. See `ISSUE_C_PLAN.md` for the first one.

---

## Executive summary

The corpus is honest and, in most places I checked, *more* careful than I assumed.
My first pass overstated the problems. Corrected findings:

- **A (narrowed, then widened again — see A2b).** `EntityMeans (ofGround) p := True`
  (`RecoveredOntologicalGround.lean:46`) is real, load-bearing, and **already
  disclosed in README.md:1659** — my first pass said it was not. What is genuinely
  thin is not the predicate's *power to discriminate* (it discriminates fine, see A2)
  but the **ground's own positive grounding obligation**, which is `True` by
  construction. **There is a second, independent root** — `EntityExistsAt` — which
  underwrites C319 itself ("the ground is necessary," characteristic #1). The corpus
  has its own machine-audited registry for both (`Stipulations.lean`,
  `scripts/audit_stipulations.py`), which is more authoritative than my grep — and
  even that registry under-counts by at least two theorems I found by hand. Current
  floor: **15 affected theorems, not 4.**
- **B (standing).** C556's conclusion is a field of its own signature. **It is true
  and stays true.** The missing piece is a `{}` **separation** proving the field is
  not free — which would make the result *stronger*, not weaker.
- **C — RESOLVED 2026-10-02.** `¬ PersonCorrelate Entity.ofGround` (`ofGround_not_a_person_correlate`,
  `CosmicExistence.lean:673`) was `PROVEN` and unledgered. Now ledgered as **C564**; the
  three conflating README/ledger sentences rewritten; see `ISSUE_C_PLAN.md` for the
  full fix (which also included a scoped rename pass and a `base.txt` backfill found
  while doing it).
- **H (new).** `TruthTracking` is satisfied *vacuously by every atom* and refuted of
  the ground. Stated nowhere. This is not a defect — it is a publishable boundary
  result, and it is the honest way to satisfy constraint 3.

---

## A. `EntityMeans (ofGround) := True` — real; narrower than my first draft, wider than my second (see A2b)

### A1. The definition

`formal/Logos/RecoveredOntologicalGround.lean:46-50`, **duplicated verbatim** at
`formal/Logos/NecessaryPersonalGround.lean:164-168`:

```lean
def EntityMeans (e : Entity) (p : Prop) : Prop :=
  match e with
  | Entity.ofSubject s => Means s p
  | Entity.ofAtom _ => False
  | Entity.ofGround => True        -- the ground theory hangs here
```

The second copy's docstring is honest: *"semantic stipulation … the `.ofGround`
meaning-everything branch is a definitional stipulation of the world-rigid
constructor."* Two copies of the load-bearing definition is a real maintenance hazard
for any fix — settle which is canonical first.

### A2. What it actually makes vacuous — corrected

`OneEssence g e := ∀ p, EntityMeans e p → EntityMeans g p`
(`RecoveredOntologicalGround.lean:57`). At `g = ofGround` the consequent is `True`, so
**`OneEssence ofGround _` holds for every `e`** — this is the vacuous obligation.

**My first pass was wrong to say the affected predicates cannot discriminate.** They
discriminate well, because the *other* arms are restrictive:

| Exclusion theorem | Loc | Footprint |
|---|---|---|
| `finite_entity_fails_omnipresence` | `FoundationalOmnipresence.lean:188` | `{}` |
| `discriminating_subject_not_undivided` | `DivineSimplicity.lean:126` | — |
| `atom_not_truth_exhaustive` | `DivineOmniscience.lean:155` | `{Means, Subject}` |
| `discriminating_subject_not_truth_exhaustive` | `DivineOmniscience.lean:164` | `{Means, Subject}` |
| `no_atom_is_universal_modal_ground` | `FoundationalUnicity.lean:158` | — |

So exclusivity is genuinely proved. The correct narrow claim is:

> The *exclusion* results are sound. The *ground's positive grounding obligation* is
> `True` by construction, and the rows discharged by `trivial` / `True.intro` /
> `Iff.rfl` are the ones whose content is that obligation.

The three at risk, and no others, are:

| Row | Discharge | Loc |
|---|---|---|
| `ofGround_universal_modal_ground` | `exact Or.inr (fun _p _hEM => True.intro)` | `FoundationalOmnipresence.lean:73` |
| `ofGround_maximal_capacity` | `intro _p; trivial` | `FoundationalOmnipresence.lean:127` |
| `ofGround_undivided_meaning` | `dsimp [EntityMeans]; exact Iff.rfl` | `DivineSimplicity.lean:120` |

Plus `ofGround_capacity_invariance`, discharged `exact Iff.rfl`
(`DivineImmutability.lean:147`), where `CapacityInvariance` reduces to `P ↔ P` because
`EntityMeans` takes no world argument — `capacity_invariance_holds_for_every_entity`
(`:180`) proves it holds of **every** entity. This one is already ledgered as C321/F16
(`base.txt:1438`).

**That is an enumerable list of four, not "Part II might collapse."** Constraint 2 is
much safer than I implied.

**CORRECTION (verified in build mode, below): this list is not complete. There is a
second, independent vacuity root, and the corpus has its own authoritative registry
for both — which I should have used instead of hand-deriving a list. See A2b.**

### A2b. A second root: `EntityExistsAt`, and the corpus's own registry (found after this file was first written)

`Entity.lean:63-66`:

```lean
def EntityExistsAt (w : World) : Entity → Prop
  | Entity.ofSubject s => SubjectExistsAt w s
  | Entity.ofAtom n => w n = Logos.Semantics.TV.t
  | Entity.ofGround => True
```

Same shape as `EntityMeans`, same match, same `True` on the ground arm — but this one
governs **existence**, not meaning-capacity. `NecessaryEntity e := ∀ w, ExistsAt w e`
(`Modal.lean:28`), so `ofGround_necessary : NecessaryEntity Entity.ofGround`
(`NecessityEternity.lean:145`) is discharged by `intro w; trivial`. **This is C319 —
"the ground is necessary" — characteristic #1, the flagship of Part II.** And
`NecessaryGroundOfReality := ⟨NecessaryEntity, GroundOfReality⟩`
(`RecoveredOntologicalGround.lean:93-95`) — so the headline "Necessary Divine Being /
Ground" row rests on **both** `True`-arms at once, one per conjunct.

**I did not have to hand-derive this.** `formal/Logos/Stipulations.lean` is a small,
rigorous, machine-audited registry of **exactly six** such stipulations, each with a
`Tag`, a `cost` sentence, and a **dependents list** — and `scripts/audit_stipulations.py`
verifies every dependent name actually exists in `formal/depgraph.json`
(`python3 scripts/audit_stipulations.py` → *"6 stipulations, 28 dependents verified"*,
writing `formal/stipulation_audit.json`). The two relevant entries:

```
ofGround_existsAt  (Entity.lean:66, Tag VOCAB)
  "Philosophical cost: every 'necessary existence' theorem about ofGround unfolds
   this True. Necessity of the ground is therefore stipulated by the constructor's
   match arm, never derived and never declared as an axiom."
  dependents: ofGround_necessary, the_ground_everlasting, the_ground_atemporal,
    everlasting_and_atemporal_ground, ofGround_necessary_ground_of_reality,
    ofGround_gapless_operative_scope, ofGround_foundational_omnipotence        (7)

ofGround_meansAll  (RecoveredOntologicalGround.lean:50, Tag VOCAB)
  dependents: ofGround_ground_of_reality, ofGround_undivided_meaning,
    ofGround_necessary_ground_of_reality, ofGround_truth_exhaustive,
    ofGround_world_truth_exhaustive, ofGround_not_truth_tracking,
    ofGround_foundational_omniscience                                          (7)
```

Union (one theorem, `ofGround_necessary_ground_of_reality`, is shared): **13 unique
theorems**, not 4. This is the corpus's own, hand-curated, machine-cross-checked
count — more authoritative than anything I derived by grep.

**But it is not exhaustive either, and I can show that concretely.** My own two finds
from A2 — `ofGround_universal_modal_ground` (`FoundationalOmnipresence.lean:70-73`) and
`ofGround_maximal_capacity` (`:125-127`) — are discharged by the **identical** proof
shape (`Or.inr (fun _ _ => True.intro)` / `trivial` against the same `EntityMeans`
arm) and are **not** in `ofGround_meansAll`'s dependents list. `audit_stipulations.py`
only checks that *listed* names resolve in the depgraph — it does not search the
corpus for every theorem that happens to reduce through the arm, so a hand-curated
list can under-count and pass verification anyway. **So the true count is at least 15,
not 13 and not 4,** and I would not call even 15 settled without a corpus-wide
structural search (e.g. every theorem whose elaborated proof term contains
`Entity.ofGround` and reduces via `match … | .ofGround => True`), which I have not
run.

**Severity, re-assessed with the full count:** this is still graded, still disclosed,
still bounded — the registry itself says so in writing, per-entry, including the
"never derived and never declared as an axiom" sentence for the necessity case. It is
not a new defect; it is a wider acknowledged footprint than my first correction
implied. The practical consequence for constraint 2: a non-vacuous `EntityExistsAt`
would put **characteristic #1 itself** ("the ground is necessary") in the re-derive
set, which is a materially bigger ask than my first correction suggested, and should
be weighed before committing to the `EntityMeansAt`/`EntityExistsAt`-separation batch
in A5.

**One more small, concrete thing worth fixing while here:** `README.md:1659` cites
`EntityMeans Entity.ofGround := True` as *"one of"* the 28 bridges from "What the
Instrument Cannot See." Checked: it is **not**. That section's 28-count comes from
`scripts/stipulated_def_allowlist.json` (bare-name `Prop` premises like
`AsymmetricGrounding`, `NoRight`, `NoGN` — a disjoint, 28-entry list, confirmed by
`python3 -c "import json; print(len(json.load(open('scripts/stipulated_def_allowlist.json'))['acknowledged']))"` → `28`,
and none of its 28 `def` names is `EntityMeans` or anything in `Stipulations.lean`).
`EntityMeans`'s stipulation is tracked by the **separate** `Stipulations.lean`/
`audit_stipulations.py` mechanism. README's inline example sentence conflates the two
disclosure systems. Minor, but worth a one-line fix alongside A4's cross-referencing
work.

### A3. Unicity — re-checked, and my framing was too harsh

`ofGround_foundational_unicity` (`FoundationalUnicity.lean:218`) *is* routed through
`hAsym`, and `not_asymmetric_grounding` (`FoundationalUnicity.lean:145`) proves `AsymmetricGrounding`
unsatisfiable. But the corpus discloses this itself and supplies the live route:
`SemanticFinitude` → `exactly_one_universal_modal_ground` (`:304`, C320).

My remark that C320 is "a fact about a 3-constructor type, not about a ground of
reality" is **an editorial judgment, not a defect.** The kernel statement is
`∃! g, UniversalModalGround g`; that it is provable from a bound on a nullary sort is
*the content of the theorem*, and F15's own ledger note argues the bound is `VOCAB`
correctly and names `SEM` as the fallback if the author disagrees. **Not a bug. Open
only as a judgement call the author has already made in writing.**

### A4. Disclosure — I was wrong; README already has it

`README.md:1659`: *"`EntityMeans Entity.ofGround := True` — the irrelevance of causal
contact to Part I — is one of them."* My first pass claimed README carried "no
vacuity disclosure." It does, in "What the Instrument Cannot See" (1651-1665), and
the ledger is fuller still (`ledger.md:445`, `:2452`, `:2515`).

**What is genuinely absent:** the pointer exists, but the eighteen Part II rows
(lines 570-1127) do not each carry a pointer back to it. That is a **cross-referencing
gap, not a concealment** — and it is fixable in `build_deduction.py` without touching
any mathematics.

### A5. Settle-before-fix — settled, in build mode, and revised upward

- **Settled:** the "four rows" claim was wrong. `python3 scripts/audit_stipulations.py`
  gives the corpus's own authoritative base (13 unique theorems across the two
  `EntityExistsAt`/`EntityMeans` roots — see A2b), and I found two more
  (`ofGround_universal_modal_ground`, `ofGround_maximal_capacity`) that the registry
  itself omits. **At least 15.** A corpus-wide structural search for every theorem
  whose proof reduces through either `True` arm has not been run and should be, before
  anyone treats 15 as final.
- **Prior warning, updated:** my first-draft "root cause of a dozen issues" was too
  strong; my first-correction "four rows" was too weak. Both were eye-checks. The
  number that should be trusted is the one from `stipulation_audit.json`, cross-checked
  against a real grep — which is what A2b did, and it moved the count from 4 to 13 to
  "at least 15" in three steps. Treat 15 the same way: as the current floor, not the
  ceiling.

---

## B. C556: the conclusion is a field of its own signature (**must stay true**)

### B1. The fact

`formal/Logos/EpistemicPersonalGround.lean:218-227`:

```lean
structure Signature where
  Subject : Type; Content : Type
  TrueAt : Content → Prop; FalseAt : Content → Prop
  Grounds : Subject → Prop; Means : Subject → Content → Prop; Free : Subject → Prop
  epistemic_order : ∀ c, TrueAt c ∨ FalseAt c
  right_wrong_not_vacuous : (∃ c, TrueAt c) ∧ (∃ c, FalseAt c)
  no_personal_ground : ¬ ∃ s, Grounds s
  order_needs_a_meaning_being : (∃ c, TrueAt c) → ∃ s, Free s ∧ ∃ c, Means s c
end
```

`epistemic_order_requires_a_free_meaning_being` (`:276`) is
`fun M => M.order_needs_a_meaning_being M.right_wrong_not_vacuous.1`.

`README.md:437` prints this as *"THE FACT on the propositional side, at `{}`"*;
`README.md:10` prints *"zero substantive axioms."*

### B2. Why it must not be "fixed" by denial

It is **true**. The module docstring (`:210-217`) is explicit that the field *"excludes
exactly that assignment … It constrains witnesses, not premises of Γ, so the register
does not move."*

**Do not** remove the field, re-tag C556, or count it as substantive. It is a theorem
at `{}`.

### B3. The real gap is a missing *counterpart*

There is **no** theorem showing the field is **not derivable** from
`epistemic_order ∧ right_wrong_not_vacuous` alone. The machinery exists and is unused
here — `TrinitySeparations.lean:51` (`unitarian_self_love_gives_no_second_centre`) is
exactly this shape, at `{}`, for the Trinity. C109, C511, C514, C520 are all such
separations. **C556's counterpart is the missing one.**

**Fix, three steps, none of which asserts anything false:**

1. **State the scope.** C556 is a theorem about signatures *satisfying
   `order_needs_a_meaning_being`*. It is not "the order entails a being" over Γ's
   `Subject`. Put that in the README gloss and the Lean docstring.
2. **Add the `{}` separation**: a signature satisfying Γ's vocabulary and
   `epistemic_order ∧ right_wrong_not_vacuous`, in which
   `¬ ∃ s, Free s ∧ ∃ c, Means s c`. New C-id, new 🧱 row.
3. **Leave the badge.** `✅ · {}` stays.

This satisfies constraint 4 exactly: the claim is not made false, and what worried me
becomes a **proved price** instead of a hidden assumption.

### B4. Leave C553 alone

C553 (`EpistemicNecessity.lean:107`) is a genuine conditional on a stated antecedent,
`ClaimsNormativeCorrectness`, and its docstring already says *"The antecedent is kept
explicit and is never discharged."* Only the propositional sibling needs work.

---

## C. `¬ PersonCorrelate Entity.ofGround` — **RESOLVED 2026-10-02, see `ISSUE_C_PLAN.md`**

**Original finding (now fixed, kept for the record):** `ofGround_not_a_person_correlate`
(`CosmicExistence.lean:673`, then named `the_ground_is_not_personal`) was `PROVEN` —
`Entity.ofGround` is provably not identical to a person-correlated subject — but had
**no row at all** in `GAPMAP.md`, and `README.md`'s generated prose (three separate
sentences) read in a way that invited conflating Part I's *personal ground* (a
`Subject` satisfying `Person`) with Part II's *metaphysical ground* (`Entity.ofGround`),
when this theorem is specifically about the latter.

**What was done, in full:** see `ISSUE_C_PLAN.md` for the complete plan, rationale, and
execution log. Summary: ledgered as **C564** (`GAPMAP.md` §18); added to
`CHARACTERISTICS.md` §6 and to `build_deduction.py`'s `CLASSICAL_ATTRIBUTES` /
`CHARACTERISTIC_SECTIONS` (the actual mechanism that reaches `README.md`); the three
conflating sentences (`:600-603` seam note, `:1676` §15 note, `:1740-1747` synthesis
paragraph) rewritten to state the two objects are distinct and to cite C564; backfilled
`base.txt`'s pre-existing gap for the whole §18 batch (C429–C431 had never been
written into the prose corpus, a separate finding made while placing C564); and, per
the user's request, a scoped rename pass (`PersonalEntity`→`PersonCorrelate`,
`DivinePerson`→`DivineHypostasis`, `the_ground_is_not_personal`→
`ofGround_not_a_person_correlate`) to stop the kernel's own naming from inviting the
conflation in the first place. Full pipeline regenerated and all test suites pass
(`test_deduction_dependencies.py`, `test_deduction_compiler.py`,
`test_argument_surface.py`, `test_goal_audit.py`, `gapmap_taxonomy.py --check`);
`lake build` clean; `ofGround_not_a_person_correlate`'s footprint unchanged,
`{Means, Subject, Will, subjectWill}`.

**What C228 remains:** `normative_ground_is_personal` (general `g`, arbitrary
`GenericGroundsRightWrong g`) stays `BLOCKED` — unaffected. C564 closes only the single
instantiation `g := Entity.ofGround`, negatively; it does not touch the general bridge,
and the README/ledger prose now says so explicitly rather than leaving a reader to
infer it.

---

## D. The Trinity's `DivineHypostasis` is not `Person` (option 3, experiment)

### D1. What the sort is

`formal/Logos/DivineAgape.lean:77-90`:

```lean
structure DivineHypostasis where
  deiformEntity : Entity
def Subsists (d : DivineHypostasis) : Prop := d.deiformEntity = divineReality
def is_divine (d : DivineHypostasis) (e : Entity) : Prop := d.deiformEntity = e
```

`divineReality := Entity.ofGround` (`:70`). No `Person`, `FreeWill`,
`RationalNature`, or `DominionOverActs`. `DivineLove`/`IsWord`/`IsSpirit` are
`opaque … := True` (`:98,103,108`) — the `BearingOf` pattern, content in docstrings.

### D2. Two readings the rows may overstate

- **Consubstantiality is definitional.** `is_divine d divineReality` and `Subsists d`
  are the *same equation*. `README.md:1177` presents "All three are God" as a derived
  anti-tritheism result. Honest form: *consubstantiality holds **given the price**.*
- **"Persons" is a name, not a predicate.** C510 proves three subsisting centres in
  one reality, not three instances of `Logos.Person.Person`.

**Prior warning:** `DivineAgape.lean:212-222` shows the author already knows the third
centre is *exactly* the price of `AxProcessionSpirit` and that a binitarian Godhead is
machine-checked consistent (C514, `{}`). This is the most carefully priced part of the
corpus. Treat my D2 as a reading question, not a defect.

### D3. The experiment

Bridge `DivineHypostasis` to Γ's `Person`. The literature answer is that the Son **is**
God (καὶ θεὸς ἦν, John 1:1), so location-equality should be a real unity, not a
container.

**In a scratch namespace. Record both outcomes. Do not commit as mainline unless it
survives.**

- Add a `Person`-shaped predicate over `DivineHypostasis` (individual substance, rational
  nature, dominion over acts).
- Ask: do the three Agape axioms still yield three? Risk: `FreeWill → Person`
  (`Person.lean:135`) plus `FreeWill s := ∃ p q, Means s p ∧ Means s q ∧ Incompatible
  p q` (`Choice.lean:177`, `:116`) — give a `DivineHypostasis` a `Means` field and
  personhood may become **derivable for free**, laundering a `META` price into a `✅`.
- **Guard:** `#print axioms` every new declaration. Any theorem that comes out at `{}`
  where a `META` axiom was previously required **is** the laundering. Report, do not
  ship.

---

## E. `T p := p` — disclosed, and I overstated its importance

`Core.lean:40`: `def T (p : Prop) : Prop := p`, with `tschema : T p ↔ p := Iff.rfl`
(`:43`). So `Correct s p ≡ A s p ∧ p` (`Order.lean:29`), `Incorrect s p ≡ A s p ∧ ¬p`
(`:49`), `Content ≡ True` (`Agency.lean:72`).

My first pass called this a vacuity risk. **On re-reading, the module docstring
(`Core.lean:16-19`) explains it is deliberate:** it is the D2 consistency model that
makes the T-schema a theorem and blocks the liar by stratification. That is standard
practice for a theory of truth in a typed setting and the README *displays it*
(`:120-122`).

**Verdict: not a defect. Lower this to a cross-reference note.** Steps 1-2 are real —
disclosure-to-someone is genuine — and the score block's non-vacuity claim rests on
`right_wrong_not_vacuous` (`EpistemicPersonalGround.lean:222`), which is a real field.

---

## F. The `def`-as-bridge census: 28 bridges, 0 reviewed

`scripts/census_stipulated_defs.py`:

```
inherited bridges (allowlist, reviewed: false) : 28
disclosed in GAPMAP.md                            : 28
UNDISCLOSED in the ledger                         : 0
reviewed against the ledger pointer               : 0
promoted to a declared axiom (paid)               : 0
theorems resting on a bridge the kernel cannot see: 53
```

`README.md:1653-1665` discloses this **well**, including the sentence that matters: *"A
`✅` therefore means kernel-verified conditional on a bridge the kernel does not
charge."* The gap is only that it does not say **which** bridges carry **which** Part II
rows. Cheap fix: a generated per-row footnote from the existing census.

---

## G. README overstates the conclusion (one sentence)

`README.md:1740-1747`: *"Established: genuine normativity has a personal ground; that
ground is unique and necessary."*

Precisely: **a person grounds the poles** (Part I, free, conditional on the stance),
and **there is one constructor with total meaning-capacity** (Part II, free, over a
3-constructor type). For `ofGround` those are provably *different* objects — see C.
Rewrite, do not delete: the sentence is the corpus's thesis and the correction is
subtler than it looks.

---

## H. NEW — the atom/ground infallibility inversion (**the real find**)

Not in ISSUES.md's first draft. Derived during verification of A.

`DivineOmniscience.lean:116`:

```lean
def TruthTracking (e : Entity) : Prop := ∀ p : Prop, EntityMeans e p → T p
```

With `T p := p`, `EntityMeans (ofAtom _) := False`, `EntityMeans ofGround _ := True`:

- **Atom:** `∀ p, False → T p` — vacuously **TRUE**. Every atom is infallible.
- **Ground:** `∀ p, True → T p` = `∀ p, p` — **FALSE** (`ofGround_not_truth_tracking`,
  `:144`, body `exact h False trivial`).

**So the strong sense of omniscience is satisfied by every meaningless atom and
refuted of the ground.** Searched `formal/Logos/`, `investigations/*.md`, and
`base.txt`: **stated nowhere.**

`FoundationalOmniscience` (`DivineOmniscience.lean:182-195`) carries
`not_truth_tracking` as a **field**, and the corpus discloses the refutation thoroughly
(`ledger.md:2516`, `base.txt:1444` item 4). That part is honest and deliberate.

**What is missing is the inversion.** C442 (`CharacteristicSoleBearer.lean:123`) claims
omniscience is a *discriminating* concept. It is — on the permissive sense — while the
strong sense runs exactly backwards. That is a boundary result about the limit of the
vocabulary, provable at `{}`, and it is worth more than the vacuity it sits on.

**Why it serves constraint 3.** The user prefers omniscience *not* refuted. The honest
answer is that **refutation is correct for the vocabulary as defined** and deleting it
would remove the most careful part of the corpus. The route to the user's preference is
not deletion but **new vocabulary** — F16's `EntityMeansAt` — after which the strong
sense may be provable, refuted, or open, and the answer will be earned rather than
stipulated.

---

## I. Direct answer: is the ground refuted? **No.** Complete inventory, checked

The user's reaction to the previous draft: *"The ground is refuted? That doesn't sound
right, at all."* That reaction is correct, and the previous draft's language
("refuted", "most consequential error") earned it. This section is the full,
grepped inventory — not a sample — of every `¬ … Entity.ofGround` theorem in all 102
files of `formal/Logos/`, so the claim can be checked rather than taken on my word.

```sh
grep -rn "¬.*[Oo]fGround\|[Oo]fGround.*¬\|not_.*ofGround\|ofGround.*not_" formal/Logos/*.lean
```

**That search returns exactly six theorems. There are no others.** Here is every one,
classified:

| # | Theorem | Loc | What it actually denies | Classification |
|---|---|---|---|---|
| 1 | `ofGround_ne_ofSubject` | `FoundationalUnicity.lean:131` / `NecessityEternity.lean:168` | ground ≠ `EntityOf s`, any `s` | type disjointness (`Entity.noConfusion`) |
| 2 | `ground_is_not_a_true_chooser` | `AsieticChoice.lean:556` | ¬∃ s, EntityOf s = ground | same disjointness, restated |
| 3 | `ofGround_not_a_person_correlate` | `CosmicExistence.lean:673` | ground is not identical to a subject-correlate-person | same disjointness, dressed in `PersonCorrelate` phrasing |
| 4 | `the_ground_is_not_the_universe` | `CosmicExistence.lean:739` | ground ≠ the totality of what obtains | **anti-pantheism — already a celebrated WIN, README characteristic #9** |
| 5 | `ofGround_not_truth_tracking` | `DivineOmniscience.lean:144` | ground's scope is not "all-and-only-true" | artifact of vocabulary overload, see below |
| 6 | `ofGround_does_not_operate_contradictions` | `DivineOmnipotence.lean:201` | ground cannot operate a contradiction | **standard scholastic doctrine — God cannot do the logically impossible — a component of PROVEN omnipotence, not a limitation** |

**Nothing denies the ground's existence, necessity, aseity, unicity, simplicity,
immutability, pure actuality, transcendence, or power.** I grepped specifically for
that and found nothing:

```sh
grep -rn "¬.*NecessaryEntity.*ofGround\|¬.*ExistsAt.*ofGround\|fails_simplicity.*ofGround\|fails_immutability.*ofGround\|fails_omni.*ofGround" formal/Logos/*.lean
# → no matches
```

Two further near-misses, checked and correctly classified as boundaries, not
refutations:

- `NecessaryKindAudit.lean:122` — `¬ (∀ e, NecessaryEntity e → e = Entity.ofGround)`.
  This does **not** deny the ground is necessary. It denies the ground is the **only**
  necessary thing — C495, already disclosed, already priced on the META bridge
  `necessaryPersonalSubjectExists` (see the Necessity table, `README.md:1156`).
- `Precedence.lean:141` — `¬ (∀ w φ, ExistsAt w ofGround → Satisfies w φ)`. This blocks
  trivialism (ground-exists ⇏ everything is true everywhere); it is a disclaimer
  against an absurd over-reading, not a limit on the ground.

### Item 3 was overstated in the previous draft — here is why it is nearly content-free

`PersonCorrelate g := ∃ s : Subject, g = EntityOf s ∧ Person s`
(`PersonalNormativeGround.lean:236`). The proof:

```lean
theorem ofGround_not_a_person_correlate : ¬ PersonCorrelate Entity.ofGround := by
  rintro ⟨s, hs, _⟩
  exact ofGround_ne_ofSubject s hs
```

**The proof discards the `Person s` conjunct — it is bound to `_` and never used.**
The entire semantic content of this theorem is `Entity.ofGround ≠ EntityOf s`, which
is itself discharged by `Entity.noConfusion` — a fact about how a three-constructor
inductive type was declared, with zero metaphysical content. It is the exact same
family as item 1 (same proof, different name) and structurally identical to item 4
("ground is not the universe"), which the README already lists as a **won**
characteristic (anti-pantheism, transcendence).

**Correction to my previous draft:** I wrote that this theorem was *"the most
consequential error in the reading path"* and worried about it inverting the
corpus's intent. That was overstated. The theorem is true, nearly content-free, and
belongs in the *same table* as "the ground is not an atom" and "the ground is not the
universe" — a transcendence/exclusion result, not a discovery that threatens anything
Part I or the Trinity rows say. **What remains correct from the previous draft: it is
unledgered** (`GAPMAP.md:3649` lists it among ten unledgered `CosmicExistence`
theorems) and `README.md:1740`'s wording still welds two different objects together.
Both are still worth a cheap prose fix. Neither is a crisis.

### Item 5 — the one that looks like infallibility is denied — has a precise, named cause

`TruthTracking e := ∀ p, EntityMeans e p → T p` (`DivineOmniscience.lean:116`).
`EntityMeans` is doing **two different jobs** under one symbol, and the refutation
lives exactly in the gap between them:

1. **Scope-of-reach** (used by omnipresence, maximal capacity): "nothing is foreign to
   the ground's grasp" — `EntityMeans ofGround p := True` for every `p`, including
   `p := False`. This is a *good* result: the ground's reach excludes nothing, not
   even the concept of falsehood.
2. **Assertoric commitment** (needed for `TruthTracking` to mean "infallible" in the
   classical sense "believes no falsehoods"): this requires reading `EntityMeans e p`
   as "e affirms p is the case."

Under reading 1, `EntityMeans ofGround False = True` simply says the ground's scope
is total — the ground is not blind to the existence of falsehood. Under reading 2,
the same fact would mean "the ground asserts the false proposition `False`" — a
defect, if it meant that. **Γ has only one relation, so one `True` on the match arm is
forced to answer both questions, and the corpus's own docstring is already explicit
about which one it means** (`"the ground's scope bears every proposition — including
False — by the constructor's match arm"` — `DivineOmniscience.lean:139-142`): it is
read 1. The theorem is real, the badge is honest, and classical theology is not
threatened — because classical infallibility is a claim about *belief*, and Γ has no
`Believes` predicate. `EntityMeans` was never built to carry assertoric weight; the
"refutation" is a boundary on **what the current vocabulary can claim**, stated
honestly, not a finding about the ground's reliability.

This sharpens — and softens — Issue H and the fix direction for Issue A: the
principled repair is not "make the ground not vacuous" in the abstract, but
**separate the two jobs `EntityMeans` is doing** (scope-of-reach vs. assertoric
content) into two relations. That is exactly what F16's `EntityMeansAt` plus a new,
dedicated `Believes`/`Asserts`-style predicate would do. Once separated,
`TruthTracking` can be restated over the assertoric relation alone, and the classical
strong sense becomes **expressible** rather than definitionally foreclosed by an
overloaded symbol. It may then be provable, refuted, or open — but on its own
vocabulary, not as a side effect of omnipresence's vocabulary.

### What to tell a reader who asks this question

*"Is the ground refuted?"* — **No.** Existence, necessity, aseity, unicity,
simplicity, immutability, pure actuality, and (classical, weak-sense) omniscience are
all `PROVEN`. The six negative theorems above are: four restatements of "the ground is
not a creature" (transcendence, already a celebrated result), one textbook point about
omnipotence not extending to contradictions, and one boundary on a *specific narrow
formalization* of infallibility that conflates two jobs under one relation. None of
them touch the ground itself.

---

## Suggested execution order

| # | Work | Badges | Risk |
|---|---|---|---|
| 1 | **C** — ledger `ofGround_not_a_person_correlate` (new C-id), three-way split, fix `README.md:1740` | none moved | low |
| 2 | **B** — scope statement + new `{}` separation | ✅ stays | low |
| 3 | **H** — prove and ledger the atom/ground inversion | ✅ stays | low |
| 4 | **A4/F** — per-row cross-reference from the census into Part II; fix README:1659's conflated citation | ✅ stays | low |
| 5 | **D3** — `DivineHypostasis`/`Person` experiment, scratch namespace | may move | experiment |
| 6 | **A1-A3/A2b** — `EntityMeansAt` **and** a non-vacuous `EntityExistsAt`, then re-derive | **≥15 rows must re-derive, including C319 itself** | high |

Steps 1-4 change no mathematical claim and move no badge. Land them first.

Step 6 is the real fix for constraint 3 and is the only one that can move a badge. Its
scope is **enumerable but not yet closed** — `stipulation_audit.json` gives 13, I found
2 more by hand, and no corpus-wide structural search has been run to confirm even 15
is final. Run that search before scoping the batch. Constraint 2 is safer than my
first draft implied, but less safe than my second draft claimed — including
**characteristic #1 itself** in the re-derive set is a bigger ask than "four rows."

**Before starting any of it, run the settle-commands in §Verification.** Two of my six
issues shrank or vanished on re-reading. The others may too.

## Verification

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal && lake build
cd .. && python3 scripts/audit_footprints.py && python3 scripts/audit_goals.py \
  && python3 scripts/build_deduction.py
python3 scripts/test_deduction_dependencies.py
python3 scripts/test_deduction_compiler.py
python3 scripts/test_argument_surface.py
python3 scripts/test_goal_audit.py
python3 scripts/gapmap_taxonomy.py --check
```

Per `AGENTS.md`, never hand-edit `README.md` or `investigations/ledger.md` — edit the
Lean docstrings and `formal/presentation_spine.json`, then regenerate. Any change to
formal status must also land in `base.txt` / `theorems/*.txt`.

**§H is VERIFIED.** It was compiled, not merely reasoned about:

```lean
theorem H_atom : ∀ (n : Nat), TruthTracking (Entity.ofAtom n) :=
  fun n _p h => absurd h (fun e => e)
# => depends on axioms: [Logos.Agency.Means, Logos.Agency.Subject]   -- i.e. {} substantive
```

So §H stands and should get a C-id. The companion `ground_not_tracking` is the
existing `ofGround_not_truth_tracking` (`DivineOmniscience.lean:144`).

**Gotcha, corrected 2026-10-02 — the "two `Subject` sorts" note above was wrong.** A
dedicated explore pass (done while scoping `ISSUE_C_PLAN.md`'s rename decision) found
exactly **one** real `Subject` sort (`Logos.Agency.Subject`, `Agency.lean:49`). The
four lookalikes are triple-namespaced local countermodel toggles in
`HostileSemantics.lean`, never opened by any other file — provably inert. Whatever
shadowing error produced the original note above was an artifact of my own scratch
file's imports, not a corpus defect. Left here, struck through in spirit, as a record
that this specific prior finding did not survive re-verification — exactly the
discipline §0 asks for, applied to my own earlier claim. Also note
`TruthExhaustive e := ∀ p, T p → EntityMeans e p` runs **opposite** to
`TruthTracking`'s `EntityMeans e p → T p` — so exhaustive scope alone
never yields tracking, which is exactly why the atom case needs `absurd` and not a
witness. (This direction gotcha is now also recorded directly in
`DivineOmniscience.lean`'s docstrings, not only here.)

Known pre-existing blocker, unrelated: `scripts/ledger_superset.py` needs
`.snapshots/README.pre-split.md`, absent (`.snapshots/` is empty and untracked).
