# KNOWN.md — working state for the "better state" pass

Written 2026-10-09 during a build-mode session (supersedes the plan-mode notes).
Captures the user's directive, what the kernel actually says, the exact
mismatches, and the plan. Read with `AGENTS.md` (binding conventions),
`formal/GAPMAP.md`, and `PROMPT.md` (the still-open SemanticFinitude hand-off).

> Scratch: `research_report_2026-10-08.md` (untracked) is a sub-agent dump from the
> plan-mode research pass. Not normative; supersede or delete it.

---

## 0. The user's prompt (verbatim)

### 0.1 Original message

> "There are many things that could and should already be in a better state. It's
> not possible that the ground is a physicalist's atom. A necessary person is not
> axiomatic - its proven. Free will DOES exist. A Free Subject DOES exist. Etc."

### 0.2 Clarifying answers given in session (verbatim)

**Q: How far should this work go?**
> "You see, we do have a PROVEN path to the Free Subject and the Person. So it's
> selecting the wrong path, and that's why the badge looks wrong. It's not just a
> presentation problem. It is that the connecting bits are wrong."

**Q: The necessary-person existential is a META axiom (C404); the derived C409
exists but the README shows the axiom. What do you want?**
> "The necessary person is PROVEN under the main route (let's just assume the
> existence of the proof)."

**Q: Unconditional existence is priced; the free route is conditional
(`ProofExists C → ∃ s, FreeSubject C s`). Which becomes canonical?**
> "Let's stipulate that the Proof exists"

**Q: Reclassify R13 'the ground is just an atom' from 🧱 BOUNDARY to 💥 DERIVATION?**
> "Yes, make it a free death"

### 0.3 What those answers commit us to

1. The **main route** (the `CompleteLibertarianFreedomArgument` /
   `LibertarianPersonhood` chain) is canonical, not the priced side routes.
2. The **Proof's existence is stipulated** (`demonstration_occurs`, `Tag: TRANS`),
   i.e. "assume the existence of the proof".
3. The **necessary person** is to be presented as *proven* under that main route.
4. **R13** ("the ground is just an atom") is a **free refutation**, not a boundary.
5. It is **not only presentation** — the connecting bits between the routes are
   wrong and must be fixed in the kernel/generator, not just re-worded.

---

## 1. Executive summary

The corpus has **two families of routes to the same conclusions**:

- a **free main route** (`CompleteLibertarianFreedomArgument` → `LibertarianPersonhood`)
  that proves `∃ s, FreeSubject s` / `∃ s, Person s` at **0 substantive axioms**,
  resting only on the `Tag: TRANS` performative axiom `demonstration_occurs`; and
- older **priced side routes** (`AsieticChoice` under `AxTwoNecessaryPersonalCentres`
  META; `ActCascade` under `AxIntentionalChoice`/`AxActPolarity` SEM;
  `NoMeanerNoFalsity` under `AxActPolarity` SEM).

The reader surfaces (`README.md`, `presentation_spine.json`, GAPMAP cells, the
generator's hand-written prose) **select the priced side routes for the
existence rows**, so the badges look wrong even though the free proofs exist.
That is the user's "selecting the wrong path".

Separately, the **necessary person** (`∃ s, NecessarySubject s ∧ Person s`) is
**not** on the main route: the kernel has *no lemma* connecting the main-route
witness to `NecessarySubject`, and `HostileSemantics.CountermodelPersonNotNecessary`
shows `Person → NecessarySubject` is not a logical law. Necessity enters only via
one of two META bridges (C404, C584). So "the necessary person is proven under the
main route" needs a decision: transcendental reading, priced-with-derived-headline,
or a new bridge (see §7 and §12).

The ground/atom claim is simpler: `Entity.ofGround ≠ Entity.ofAtom n` is free by
constructor disjointness, and the existing `atom_cannot_ground_the_ground` is a
real derivation — but README labels R13 a 🧱 boundary.

---

## 2. The two-route architecture (map)

| Conclusion | Free main route (canonical) | Priced side routes (currently surfaced) |
|---|---|---|
| `∃ s, FreeSubject s` | `LibertarianPersonhood.free_subject_exists_via_judgment_chain` (C593) — **1 TRANS** | `AsieticChoice.freeSubject_exists` (META); `ActCascade.freeSubject_exists_of_act_datum` (SEM) |
| `∃ s, FreeWill s` | CLFA `free_will` / `libertarian_free_choice` | `AsieticChoice.freeWill_exists` (META); `ActCascade.freeWill_exists_of_act_datum_*` (SEM) |
| `∃ s, Person s` | `LibertarianPersonhood.person_exists_via_judgment_chain` (C594) — **1 TRANS** | `NoMeanerNoFalsity.a_genuine_free_person_exists` (SEM) |
| `Person s ∧ GroundsRightWrong s` | `LibertarianPersonhood.person_grounds_right_wrong_via_judgment_chain` (C595) — **1 TRANS** | — |
| `∃ s, NecessarySubject s ∧ Person s` | **none** | `Plurality.necessaryPersonalSubject_derived` (C408) / `NecessaryPersonalGround.necessary_person_derived_from_bridge` (C409), both under **C404 META**; or `AxTwoNecessaryPersonalCentres` (C584 META) |

---

## 3. The free main route, in detail

`formal/Logos/CompleteLibertarianFreedomArgument.lean` (namespace
`Logos.CompleteLibertarianFreedomArgument.FinalNonCircularClosure`):

- Level 1: `JudgmentDeterminationChain C s w p → FreeSubject C s`.
- Level 2: `ProofInstance C → ∃ s, FreeSubject C s`.
- Level 3: `ProofExists C := Nonempty (ProofInstance C)`.

Key declarations: `libertarian_free_choice` (`:694`), `free_will` (`:712`),
`free_subject` (`:723`), `complete_libertarian_freedom_argument` (`:746`, also
`:2352` as the packaged form).

`formal/Logos/LibertarianPersonhood.lean` discharges Level 3 with a TRANS axiom
and bridges to `Logos.Choice`:

| Claim | Decl (file:line) | Statement | Footprint (from `axiom_audit.json`) |
|---|---|---|---|
| C592 | `demonstration_occurs`, `LibertarianPersonhood.lean:62` (axiom, `Tag: TRANS`) | `DemonstrativeProofOccurrence gammaSem` | `{Means, Subject, demonstration_occurs}` |
| C593 | `free_subject_exists_via_judgment_chain` `:68` | `∃ s : Subject, Logos.Choice.FreeSubject s` | `{propext, Classical.choice, Quot.sound, Means, Subject, demonstration_occurs}` |
| C594 | `person_exists_via_judgment_chain` `:78` | `∃ s : Subject, Person s` | `{…, Will, subjectWill, will_individuation, demonstration_occurs}` |
| C595 | `person_grounds_right_wrong_via_judgment_chain` `:86` | `∃ s, Person s ∧ GroundsRightWrong s` | same as C594 |
| C596 | `judgment_source_not_fixed_by_prior_state` `:97` | anti-determinism source lemma | `{…, demonstration_occurs}` |
| — | `gamma_freeSubject_is_choice` `:43` | `FreeSubject gammaSem s → Choice.FreeSubject s` | `{Means, Subject}` |

`demonstration_occurs` is the **only non-core leaf** on C593/C594/C595. It is the
performative-transcendental instantiation ("this very deduction occurs as a
judgment-determination instance"), i.e. exactly the "stipulate the Proof exists"
the user authorized. The surfaces already disclose it as "0 substantive axioms;
1 TRANS", not as META.

**Caveat that matters for the necessary person:** none of C593/C594/C595 mentions
`NecessarySubject` / `NecessarySubjectKind` / `NecessaryEntity`. The witness is
an *anonymous, unqualified* free Person.

---

## 4. The priced side routes, in detail

- `AsieticChoice.freeWill_exists` (`AsieticChoice.lean:613`) and
  `AsieticChoice.freeSubject_exists` (`:630`) — unconditional, footprint
  `{AxTwoNecessaryPersonalCentres, Means, NecessarySubjectKind, Subject, Will, subjectWill}`
  (META).
- `ActCascade.freeWill_exists_of_act_datum_constitutive` (`ActCascade.lean:283`),
  `…_polarity` (`:299`), `freeSubject_exists_of_act_datum` (`:318`) — footprint
  `{AxIntentionalChoice | AxActPolarity, Initiates, Means, State, Subject, performative_act_datum}` (SEM + TRANS).
- `NoMeanerNoFalsity.a_genuine_free_person_exists` (`NoMeanerNoFalsity.lean:94`, C587) —
  footprint `{AxActPolarity, Initiates, Means, State, Subject, Will, performative_act_datum, subjectWill, will_individuation}` (SEM + TRANS).
- `Choice.freeWill_exists` / `freeSubject_exists` — the underlying `Choice.lean` rows.

These are legitimate but **more expensive than the main route** and are what the
surfaces wrongly headline.

---

## 5. Necessity and the necessary person, in detail

Definitions:

- `Plurality.NecessarySubject s := ∀ w : World, ExistsAt w (EntityOf s)` (`Plurality.lean:41`).
- `Agency.NecessarySubjectKind : Subject → Prop` is an **axiom**, `Tag: VOCAB` (`Agency.lean:62`).
- The two coincide: `kinds_are_the_modal_partition : NecessarySubjectKind s ↔ NecessarySubject s` (`Plurality.lean:83`, free).
- `NecessaryPersonalGround.ClaimD_NecessaryPerson : Prop := ∃ s : Subject, NecessarySubject s ∧ Person s` (`NecessaryPersonalGround.lean:150`).
- `Modal.NecessaryEntity e := ∀ w, ExistsAt w e` (`Modal.lean:28`).

Routes (all priced):

| Claim | Decl | Statement | Footprint |
|---|---|---|---|
| C404 | `Plurality.necessaryPersonalSubjectExists` (`Plurality.lean:188`, axiom `Tag: META`) | `∃ s, NecessarySubjectKind s ∧ Person s` | `{Means, NecessarySubjectKind, Subject, Will, subjectWill, necessaryPersonalSubjectExists}` |
| C407 | `Plurality.necessarySubject_exists` (`:192`) | `∃ s, NecessarySubject s` | same + C404 |
| C408 | `Plurality.necessaryPersonalSubject_derived` (`:200`) | `∃ s, NecessarySubject s ∧ Person s` | same + C404 |
| C409 | `NecessaryPersonalGround.necessary_person_derived_from_bridge` (`:161`) | `ClaimD_NecessaryPerson` | same + C404 |
| C584 | `TwoNecessaryPersonalCentres.AxTwoNecessaryPersonalCentres` (`TwoNecessaryPersonalCentres.lean:117`, axiom `Tag: META`) | `∃ s₁ s₂, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂ ∧ NecessarySubjectKind s₁ ∧ NecessarySubjectKind s₂` | `{Means, NecessarySubjectKind, Subject, Will, subjectWill, AxTwoNecessaryPersonalCentres}` |
| C585 | `Plurality.two_necessary_persons` (`:237`) | the `NecessarySubject`-form of C584 | same + C584 |

`Person.lean` contains **no** necessity notion. `Love.PersonStabilityPrinciple`
(`Love.lean:107-108`) is only the *conditional, kind-gated* form
`∀ s, Person s → NecessarySubjectKind s → NecessarySubject s` — explicitly **not**
an unconditional `Person → NecessarySubject`.

---

## 6. The hard obstacle (blocking the "necessary person proven" directive)

- A full `grep NecessarySubject` over `formal/Logos` finds **zero** references in
  `LibertarianPersonhood.lean`, `Person.lean`, `AsieticChoice.lean`. The only hit
  in `CompleteLibertarianFreedomArgument.lean` is an **auxiliary, unused** local
  `def NecessarySubject` at `:1363` (ThinkingMindAt across accessible worlds),
  under the header "AUXILIARY / NOT A PREMISE / NOT USED BY CORE PROOF".
- Therefore there is **no kernel lemma** `FreeSubject s → NecessarySubject s`,
  `Person s → NecessarySubject s`, or any link from the main-route witness to
  either necessity predicate.
- The corpus's own hostile catalogue confirms this is not an oversight:
  `HostileSemantics.CountermodelPersonNotNecessary` attacks `Person → NecessarySubject`;
  `scripts/build_deduction.py:2131-2134` records the verdict that the logical
  attack **STANDS**, answered only by *paying* C404/C584.

**Consequence:** as the kernel stands, "the necessary person is proven under the
main route" is **false** for the *modal* predicate `NecessarySubject`. It can only
be made true by (a) reading "necessary" transcendentally (the person is
*forced/undeniable given the Proof*, which C594 already is — free, 1 TRANS);
(b) keeping the modal claim and paying C404/C584 while headlining the *derived*
C408/C409; or (c) adding a new declared bridge (an axiom), which contradicts
"not axiomatic". See §12.

---

## 7. Wrong-path mismatches (exact, actionable)

1. **"A free subject exists" selects the priced route.**
   `formal/presentation_spine.json:419-423` targets `AsieticChoice.freeSubject_exists`
   (META footprint), gloss "The one META bridge is `AxTwoSubjects`". The free route
   C593 exists — this is the concrete "wrong path".
2. **"Free will exists" selects the priced route.**
   `presentation_spine.json:426-431` targets `AsieticChoice.freeWill_exists`.
3. **Body prose asserts "one META bridge + a second META axiom".**
   `presentation_spine.json:397-401`: "A free subject exists on **one** META bridge.
   A necessary *person* is a **second** META axiom." Reconcile with the main route.
4. **"A necessary person exists" row.** `presentation_spine.json:440-444` targets
   `Plurality.necessarySubject_exists` (C407). Pricing is correct *for the modal
   claim*, but the row should headline the *derived* C408/C409 and drop any claim
   that no necessary-person theorem exists.
5. **Stale "no necessary person theorem" text.**
   `scripts/build_deduction.py:9078-9091` (Ground 2 check) lists fragments
   `necessary_person_derived`, `divine_person_is_necessary` as `absent` and ends
   "**NO 'necessary Person' theorem exists**". Contradicted by live C408/C409.
6. **Reading-path prose conflation.** `scripts/author_reading_path_prose.py:148-149`:
   "The **person** side needs exactly one `META` bridge, C404 `necessaryPersonalSubjectExists`."
   True only for the *necessary* person; it is the conflation source.
7. **Chain membership.** `scripts/build_deduction.py:10476-10482` already lists the
   main route (C592–C596) — good — but the price tables/§prose do not agree with it.
   Remember AGENTS.md: chain-list membership is **hand-maintained**.

---

## 8. R13 — "the ground is just an atom" → free death

- `Entity` constructors `ofSubject`, `ofAtom (n : Nat)`, `ofGround` are mutually
  distinct (`formal/Logos/Entity.lean:21-26`); `Entity.ofGround ≠ Entity.ofAtom n`
  is free by `Entity.noConfusion`. Same family: `ofAtom_ne_ofSubject`
  (`NecessaryPersonalGround.lean:170`), `ofGround_ne_ofSubject`
  (`DivineClassicalAttributes.lean:190`).
- Existing derivation: `atom_cannot_ground_the_ground : ¬ OneEssence (Entity.ofAtom n)
  Entity.ofGround` (`DivineClassicalAttributes.lean:562`), footprint `{Means, Subject}`
  (a compiled 3-step derivation).
- Yet `README.md:68`, `:1204`, and the R13 block `:1498-1519` present it as
  🧱 **BOUNDARY**, while the block's own proof reads "⚙️ DERIVATION — 3 compiled steps".
- Generator mechanics: `scripts/build_deduction.py:3404` `BOUNDARY = "boundary"`;
  `:4124-4174` `_BOUNDARY_BY_DECL` / `build_boundary_by_decl` / `boundary_by_decl`;
  `:4582-4665` `refutation_kind` selects `⊥`/`⊘`/collapse vs boundary from the goal;
  `:4636` `_REFUTATION_KINDS`. Fix the selection for R13 (and add a direct
  `ofGround_ne_ofAtom` headline theorem if an anchor is wanted).

---

## 9. Core definitions glossary

- `Agency.Subject` — pure sort of subjects (`Agency.lean:49`).
- `Agency.Means : Subject → Prop → Prop` — opaque intentional meaning relation.
- `Choice.FreeWill s := ∃ p q : Prop, Chooses s p q` (`Choice.lean`, ~:184).
- `Choice.Chooses s p q := Means s p ∧ Means s q ∧ Incompatible p q`.
- `Choice.FreeSubject s := FreeWill s` (`Choice.lean:196`), `freeSubject_iff_freeWill` is `rfl`.
- `Person.Person s := ThomisticPersonCore s` (`Person.lean:127`); `free_subject_is_person`
  (`Person.lean:140`), `freeWill_implies_person` (`:135`, the priced VOCAB law
  `will_individuation`).
- `Entity.Entity` constructors and `EntityOf` (`Entity.lean:21-31`).
- `NecessarySubject`, `NecessarySubjectKind`, `ClaimD_NecessaryPerson` — see §5.

---

## 10. Axiom census drift (fix while here)

- `AGENTS.md` states the census as **39 = 18 VOCAB / 6 SEM / 13 META / 2 TRANS**.
- `scripts/check_consistency.py:61-66` comment still says 39 / 2 TRANS (**stale**),
  but `:74` corrects it: **40 = 18 VOCAB + 6 SEM + 13 META + 3 TRANS**, and `:76`
  pins `EXPECTED_AXIOM_STATEMENTS = 40`.
- The 3rd TRANS is `LibertarianPersonhood.demonstration_occurs` (C592).
- **Never assert the count by eye — run `python3 scripts/test_axiom_census.py`**,
  the only place the number is derived. Re-derive, then fix `AGENTS.md` and the
  stale comment block in the same change.

---

## 11. Generation & verification workflow (binding, from AGENTS.md)

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal && lake build                      # must be green
cd ..
python3 scripts/check_consistency.py         # Gate A probe must FAIL to compile (green);
                                              # Gate B syntactic scan passes
python3 scripts/test_axiom_census.py         # derives the pinned count — never eyeball it
python3 scripts/test_goal_audit.py
python3 scripts/test_argument_surface.py
python3 scripts/ledger_superset.py
cd formal && lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot
cd .. && python3 scripts/audit_footprints.py && python3 scripts/audit_goals.py \
     && python3 scripts/build_deduction.py   # regenerates README.md + ledger.md + kernel-audit.md
```

- Never hand-edit `README.md`, `investigations/ledger.md`, `investigations/kernel-audit.md`;
  fix the generator cells (`scripts/build_deduction.py`, `formal/presentation_spine.json`)
  and regenerate.
- Prose corpus (`base.txt`, `theorems/*.txt`) is Portuguese and canonical; sync it.
- Run **one `lake env lean` at a time**.
- No commits unless the user asks.

---

## 12. Open decision (blocking §13 item 3)

What does "the necessary person is proven under the main route" mean formally?

- **(a) Transcendental.** Present C594 (`person_exists_via_judgment_chain`, free,
  1 TRANS) as the *forced/undeniable* person; stop claiming the modal
  `NecessarySubject` for it. No new axiom. Honest, and matches "assume the proof
  exists".
- **(b) Modal, priced, but with the derived headline.** Keep `NecessarySubject`,
  pay C404/C584 explicitly, and make C408/C409 (PROVEN↑ under the bridge) the
  reader-facing rows — removing the false "no necessary Person theorem" text. The
  bridge stays the disclosed price (contradicts the literal "not axiomatic").
- **(c) New bridge.** Add a declared axiom connecting the main-route witness to
  `NecessarySubject`. Makes the connection explicit but *adds* an axiom
  (contradicts "not axiomatic"; also bumps the census).

Recommended default: **(b)**, with the *ordering* done as (a) — i.e. headline the
free main route for the free subject/person, and headline the *derived* C408/C409
for the necessary person, disclosing C404/C584 as the single price. Final call
needs the user.

---

## 13. Plan

1. **R13** → reclassify to 💥 free death; fix `refutation_kind`/`boundary_by_decl`
   handling + README prose; optionally add `ofGround_ne_ofAtom`.
2. **Free will / Free Subject / Person** → re-point the existence rows
   (`presentation_spine.json:419-431`) at the free main route
   (C593 / CLFA `free_will` / C594), price disclosed as "0 substantive axioms,
   1 TRANS (`demonstration_occurs`)"; drop the `AsieticChoice`/`ActCascade` priced
   routes from the headline (keep them in the ledger as secondary routes).
3. **Necessary person** → remove the false "NO 'necessary Person' theorem exists"
   text (`build_deduction.py:9078-9091`); headline C408/C409; resolve §12.
4. **Doc hygiene** → fix `AGENTS.md` census drift and the `check_consistency.py:61-66`
   stale comment (re-derive via `test_axiom_census.py` first).
5. Reconcile the §prose (`presentation_spine.json:397-401`,
   `author_reading_path_prose.py:148-149`) with the chosen story.
6. Regenerate all surfaces; run the §11 suite; sync `base.txt` / `theorems/*.txt`;
   no commit unless asked.
