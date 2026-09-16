# GAPMAP.md — theorem ledger of Γ (generated from `#print axioms`, 2026-09-16, post M0+M1)

Statuses: `PROVEN` (theorem, kernel-checked) · `PROVEN↑` (theorem under
flagged axioms) · `AXIOM` (declared) · `BLOCKED` (missing lemma named) ·
`DEFERRED` (out of scope of this milestone).

`CL` = `{propext, Classical.choice, Quot.sound}` (classical meta-logic, D1).
`FORCED` (batch M0, 2026-09-16, `FORCED_SUBJECT.md`): the foundation class —
a TRANS axiom whose negation refutes itself (`Cogito`); not a price.

## Level 0 — performative core (`Logos.Core`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C1 | §4 | `nothingTrueRefutes : ¬ T N_T` | PROVEN | `{}` (E0: `T := id`) |
| C2 | §4 | `notNothingTrue : ¬ N_T` | PROVEN | `{}` (E0) |
| C3 | §4 | `someTrue : ∃ p, T p` | PROVEN | `CL` |
| C4 | §4 | `atomicTruthWitnessed : T True` | PROVEN | `{}` (E0) |
| C5 | §5 | `nothingFalseRefutes : ¬ T N_F` | PROVEN | `{}` (E0) |
| C6 | §5 | `notEverythingTrue : ¬ N_F` | PROVEN | `{}` (E0) |
| C7 | §5 | `someFalse : ∃ q, IsFalse q` | PROVEN | `{}` (E0) |
| C8 | T3 §6 | `greatResult : ∃ p q, T p ∧ IsFalse q` | PROVEN | `{}` (E0) |
| C9 | T3 | `noBothTrueAndFalse` | PROVEN | `{}` (pure logic) |
| C10 | §22 | `excludedMiddle : ∀ p, T (p ∨ ¬ p)` | PROVEN | `CL` |
| C11 | §23 | `nonContradiction : ∀ p, T (¬ (p ∧ ¬ p))` | PROVEN | `{}` (E0) |
| C12 | §10 | `bivalence : ∀ p, T p ∨ IsFalse p` | PROVEN | `CL` |

Founding definitions of Level 0 (E0, 2026-09-15): `def T (p : Prop) : Prop := p`
(the D2 consistency model made definitional); `tschema` is a theorem
(`Iff.rfl`), no longer an axiom. The §4–§6 self-refutation core is
axiom-free: its negation-free content rests on classical logic only.

## Level 1 — semantics (`Logos.Semantics`, `Logos.Truthmaker`, `Logos.Modal`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C13 | §22 | `Semantics.lawExcludedMiddle` | PROVEN | `CL` |
| C14 | §23 | `Semantics.nonContradiction` | PROVEN | `{propext}` |
| C15 | §24a | `Truthmaker.groundPrinciple_atom` | PROVEN | `{Subject, ExistsAt, Ground}` (atom-only structural TrueAt, A2; C2: `Entity := Subject`) |
| C16 | §22 | `Truthmaker.lawExcludedMiddle` | PROVEN↑ | `CL + {Subject, ExistsAt, Ground}` (A2: AxOr/AxNot dropped) |
| C17 | §23 | `Truthmaker.nonContradiction` | PROVEN | `{Subject, ExistsAt, Ground}` (A2: AxAnd/AxNot dropped; no propext) |
| C18 | T7 | `Modal.T7_necessaryReality` | PROVEN↑ | `{AxGlobalGround, Subject, ExistsAt, Ground}` |
| C19 | T7 | `Modal.T7_excludedMiddleInstance` | PROVEN↑ | as C18 |
| C20 | T7 | `Modal.noNecessaryTruthIfAllContingent` | PROVEN↑ | as C18 |

Declared (Level 1): `Ground` (world-rigid, D6; now over `Subject`), `ExistsAt`
(SEM, D4); `actualWorld` (def, SEM —
shrinks C18–C20; was axiom); `AxGlobalGround` (SEM, D7 — the named quantifier
swap). `Entity := Subject` is a *definition* (C2, 2026-09-15 — the Q2/D11
identification, no longer an axiom); `EntityOf` is the identity (dissolved).
A2 (2026-09-16): `AxOr`/`AxAnd`/`AxNot` deleted — the connective truthmaker
clauses are now **PROVEN theorems** (structural `TrueAt`, C15–C17).

## Level 2 — agency and person (`Logos.Agency`, `Person`, `Alternatives`, `Order`, `GroundPerson`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C58 | §1 fnd | `Agency.noCogito_selfRefutes : (¬∃s p, A s p) → False` — **SUBJECT IS FORCED** | PROVEN↑ | `{Cogito, Means, Subject}` (FORCED foundation; the denial is itself an act) |
| C59 | §27 | **M5** `Spike_M5.strongTruthExists : ∃ τ : Semantics.Form, Semantics.NecessarilyTrue τ` — "Strong Truth Exists" resident axiom-free ("há certo E há errado"; spike-only, outside barrel) | PROVEN (spike) | **`{CL}` — no Cogito** (14th axiom-free theorem; C37 lever) |
| C21 | §1/T1 | `Plurality.T1_subjectExists` (re-homed from Agency by A1) | PROVEN↑ | `{Cogito, Means, Subject}` (kind-preds `Agent`/`Rational` are now defs; A1: content re-homed here; M0: re-anchored on the forced foundation `Cogito`, not on `T12`) |
| C22 | T2 | `Agency.T2_contentExists` | PROVEN | **`{}`** — `Content _ := True` (def), `True` witnesses content; cogito not needed (was `{cogito}` + 6 kind-preds) |
| C23 | T4 | `Plurality.T4_agentExists` (re-homed from Agency by A1) | PROVEN↑ | as C21 (`Agent` is `:= True`, def — agent existence is analytic) |
| C24 | T5 | `Plurality.T5_personExists` (re-homed from Person by A1) | PROVEN↑ | as C21 (was `Person.T5_personExists`, on the deleted `cogito` axiom) |
| C25 | §24b | `Person.inseparability_24b` | PROVEN↑ | `CL + {Means, Subject}` (no cogito) |
| C26 | **T9 (new)** | `Alternatives.T9_incompatibleAlternatives` | PROVEN | `{}` (E0) |
| C27 | §13 | `Alternatives.incompatible_with_negation` | PROVEN | `{}` (E0) |
| C28 | T6 | `Order.T6_fallibility` | PROVEN↑ | `{Cogito, Means, Subject}` (M0: from the forced foundation, not the pair) |
| C29 | T6 | `Order.T6_truthTranscendsWill` | PROVEN↑ | as C28 |
| C30 | §8 | `Order.correctness_distinct` | PROVEN↑ | `CL + {Cogito, Means, Subject}` (M0) |
| C31 | §9 | `Order.consequence_preserves_truth` | PROVEN | `{}` (E0) |
| C32 | T8 | `GroundPerson.T8_personalGround` | PROVEN↑ | `{AxPersonalGround, GroundProp, Means, Subject, ExistsAt}` (no cogito) |
| C33 | T8 | `GroundPerson.present_feature_is_grounded` | PROVEN↑ | `{GroundProp, GroundPrincipleProp, Means, Subject}` |
| C34 | T8 | `GroundPerson.necessary_truth_has_necessary_grounder` | PROVEN↑ | as C18 |

Declared (Level 2): vocabulary `Subject` (pure-sort postulate — an empty
`inductive` would refute `∃ s` and break `Cogito`/T12; `Bool`/`fin 2`
smuggle "exactly two subjects"; `ℕ` asserts infinity; `Unit` kills `s₁ ≠ s₂`)
and `Means` (opaque, the only real act-vocabulary); `Exists`/`Content` and
`Agent`/`Rational` are now *analytical definitions* (`:= True`, batches
cogito-rethinking + Tier1 — no longer axioms).
**FORCED FOUNDATION (M0, 2026-09-16):** `Agency.Cogito : ∃ s p, A s p` — the
choosing-subject existence is restored as the unconditional TRANS axiom here
(the act is the first given). The A1 experiment (cogito deleted, datum
derived under `AxTwoSubjects`) is recognized as the bug `FORCED_SUBJECT.md`
fixes: the datum is NOT a consequence of plurality. Its denial refutes itself
(`noCogito_selfRefutes`, C58) and the Walls (empty model + carrier smuggling)
forbid a derivation. The former derived chain re-anchors on `Cogito` — the
`{AxTwoSubjects, Means, Subject}` footprints of C21/C23/C24/C28-C30/C39/
C48/C52-C57 become `{Cogito, Means, Subject}` (measured, §Annex).
Act structure is *defined* (B1, now Tier1-collapse): `A s p := Means s p` —
the bundled act IS the meaning-act; the `act_implies_*` are `rfl`-level
theorems.
`GroundProp`, `GroundPrincipleProp` (SEM reflection of §24a);
`AxPersonalGround` (META, D9 — the remaining price of "personal").
`Realizes := GroundProp` (def, B2) — `AxGroundBearing` dissolved (was META).

## Deferred / blocked

| ID | Prose | Status | Missing |
|----|-------|--------|---------|
| F1a | §13–§15 choice-existence (`∃s p q`, `Chooses s p q`) | PROVEN↑ | `person_chooses`/`choiceExists`/`judge_commits` (choice-realism batch, C51–C52/C55) |
| F1b | §15 bipolar freedom (`FreeWill ↔ ◇Choose ∧ ◇Choose¬`) | DEFERRED | modal choice semantics on `NecessityPH` — a subject may mean `p` without being able to mean `¬p` (T11 is only the structural field) |
| F2 | §21 teleology (`Ought → Goal`) | DEFERRED | deontic layer (normativity → telos) |
| F3 | §28 Good (`§20 → bem`) | DEFERRED | moral good from logical normativity not yet derived |
| F4 | §28 Love | PROVEN↑ | T13 under AxTwoSubjects (C3-I) |
| F5 | §28 EternalRelation | PROVEN↑ | T14 under C3-I bridges + AxPersonStability |
| F6 | §28 Trinity | DEFERRED | no argument exists yet (§28/§29) |
| Q7.2 | weaker `AxGlobalGround` | DEFERRED | research sub-question (DESIGN.md) |

## Level 3 — modal, choice, interpersonal value (new: poem chain)

| ID | Poem | Lean theorem | Status | Axiom footprint |
|----|------|--------------|--------|-----------------|
| C35 | P2 | `Core.negatedAbsolutes : ¬ (N_T ∨ N_F)` | PROVEN | `{}` (E0) |
| C36 | P2 | `Core.rightWrongDistinction : ¬ N_T ∧ ¬ N_F` | PROVEN | `{}` (E0) |
| C37 | P2 | `Semantics.bothNecessarilyTrueAndFalse` | PROVEN | `CL` |
| C38 | P2 | `Necessity.necDistinction : Necessity (¬ N_T ∧ ¬ N_F)` | PROVEN (was AXIOM) | `{}` (E0; C1: identity-model alias; world content = C37) |
| C39 | P4 | `Choice.T11_choiceField` | PROVEN↑ | `{Cogito, Means, Subject}` (was `{cogito, …}` — A1; M0 re-anchor) |
| C40 | P5/P7 | `Plurality.T12_twoPersons` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` |
| C41 | P7 | `Love.T13_someoneLovable` | PROVEN↑ | via C40 |
| C48 | P1/§1 | `Plurality.cogito_from_T12` | PROVEN↑ | `{Cogito, Means, Subject}` (cogito *as corollary*: the forced datum; former A1 derivation re-classified — datum is the foundation, not a theorem of plurality; M0, `FORCED_SUBJECT.md`) |
| C49 | §13/IM_STUPID | `Choice.meaning_needs_subject` | PROVEN↑ | `{Means, Subject}` (analytic; vocabulary only) |
| C50 | §14 | `Choice.incompatible_self_negation` | PROVEN | **`{}`** (pure logic — the field around any meaning-act, 11th axiom-free theorem) |
| C51 | §14/IM_STUPID | `Choice.person_chooses : Person s → ∃p q, Chooses s p q` — **subject ⇒ choice** (was mislabeled "OPEN" gap) | PROVEN↑ | `{Means, Subject}` (no cogito) |
| C52 | §14 | `Choice.choiceExists` | PROVEN↑ | `{Cogito, Means, Subject}` (choice is real, from T5 — now `Plurality.T5_personExists`, M0 re-anchor) |
| C53 | §14 | `Choice.noChoice_selfRefutes : (¬∃s p q, Chooses s p q) → False` | PROVEN↑ | `{Cogito, Means, Subject}` — denying choice is itself an act = a choice |
| C54 | IM_STUPID §2 | `Choice.JUDGE_COMMITTED : (¬N_T ∧ ¬N_F) → ∃s p q, Chooses s p q` — **right/wrong ⇒ choice** | PROVEN↑ | `{Cogito, Means, Subject}` (premise unused: choice already holds via C52) |
| C55 | §8/§14 | `Order.judge_commits : ∃s p q, A s p ∧ (Correct s p ∨ Incorrect s p) ∧ Chooses s p q` — the judge IS a chooser | PROVEN↑ | `CL + {Cogito, Means, Subject}` |
| C56 | P6 | `Value.alone_no_other_help_harm` | PROVEN | `{Subject}` (M1: `Affects` is now the A3 definition `s ≠ t`, so the P6 lemma loses its axiom — measured) |
| C57 | §26 | `Choice.noSubject_selfRefutes : (¬∃_s : Subject, True) → False` — **a subject exists is un-denyable**: the denial is itself an act/choice of a subject; `choiceExists` (C52) supplies the resident witness | PROVEN↑ | `{Cogito, Means, Subject}` — formal record of §26 "não existe sujeito do ato presente"; the act-datum is the *forced foundation* `Cogito` (M0), never a consequence of the plurality bridge |
| C42 | P8 | `Love.T14_eternalRelation` | PROVEN↑ | `{AxTwoSubjects, AxPersonStability, ExistsAt, Means, Subject}` (M1: `Affects := s ≠ t` def + `AxPersonsAffect` theorem — both words vanish from the footprint) |
| C43 | P8 | `Love.T14_content` | PROVEN↑ | as C42 |
| C44 | P8 | `Love.T14_world` (`NecessityPH`) | PROVEN↑ | as C42 (world-anchored honest □) |
| C45 | P8 | `Love.T14_square` (alias `Necessity`) | PROVEN↑ | as C42 (image of the old statement shape) |
| C46 | P5 | `Value.valueInterpersonal_of_split` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (recovery theorem: exact old statement; M1: `Affects`/`AxPersonsAffect` gone) |
| C47 | P5/P7 | `Plurality.T12_directedPair` | PROVEN↑ | `{AxTwoSubjects, Means, Subject}` (chain node — M1: distinctness is already the forward direction under A3, so the pair wears its own inequality; T14 built on this node) |

Declared (Level 3): **M1 (A3, 2026-09-16): `Affects` is now a structural
DEFINITION (`Affects s t := s ≠ t`), no longer the primitive value axiom, and
`AxPersonsAffect` is a THEOREM of that definition** (distinct persons are
distinct — `Or.inl hne`). `Helps`/`Harms` are its definitional projections
(`:= Affects`); `help_affects`/`harm_affects` are `rfl`-theorems;
`Entity`/`EntityOf` dissolved (C2). The only declared interpersonal bridge is
the plurality claim `AxTwoSubjects`
(META, right-and-wrong demands two distinct persons).
`AxPersonStability` (SEM, world-persistence of persons) stays declared (M3
spike BLOCKED — the necessary relata is not connected to the act's subject).
`Loves` is a *definition* (`:= Affects`, C4), no longer an axiom;
`AxValueInterpersonal` and `AxEternalLove` are dissolved (split / replaced).
M2 spike (`formal/Spikes/Spike_A4_2.lean`): `ALONE_EXCLUDED` BLOCKED — the
lone-subject consistency witness (`nonempty Unit`, `Me`/`Per`/`Lon` images,
`lonely_affects_no_other`) is kernel-checked in-file; `AxTwoSubjects` stays as
a *price justified by a model* (a mathematical result, GAPMAP D14b annex).
Modal layer is derived (C1): `Necessity: Prop → Prop` is a *definition*
(identity-model alias) and `NecessityPH : (World → Prop) → Prop` the
semantics-grounded operator; `necK/necT/nec4` (alias) and `necKPH/necTPH/nec4PH`
are theorem; `necDistinction` is a theorem. No modal axiom remains.

## Faith / DEFERRED

| ID | Poem | Status | Note |
|----|------|--------|------|
| FAITH-1 | P2 necessity | → PROVEN | dissolved in C1: `necDistinction` is now a theorem (C38); world content = C37 |
| FAITH-2 | P8 eternal love | → PROVEN↑ | dissolved in C4: replaced by `AxPersonStability` (SEM) + C3-I bridges; T14 is a theorem under them |
| F7 | §15 the bipolar half of freedom | DEFERRED | = F1b — must be built on `NecessityPH` (world-level), not the degenerate alias |
| F8 | Trinity | DEFERRED | not attempted (§28/§29) |
| F9 | Incarnation / creation | DEFERRED | poem P10, faith datum |

## Hardening batch B1/A1/B2/C1 (2026-09-15)

- **B1** (act bundle): `A` redefined as a bundled predicate; the six
  `act_implies_*` meaning postulates became `rfl`-theorems. `cogito` is the
  single performative datum. Saves 6 axiom declarations; C21–C25, C39
  footprints shrink to `{cogito}` + kind-predicates.
- **A1** (fallibility): `Fallible := IsFalse` (the former consistency model,
  lifted to bivalence); `fallible_false` is a theorem. `Fallible` and
  `fallible_false` dissolved; C28–C30 lose them from their footprints.
- **B2** (`Realizes`): `Realizes := GroundProp` (rename); `AxGroundBearing`
  dissolved (was META); T8 (C32) now loads on `AxPersonalGround` only.
- **C1** (necessity): `Necessity p := ∀ w, p` (identity-model alias, D12) is a
  definition; `necK/necT/nec4` are theorems. Added `NecessityPH` — the
  semantics-grounded world-level operator with `necKPH/necTPH/nec4PH` theorems
  (no axioms). `necDistinction` is a theorem (was axiom, C38/FAITH-1). Saves 4
  axiom declarations.

## Batch C3-I/C4 — Interpersonal bridge split + structural love (2026-09-15)

- **C3-I** (split of `AxValueInterpersonal`): the monolithic META bridge
  `AxValueInterpersonal` is split into two narrower bridges:
  * `AxTwoSubjects` (META, plurality only: right-and-wrong demands two persons);
  * `AxPersonsAffect` (SEM meaning-postulate: distinct persons bear on each other).
  Recovery theorem `valueInterpersonal_of_split` proves the old statement. No
  strength lost; axiom content redistributed (lines 70–91 of `Value.lean`).
  Exclusion spikes (x2_spikeA, x2_spikeB) both stuck as designed: named missing
  lemma `ALONE_EXCLUDED : ¬ (∃ s, Person s ∧ Alone s)` — the transcript of the
  spike kernel context is in `/tmp/opencode/x2_spike{A,B}.lean`.
- **C3-II** (single exclusion attempt, one-shot): tried to derive a second
  subject directly from the denial of `Alone` via `cogito + T6 + P6 + defs`.
  Stuck (x2_spikeC): the one-person scenario is consistent with every theorem;
  the interpersonal bridge is genuinely separate. Record in DESIGN.md D14b.
- **C4** (`Loves := Affects`, structural love): `Loves` is redefined as a
  *definition* (`Affects`); `AxEternalLove` (FAITH/META, D14b) is dissolved.
  A new bridge `AxPersonStability : ∀ s, Person s → NecessarySubject s`
  (SEM, poem's "de alguma forma") carries the *eternal* half of T14, attached to
  the relata. T14 is restated as four theorems (`T14_eternalRelation` with
  `NecessarySubject` relata; `T14_world` with `NecessityPH`; `T14_square` the
  alias-□ image; `T14_content`). FAITH-2 dissolves. Loves is no longer an axiom.
  Exclusion spike x2_spikeD stuck: `Person` structure (T5) gives no fact about
  world-persistence of the entity-correlate.

## Batch E0/C2/A3 + transcendental spikes (2026-09-15) — honest info-line cut

Mechanism is **axiom→theorem/definition only** (no audit suppression, no lake
silencing — the 38 `#print axioms` statements stay). Measured on `lake build`
output: **220 → 180 printed axiom-entries (−18 %)**; 222 → 198 output lines;
6 theorems now print `does not depend on any axioms`.

- **E0** (`T := id`, `Core.lean`): the D2 consistency model made definitional.
  `axiom T` + `axiom tschema` are dissolved; `theorem tschema := Iff.rfl`.
  All §4–§6 self-refutation proofs re-verified (unchanged bodies — they were
  already logic, now openly so): `rightWrongDistinction` ("há certo e há
  errado") is axiom-free. `{T, tschema}` vanishes from ~16 non-empty blocks.
  Reversible by definition-restore; D4's gap concern re-recorded in D-E0.
- **C2** (`Entity := Subject`, `EntityOf := id`; `Truthmaker.lean`,
  `Plurality.lean`): the Q2/D11 identification made definitional
  (`Truthmaker` imports `Agency`, no cycle). `Ground`/`ExistsAt` stay the two
  real semantics axioms, now over `Subject`. `{Entity, EntityOf}` leave every
  Level-1 and T8/T14 block (T14 family: 13 → 10 entries each).
- **A3** (`Affects := Helps ∨ Harms`, `Value.lean`): faithful to P6; bundle
  mirrors B1. `help_affects`/`harm_affects` become projection theorems.
  `AxPersonsAffect` restated over the bundle; its footprint now shows
  `Helps`/`Harms` (unfold) instead of `Affects`.
- **B-spikes 2.0** (transcendental retries, `/tmp/opencode/x3_spikeB{1,2,3}.lean`,
  stuck by design): `ALONE_EXCLUDED` re-attacked post-E0/C2/A3 (strawmen: T6
  fallibility is one-subject; `rightWrongDistinction` is axiom-free but
  quantification-agnostic); `PERSONS_BEAR` (no intro rule for `Helps`/`Harms`
  from act-structure); `PERSON_PERSISTS` (no rule from `Person` to `ExistsAt`).
  Named missing lemmas `ALONE_EXCLUDED`, `PERSONS_BEAR`, `PERSON_PERSISTS`;
  the three bridges stay priced (META/SEM/SEM) — no fabricated promotion.

## Batch actualWorld-def + T12_directedPair (2026-09-15) — free fortifications

Two honest cuts with no price, per the reducibility audit (§3 of the plan):
the previous agent's vetoed `someTrue` classical proof is **untouched** — it
remains the explicit reductio that exhibits the transcendental content, and
its footprint stays `CL`.

- **actualWorld → def** (`Modal.lean`): `def actualWorld : World :=
  fun _ => Logos.Semantics.TV.t` (precedent: `Necessity.someWorld`). T7
  invokes `Ground e τ` at *some* fixed world; nothing depends on which, so the
  "present world" is a modeled choice, not a datum. Axiom count 23 → 22;
  C18–C20 lose `actualWorld` (now `{AxGlobalGround, Subject, ExistsAt, Ground}`).
  No proof-body changes.
- **T12_directedPair** (`Plurality.lean`, **C47**): the T12 pair oriented so
  affectivity flows named-forward — `AxPersonsAffect` decides direction by
  cases. `T14_eternalRelation` (`Love.lean`) is rebuilt on this node instead
  of the inline T12+cases, so direction and stability hold of the *same* pair.
  Same footprint as before (`{AxTwoSubjects, AxPersonsAffect, AxPersonStability}`
  + vocabulary + `{ExistsAt, Helps, Harms}`); one more named step in the chain.
  A lone stability-only node was rejected: direction and stability would then
  be unconnected (see DESIGN.md D-C47).
- Measured: `#print axioms` statements total 38 (statement-level audit set;
  the earlier "39" figure counted two in-doc mentions in `Core.lean`);
  theorems printing `does not depend on any axioms` now 8 (adds
  `necDistinction_content`, `necKPH`, `nec4PH`); `sorryAx: 0`; `lake build`
  green, zero warnings.

## Batch Chooses-def + A3-refactor (2026-09-15) — Value & Choice hardening

Two more honest cuts from the reducibility audit; the `someTrue` classical
proof remains **untouched**.

- **Chooses → def** (`Choice.lean`): `axiom Chooses` was dead code — used only
  by `def CanChoose` → `def FreeWill`; not a single theorem carries it in its
  footprint (F1/DEFERRED interface built on the placeholder `def Chooses :=
  False`). Axiom count 22 → 21; `T11_choiceField` footprint unchanged
  (`{cogito}` + kind-predicates); no proof bodies touched.
- **A3-refactor / Affects-primitive** (`Value.lean`): `Affects` promoted from
  bundle-definition to the *single primitive* value relation
  (`axiom Affects : Subject → Subject → Prop`); `Helps`/`Harms` demoted to
  projections `def Helps := Affects`, `def Harms := Affects`;
  `help_affects`/`harm_affects` become `rfl`-theorems. Axiom count 21 → 20.
  Footprints across the love chain drop `{Helps, Harms}` and read
  `{Affects}` instead — measured: `alone_no_other_help_harm`
  `{Subject, Affects}`; `valueInterpersonal_of_split` / `T12_directedPair`
  / `T14_*` all `{…, Affects, AxPersonsAffect, AxTwoSubjects, …}`.
  Honesty note: the HELP/HARM distinction is no longer formal (both unfold to
  `Affects`); it survives only on the prose/conceptual side (P6's "não ajuda
  nem prejudica ninguém" still holds, both halves literally).
- Measured: axiom inventory **20 declarations + CL** (now **18** after
  cogito-rethinking batch); `#print axioms` statements **39** (was 38, adds
  `cogito_from_T12`); `sorryAx: 0`; `lake build` green, zero warnings. The
  `PERSONS_BEAR` spike conclusion is unchanged: `Affects` (and hence its
  projections `Helps`/`Harms`) still has no *introduction rule* forcing it
  between persons — `AxPersonsAffect` stays a priced SEM bridge.

## Batch cogito-rethinking (2026-09-15) — Exists/Content defs + cogito as theorem

The user's observation drives this batch: **non-cogito refutes itself**.
Structurally this mirrors N_T ("there is no wrong") — the absolute negation
contradicts itself. RETHINKING-COGITO.md records the parallel in full.

- **Exists → def, Content → def** (`Agency.lean`): `def Exists (_s) := True`,
  `def Content (_p) := True` — analytical: every subject we meet exists; every
  proposition is a valid content. These two opaque axioms were meaning-intended
  as definitional; now made so. **Axiom count 20 → 18**.
- **cogito → derivable theorem** (`Plurality.lean`, C48): `cogito_from_T12` —
  from `T12_twoPersons` take a Person (`Agent ∧ Rational ∧ Intentional`),
  `Intentional` supplies the meant content, and the defs fill Exists/Content.
  Footprint `{AxTwoSubjects}` + kind-predicates — **no cogito, no Exists, no
  Content**. T2 became axiom-free (`{}`, witnessed by `True`). The denial of
  cogito is now refuted by a *theorem*, exactly as N_T is refuted by
  `notNothingTrue`.
- **`axiom cogito` retained in `Agency.lean`** for import-order only (Agency
  cannot import Plurality — cycle). Marked formally redundant.
- Measured: `#print axioms` statements total **39** (adds `cogito_from_T12`;
  the audit set never shrinks); `Exists`/`Content` leave *every* footprint;
  theorems printing `does not depend on any axioms` now **10** (adds
  `T2_contentExists`); `sorryAx: 0`; `lake build`
  green, zero warnings.
- Honest trade-off: footprints that read `{cogito}` still read `{cogito}`
  (T1/T4/T5/T6/T11/correctness_distinct — the axiom is still declared). But
  the *derivability* is now proven, so cogito's status is "axiom, proved
  redundant" rather than "irreducible datum" — a strict strengthening.

Summary counts (post M0+M1, measured 2026-09-16):

- **PROVEN** (no axioms beyond `CL` where marked): C1–C17 (`CL`: C3, C10,
  C12–C16; C13/C14 also need `propext`; everything else `{}`; after A2, C15
  and C17 are axiom-light — C17 measured `{Subject, ExistsAt, Ground}` with
  **no propext**, C15 is definitional), C22,
  C26–C27, C31, C35–C38, C50, C56 (all `{}`; C37 keeps `CL`) — **13 axiom-free**. M5
  (2026-09-16) adds C59 (`strongTruthExists`, `{CL}`) → **14 axiom-free**.
- **PROVEN↑** (under flagged SEM/META/foundation + vocabulary): C58 (`Cogito`
  FORCED foundation + `{Cogito, Means, Subject}`), C18–C20,
  C21, C23–C25, C28–C30, C32–C34, C39–C49, C51–C55, C57.
  (`Cogito` is the sole forced-foundation axiom (TRANS, M0 — `FORCED_SUBJECT.md`);
  `{Cogito, Means, Subject}` replaces the former `{AxTwoSubjects, Means, Subject}`
  on all transcendental-chain theorems C21/C23/C24/C28–C30/C39/C48/C52–C55/C57
  (measured 2026-09-16). `AxGlobalGround`/`AxPersonalGround` are the two META
  prices; `actualWorld` is a def;
  `Exists`/`Content`/`Agent`/`Rational` are analytical defs; `Affects` is the A3
  definition `s ≠ t`; `AxPersonsAffect` is a theorem.)
- FAITH layer: **empty** (FAITH-1 → C38, FAITH-2 → C4); no claims live at the faith boundary.
- Axioms dissolved (all batches): `T`, `tschema`, `Entity`,
  `EntityOf`, `help_affects`, `harm_affects`; `Affects` (axiom → def, M1);
  `actualWorld` (axiom → def); `Chooses` (axiom → def);
  `Exists`/`Content`/`Agent`/`Rational` (axioms → defs);
  `AxOr`/`AxAnd`/`AxNot` (axioms → theorems via A2);
  `AxPersonsAffect` (axiom → theorem, M1 via A3).
  A1 removed `cogito`; M0 restored it as the FORCED foundation **Cogito** (+1).
  Net inventory: **11 declarations** + `CL`:
  `Cogito` (FORCED), `Subject`, `Means`,
  `Ground`, `ExistsAt`, `AxGlobalGround`,
  `AxTwoSubjects`, `AxPersonStability`,
  `GroundProp`, `GroundPrincipleProp`, `AxPersonalGround`.
- `sorryAx` count across all modules: **0**.
- Verification: `lake build` green (34 jobs, seconds, Lean core only); zero
  errors, zero warnings.

## Batch Tier1 + choice-realism (2026-09-16) — act = meaning, choice as theorem

Driven by the user: "There is no right and wrong without choice! OBVIOUSLY"
and "fix the argument, some gaps are obviously not so". Fine-text in
`Choice.lean` + `Order.lean`; full narrative in `IM_STUPID.md` (kept in sync).

- **Tier1 (act = meaning)** (`Agency.lean`, `Person.lean`): `axiom Agent`,
  `axiom Rational` were the *same analytical class* as `Exists`/`Content`
  (intended-definitional); both now `def _ := True`. `A` is redefined as
  `def A s p := Means s p` — the bundled act of B1 IS the meaning-act.
  `act_implies_*` remain `rfl`-level. **Axiom count 18 → 16.**
  Kind-predicates `{Agent, Rational}` vanish from every footprint.
  `Subject` stays an axiom as a *pure-sort postulate*: an empty `inductive`
  `Subject` refutes `∃ s` (breaks `Cogito`/T12 → `False`); `Subject :=
  Bool`/`fin 2` would smuggle "exactly two"; `ℕ` asserts infinity; `Unit`
  kills `s₁ ≠ s₂`. Recorded in the file and in DESIGN.md D-Tier1.
- **Choice-realism** (`Choice.lean`, `Order.lean`): the old `def Chooses :=
  False` placeholder made choice unrepresentable — the mislabeled "subject ⇒
  choice" gap. New real definition `Chooses s p q := A s p ∧ Incompatible
  p q`, plus theorems: `incompatible_self_negation` (pure logic `{}` —
  the field around any meaning-act is non-empty), `meaning_needs_subject`,
  `person_chooses` (**subject ⇒ choice**, was OPEN; `{Means, Subject}`, no
  cogito), `choiceExists`, `noChoice_selfRefutes` (denying choice is itself a
  choice), `JUDGE_COMMITTED` (**right/wrong ⇒ choice**), `judge_commits`
  (the §8 judge IS a chooser, `CL + {Cogito, Means, Subject}` post-M0),
  `canChoose_unfold` (the aliased-◇ choice collapses to real choice),
  `noSubject_selfRefutes` (a subject exists is un-denyable: the denial is itself
  an act; `{Cogito, Means, Subject}` post-M0, formal record of §26).
  `Order.lean` now imports `Logos.Choice` (no cycle).
- **F1 split**: F1a (choice-existence, transcendental) is PROVEN↑; F1b
  (bipolar `◇Choose ∧ ◇Choose¬`, world-level on `NecessityPH`) stays
  DEFERRED — a subject may mean `p` without being able to mean `¬p`.
- Measured: `#print axioms` statements **47** (was 39; +7 Choice, +1 Order);
  axiom-free theorems **11** (adds `incompatible_self_negation`); `sorryAx:
  0`; `lake build` green, zero warnings.

## Batch A1-cogito-removal (2026-09-16, superseded by M0) — axiom deleted, content re-homed

A1 was genuine but mechanical: it relocated the datum, not restructured it.
**M0 (2026-09-16, `FORCED_SUBJECT.md`) recognizes the A1 move as the bug the
forced-foundation batch fixes**: deleting cogito and anchoring on T12/AxTwoSubjects
made choosing-subject existence a *consequence* of plurality — the very datum
it must precede. M0 restores cogito as `Agency.Cogito` (FORCED foundation),
T1/T4/T5/cogito_from_T12 re-anchor there, and the A1-derived footprints
`{AxTwoSubjects, Means, Subject}` become `{Cogito, Means, Subject}` (measured).
The A1 mechanics (re-homing T1/T4/T5, Plurality audit lines, Choice/Order
switches) are retained as implementation but their anchor flips.

- **A1 (historical): `axiom cogito` was DELETED** (`Agency.lean`). The act-datum became
  `Plurality.cogito_from_T12` (C48), anchored on `AxTwoSubjects`. **M0
  recognized this as the bug and re-posted the datum** (see M0 batch below).
- **T1/T4/T5 re-homed** to `Plurality` as corollaries of the *foundation*
  (M0) — not as T12 projections: `Plurality.T1_subjectExists`,
  `Plurality.T4_agentExists`, `Plurality.T5_personExists`. `Person.lean`
  drops the deleted-axiom use; Choice/Order switch to the Plurality nodes.
- **A1 footprint flip (historical, superseded):** `{cogito,...}` → `{AxTwoSubjects,...}`
  was the A1-era state; M0 flips it again to `{Cogito,...}`.
- A4 circularity guard is now **live unconditionally** (M0): `choiceExists`,
  `cogito_from_T12`, `judge_commits`, `noChoice_selfRefutes`,
  `noSubject_selfRefutes`, `person_chooses` all depend on `Cogito` — not on
  `AxTwoSubjects` — so they are now permitted in any spike whose goal is
  `AxTwoSubjects` (no plurality assumption enters their footprints).

## Batch A2-structural-TrueAt (2026-09-16) — connectives as THEOREMS via structural `TrueAt`

The user's ruling: record A2 in its strongest form — *theorem, not thesis*.
Executed in `Truthmaker.lean`:

- **`def TrueAt` is now structural** (atom-grounding + Tarskian recursion over
  `Form`, mirroring `Semantics.Satisfies`): an atom is true in `w` iff some
  entity grounding it exists there; `not`/`and`/`or`/`imp` are
  Tarskian-compositional **by definition**.
- **`axiom AxOr`/`AxAnd`/`AxNot` DELETED** (−3 declarations). Their content is
  now **proved**: `sat_ground_or/and/not/imp : … := Iff.rfl` (C15–C17), and
  `lawExcludedMiddle`/`nonContradiction` are re-proved by definitional
  reduction (classical only for the `or`).
- **`groundPrinciple` → `groundPrinciple_atom`** (C15): the old formula-level
  version is deliberately dropped — for compounds it is underivable (not
  false): `Ground e (or …)` is a free relation with no introduction rule, so
  composite truth carries no existential grounding claim. Prose §24a/§27:
  "toda verdade **ATÓMICA** tem fundamento; a verdade composta é
  composicional (Tarskiana)". The atom-clause is not a new belief: it is the
  face-value model already in DESIGN D4-D5 and `Semantics.Satisfies`.
  Honesty limits: no `TrueAt = Satisfies` ∈-theorem (Ground/ExistsAt remain
  free VOCAB); `Ground e (or …)` neither asserted nor denied.
- Measured footprints (`#print axioms`, scratch `/tmp/opencode/aud.lean`):
  `groundPrinciple_atom` = `{Subject, ExistsAt, Ground}`;
  `lawExcludedMiddle` = `CL + {Subject, ExistsAt, Ground}`;
  `nonContradiction` = `{Subject, ExistsAt, Ground}` (**no propext** — the
  re-proof avoids `rw` on `Iff`); `T7_necessaryReality`/`T7_excludedMiddleInstance`/
  `noNecessaryTruthIfAllContingent` unchanged from before.
- Measured totals: axiom declarations **15 → 12**; `#print axioms` statements
  stay **47** (Truthmaker audit still 3); `sorryAx: 0`; `lake build` green,
  zero warnings.

## Batch M0+M1 (2026-09-16) — SUBJECT IS FORCED + definitional affectivity (`FORCED_SUBJECT.md`)

- **M0 — M0 forced foundation `Cogito` (`Agency.lean`).** The bug (measured):
  choosing-subject existence `∃ s p, A s p` was *optional-conditional* — the
  entire transcendental chain (T1/T4/T5, T6*, T11, choice/reason side, cogito)
  paid `{AxTwoSubjects}` merely to obtain a single witness. **Fix:**
  `axiom Cogito : ∃ s : Subject, ∃ p : Prop, A s p` (FORCED/TRANS) +
  `noCogito_selfRefutes` (C58). Walls that forbid a derivation recorded in
  `FORCED_SUBJECT.md` §1 (empty model satisfies the vocabulary; every non-empty
  carrier smuggles a count). Downstream witnesses re-anchor on `Cogito` —
  measured (`#print axioms`, scratch `/tmp/opencode/audit_forced.lean`):
  C21/C23/C24/C39/C48/C52/C53/C54/C57, C28/C29/`fallible_false` and
  C30/C55 at `CL +` — all `{Cogito, Means, Subject}`.
- **M1 — A3 definitional affectivity (`Value.lean`).** `def Affects s t :=
  s ≠ t` (bearing = distinctness; the lone subject affects nothing, P6);
  `def Helps`/`Harms := Affects`; **`AxPersonsAffect` → THEOREM**
  (`Or.inl hne`). Measured: `alone_no_other_help_harm` → `{Subject}` (C56);
  `T12_directedPair`/`valueInterpersonal_of_split` → `{AxTwoSubjects, Means,
  Subject}` (C46/C47); `T14_*` (C42–C45) → `{AxTwoSubjects, AxPersonStability,
  ExistsAt, Means, Subject}` (no `Affects`, no `AxPersonsAffect`).
- **Axiom inventory 12 → 11:** +`Cogito` (FORCED) −`Affects` (→ def)
  −`AxPersonsAffect` (→ theorem). `#print axioms` statements 47 → 50
  (adds M0 audit lines). `sorryAx: 0`; `lake build` green, zero warnings.
- **Spike verdicts (all BLOCKED, transcripts in `formal/Spikes/`):**
  * M2 `Spike_A4_2.lean`: `ALONE_EXCLUDED` — the lone-subject consistency
    witness is kernel-checked in-file (single inhabitant refutes the target
    over the whole allowed surface); `AxTwoSubjects` stands as a **price
    justified by a model**.
  * M3 `Spike_PersonStability.lean`: `PERSON_PERSISTS` — a necessary relata
    `e₀` exists (T8 content) but `Realizes e₀ f` does not identify it with the
    act's subject; `NecessarySubject s` needs `ExistsAt w s` and no rule links
    `Means` to `ExistsAt`; `AxPersonStability` stays priced (SEM).
  * M4 `Spike_A6_probe.lean`: weaker `AxGlobalMirror` derives T7-**atom**
    (kernel-checked, no `AxGlobalGround`) but cannot cover the compound
    excluded-middle instance (A2 structural TrueAt has no existential ground
    for compounds) — `AxGlobalGround` **stays priced (smaller)**; recording
    only, not adopted.
- **A4 guard relaxes justifiably:** the six enumerated theorems now bottom out
  at `Cogito` (no plurality), so they are plurality-free surface for future
  plurality spikes; the ban on plurality-from-plurality is preserved (nothing
  derives `AxTwoSubjects` from itself).
- **M5 — "Strong Truth Exists" resident; choosing subject stays FORCED (spike
  verdict BLOCKED, presumably permanent).** `Strexp` `Spike_M5_StrongTruth.lean`
  (outside barrel) proves `strongTruthExists : ∃ τ, NecessarilyTrue τ` on the
  axiom-free `{Core, Semantics}` surface — **C59, footprint `{CL}`, no Cogito**,
  the "há certo E há errado" datum of en.md §27/poem.txt, from C37. Axiom-free
  theorems: 13 → 14. `Spike_M5_ChoosingSubject.lean` is the honest probe at
  `∃ s p q, Chooses s p q` WITHOUT Cogito: stopped at the **atom-wall**
  (`groundPrinciple_atom` is atom-only; the {CL}-forced strong truth is the
  necessitated disjunction `Form.or (atom 0) (Form.not (atom 0))`, never a true
  atom; exact missing lemma `∀ w, TrueAt w (Form.atom 0)` is not provable on
  {CL}worlds). `Cogito` **stays FORCED, ladder 11**; NOT demoted. M5 verdict:
  the transcendental datum is axiom-free, the choosing subject is not.
