# GAPMAP.md — theorem ledger of Γ (generated from `#print axioms`, 2026-09-17, post A2-swap-theorem)

Statuses: `PROVEN` (theorem, kernel-checked) · `PROVEN↑` (theorem under
flagged axioms) · `AXIOM` (declared) · `BLOCKED` (missing lemma named) ·
`DEFERRED` (out of scope of this milestone).

`CL` = `{propext, Classical.choice, Quot.sound}` (classical meta-logic, D1).

## Batch A2-swap-theorem (2026-09-17) — `AxGlobalGround` becomes a theorem (atom-restricted)

The quantifier swap `∀w∃e … ⇒ ∃e∀w …` (D7, SEM) is answered by the
esse-est-agere deflation: `ExistsAt` is world-vacuous by definition, so the
witness from any one world works for all worlds definitionally —
`axiom AxGlobalGround` → **theorem** `AxGlobalGround (n : Nat)
(hnec : NecessarilyTrue (atom n))` (name kept per M1 precedent; proof:
`groundPrinciple_atom` at `actualWorld`, same entity reused at every `w`).
Measured (`#print axioms`): A2-atom, C18, C20, C34 → `{Ground}`
(vocab-only — the statement's own vocabulary, no SEM/META).
**Axiom inventory 6 → 5 declarations** (−`AxGlobalGround`); substantive
axioms unchanged in kind (SEM/META only).
Restricted to atoms by the M4 wall (structural `TrueAt` carries no
existential ground for compounds): the excluded-middle instance C19
(`T7_excludedMiddleInstance`, deleted from the barrel) is recorded
BLOCKED with its exact missing lemma `∃ e, Ground e (or θ (not θ))`
given EM-necessity (transcript: `formal/Spikes/Spike_A6_probe.lean` — the
M4 "stays priced (smaller)" verdict is superseded: nothing stays priced;
the atom swap needs no axiom at all). T7 (C18), its reductio (C20) and
the GroundPerson link (C34) are re-scoped to atoms, same proofs. Honestly
recorded cost: T7's "necessary reality grounded on the indubitable"
(compound) is no longer derived — the atom ground is. Q7.2 answered: for
atoms the swap needs no weaker premise (it is definitional); the compound
instance is a different, unforced claim.

## Batch definitional-subject (2026-09-17) — `Cogito` becomes a theorem

The user correction ("cogito must be a theorem; subject definitional, in the
traditional sense") retires M0's TRANS axiom. `axiom Subject : Type` → **def**
`Subject := Unit ⊕ Prop` (ὑποκείμενον: the silent origin sustaining every
posit + posited contents positing themselves; origin-only, never evaluated);
`axiom State : Type` → **def** `State := Prop` (truth-bearers);
`axiom Initiates` → **def** (field-toward-posit, by cases on the subject);
`axiom Cogito` → **theorem** `Cogito : ∃ s p, A s p` (**`{}`**, witness
`Sum.inl ()`); `noCogito_selfRefutes` re-proved by exhibition (**`{}`**,
no axiom cited — the degenerate `fun h => h Cogito` is retired). The M0
FORCED class is dissolved: there is no foundation axiom left to force. The
foundation is re-anchored on the original chain — undeniable right-and-wrong
(C36, `{}`) ⇒ meaning (analytic, §8) ⇒ choosing subject (definitional
witness). **Axiom inventory 12 → 8 declarations** (−`Cogito`, −`Subject`,
−`State`, −`Initiates`); substantive axioms unchanged (SEM/META only).
Former `{Cogito, Initiates, State, Subject}` footprints below are now `{}`
(measured, §Annex), `CL` where `by_cases` is used. (Prior batch, same day:
act-as-initiation rebase — `axiom Means` → def `Means s p := ∃ w w',
Initiates s w w' p`; `A s p := Means s p` unchanged.)

## Batch esse-est-agere (2026-09-17) — existence as agency; `AxPersonStability` becomes a theorem

The M3 wall (`PERSON_PERSISTS`: no rule from `Person`/`Means` to `ExistsAt`)
is answered by supplying the rule as a definition: `axiom ExistsAt` → **def**
`ExistsAt _w s := ∃ p, A s p` (to be is to act; the world-index is vacuous by
principle — `Means` takes no `World` parameter, so agency is not
world-located — while the existential does the real work: only actors exist).
`Person s` unfolds definitionally to `∃ p, Means s p` (via `Intentional`;
kind-preds `:= True`; `A := Means`), so `AxPersonStability : ∀ s, Person s →
NecessarySubject s` is now a **theorem** (**`{}`**, name kept per M1
precedent). Measured (`#print axioms`): T14 family (C42–C45) → `{}`
  after the plurality-discharge (2026-09-17); C18/C34 → `{AxGlobalGround, Ground}`;
  C15/C16/C17/C60 → `{Ground}`;
  C32 → `{AxPersonalGround, GroundProp}`; `Cogito` still `{}`.
**Axiom inventory 8 → 6 declarations** (−`ExistsAt`, −`AxPersonStability`);
substantive axioms unchanged in kind (SEM/META only). M2 (`ALONE_EXCLUDED`)
was untouched by this batch: `Alone` never mentions `ExistsAt` — this batch
proved *persistence*, not plurality; M2 was later closed by the
plurality-discharge (2026-09-17, `neverAlone`/`aloneExcluded`, C74).
Honestly recorded costs: the world-index is vacuous (declared, not hidden);
`T14_world` is trivially witnessed (same act in all worlds); T7/T8
"necessary" turns agent-flavored (grounded by an acting subject).

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
| C15 | §24a | `Truthmaker.groundPrinciple_atom` | PROVEN | `{Ground}` (VOCAB — footprint is the statement's own vocabulary; proof is a definitional collapse, `P → P`; see C60; esse-est-agere batch drops `ExistsAt`, now a def) |
| C60 | §24a (RAA) | `Truthmaker.noGround_selfRefutes` | PROVEN | `{Ground}` (VOCAB — denial refutes itself by definition: `TrueAt w (atom n)` unfolds to `∃e, ExistsAt w e ∧ Ground e (atom n)` with `ExistsAt` now agency itself, so the denial is `∃e… ∧ ¬∃e…`; companion of C15) |
| C16 | §22 | `Truthmaker.lawExcludedMiddle` | PROVEN | `CL + {Ground}` (A2: AxOr/AxNot dropped; esse-est-agere drops `ExistsAt`) |
| C17 | §23 | `Truthmaker.nonContradiction` | PROVEN | `{Ground}` (A2: AxAnd/AxNot dropped; no propext; esse-est-agere drops `ExistsAt`) |
| C18 | T7 | `Modal.T7_necessaryReality` (atom-restricted: `(n : Nat)`, `NecessarilyTrue (atom n)`) | PROVEN | `{Ground}` (VOCAB — batch A2-swap-theorem: `AxGlobalGround` axiom → theorem) |
| C19 | T7 | `Modal.T7_excludedMiddleInstance` (deleted from barrel) | BLOCKED | missing lemma `∃ e, Ground e (or θ (not θ))` given EM-necessity — no existential compound ground is forced by structural `TrueAt` (transcript: `formal/Spikes/Spike_A6_probe.lean`) |
| C20 | T7 | `Modal.noNecessaryTruthIfAllContingent` (atom-restricted: `∀ n`) | PROVEN | `{Ground}` (VOCAB — as C18) |

Declared (Level 1): `Ground` (world-rigid, D6; now over `Subject`) is the one
remaining semantics axiom; `ExistsAt` is now the agency *definition*
(esse est agere, 2026-09-17 — was VOCAB/SEM axiom, D4); `actualWorld` (def, SEM —
shrinks C18–C20; was axiom); `AxGlobalGround` (theorem, atom-restricted,
batch A2-swap-theorem — former SEM axiom, D7; the compound EM instance is
BLOCKED, C19). `Entity := Subject` is a *definition* (C2, 2026-09-15 — the Q2/D11
identification, no longer an axiom); `EntityOf` is the identity (dissolved).
A2 (2026-09-16): `AxOr`/`AxAnd`/`AxNot` deleted — the connective truthmaker
clauses are now **PROVEN theorems** (structural `TrueAt`, C15–C17).

## Level 2 — agency and person (`Logos.Agency`, `Person`, `Alternatives`, `Order`, `GroundPerson`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C58 | §1 fnd | `Agency.noCogito_selfRefutes : (¬∃s p, A s p) → False` — **denial refuted by exhibition** | PROVEN | `{}` (the silent origin is exhibited definitionally; no axiom cited) |
| C68 | §1 fnd | `Agency.Cogito : ∃ s p, A s p` — **the choosing subject exists, proven** | PROVEN | `{}` (witness `Sum.inl ()`: the silent origin sustains every posit; definitional subject, 2026-09-17) |
| C59 | §27 | **M5** `Spike_M5.strongTruthExists : ∃ τ : Semantics.Form, Semantics.NecessarilyTrue τ` — "Strong Truth Exists" resident axiom-free ("há certo E há errado"; spike-only, outside barrel) | PROVEN (spike) | **`{CL}`** (C37 lever) |
| C21 | §1/T1 | `Plurality.T1_subjectExists` (re-homed from Agency by A1) | PROVEN | `{}` (kind-preds `Agent`/`Rational` are defs; datum now the exhibited theorem `Cogito`) |
| C22 | T2 | `Agency.T2_contentExists` | PROVEN | **`{}`** — `Content _ := True` (def), `True` witnesses content; cogito not needed (was `{cogito}` + 6 kind-preds) |
| C23 | T4 | `Plurality.T4_agentExists` (re-homed from Agency by A1) | PROVEN | `{}` (as C21; `Agent` is `:= True`, def — agent existence is analytic) |
| C24 | T5 | `Plurality.T5_personExists` (re-homed from Person by A1) | PROVEN | `{}` (as C21) |
| C25 | §24b | `Person.inseparability_24b` | PROVEN | `CL` (vocab-only — no substantive axiom; see VOCAB.md) |
| C26 | **T9 (new)** | `Alternatives.T9_incompatibleAlternatives` | PROVEN | `{}` (E0) |
| C27 | §13 | `Alternatives.incompatible_with_negation` | PROVEN | `{}` (E0) |
| C28 | T6 | `Order.T6_fallibility` | PROVEN | `{}` (from the exhibited act + `Core.someFalse`) |
| C29 | T6 | `Order.T6_truthTranscendsWill` | PROVEN | as C28 |
| C30 | §8 | `Order.correctness_distinct` | PROVEN | `CL` (defs act-relative §8 `Correct s p := A s p ∧ T p`) |
| C31 | §9 | `Order.consequence_preserves_truth` | PROVEN | `{}` (E0) |
| C32 | T8 | `GroundPerson.T8_personalGround` | PROVEN↑ | `{AxPersonalGround, GroundProp}` (esse-est-agere drops `ExistsAt`) |
| C33 | T8 | `GroundPerson.present_feature_is_grounded` | PROVEN↑ | `{GroundProp, GroundPrincipleProp}` |
| C34 | T8 | `GroundPerson.necessary_truth_has_necessary_grounder` (atom-restricted: `(n : Nat)`) | PROVEN | `{Ground}` (VOCAB — as C18) |

Declared (Level 2): vocabulary now definitional — `Subject := Unit ⊕ Prop`
(the underlier: silent origin + posited contents), `State := Prop`
(truth-bearers), `Initiates` (field-toward-posit, by cases on the subject);
`Exists`/`Content` and
`Agent`/`Rational` are *analytical definitions* (`:= True`, batches
cogito-rethinking + Tier1 — no longer axioms). `Means` is defined by the
act-as-initiation rebase (2026-09-17):
`Means s p := ∃ w w', Initiates s w w' p`.
**THEOREM (definitional subject, 2026-09-17):** `Agency.Cogito : ∃ s p, A s p`
— choosing-subject existence is exhibited (witness `Sum.inl ()`), no longer
the unconditional TRANS axiom of M0. The A1 experiment (cogito deleted, datum
derived under `AxTwoSubjects`) stays superseded; the M0 forced-foundation
interlude is retired with its degenerate `fun h => h Cogito`. The derived
chain stands on the exhibited act — the former
`{Cogito, Initiates, State, Subject}` footprints of C21/C23/C24/C28-C30/C39/
C48/C52-C57 are now `{}` (measured, §Annex), and `CL` where `by_cases` is used.
Act structure is *defined* (B1, now Tier1-collapse over the act-as-initiation
rebase): `A s p := Means s p` with `Means s p := ∃ w w', Initiates s w w' p` —
the bundled act IS the meaning-act (an initiation positing content); the
`act_implies_*` are `rfl`-level theorems.
`GroundProp`, `GroundPrincipleProp` (SEM reflection of §24a);
`AxPersonalGround` (META, D9 — the remaining price of "personal").
`Realizes := GroundProp` (def, B2) — `AxGroundBearing` dissolved (was META).
**THEOREM (esse est agere, 2026-09-17):** `AxPersonStability : ∀ s, Person s →
NecessarySubject s` — persons persist, proven from `Person → Intentional →
Means` with `ExistsAt` as agency itself (M3 PERSON_PERSISTS dissolved; name
kept per M1 precedent). T14 now stands on `AxTwoSubjects` alone.

## Deferred / blocked

| ID | Prose | Status | Missing |
|----|-------|--------|---------|
| F1a | §13–§15 choice-existence (`∃s p q`, `Chooses s p q`) | PROVEN | `person_chooses`/`choiceExists` `{}` + `judge_commits` `CL` (choice-realism batch, C51–C52/C55) |
| F1b-weak | §15 freedom of the actor (`FreeWill ↔ ◇Choose ∧ ◇Choose¬`, origin) | PROVEN | `freeWillOrigin`/`judgeIsFree`/`originFreedomSelfRefutes` `{}` (freedom split 2026-09-17: the act's subject — the origin, the judge right/wrong commits — can both choose `p` and choose `¬p`; the "could not have chosen otherwise" denial self-refutes, C69/C71/C72) |
| F1b-strong | §15 world-level alternativity | BLOCKED | **vocabulary gap** (not a proof gap): no world-varying choice predicate exists — every predicate is world-invariant, so `NecessityPH` over any of them collapses to identity; missing `ChoiceAt : World → Subject → Prop → Prop` (genuinely world-varying; a new SEM/META bridge, deliberately deferred) |
| F2 | §21 teleology (`Ought → Goal`) | DEFERRED | deontic layer (normativity → telos) |
| F3 | §28 Good (`§20 → bem`) | DEFERRED | moral good from logical normativity not yet derived |
| F4 | §28 Love | PROVEN | `Love.T13_someoneLovable` (C41) under the derived plurality — no bridge (definitional subject, 2026-09-17; old bridge `AxTwoSubjects` retired) |
| F5 | §28 EternalRelation | PROVEN | T14 under the derived plurality + esse est agere (AxPersonStability theorem); `T14_canonicalRigid` strengthens it to a world-rigid canonical pair |
| F6 | §28 Trinity | DEFERRED | no argument exists yet (§28/§29) |
| Q7.2 | weaker `AxGlobalGround` | ANSWERED | answered by batch A2-swap-theorem: for atoms the swap needs no premise at all (definitional via world-vacuous `ExistsAt`); the compound instance is unforced, not weaken-able (DESIGN.md) |

## Level 3 — modal, choice, interpersonal value (new: poem chain)

| ID | Poem | Lean theorem | Status | Axiom footprint |
|----|------|--------------|--------|-----------------|
| C35 | P2 | `Core.negatedAbsolutes : ¬ (N_T ∨ N_F)` | PROVEN | `{}` (E0) |
| C36 | P2 | `Core.rightWrongDistinction : ¬ N_T ∧ ¬ N_F` | PROVEN | `{}` (E0) |
| C37 | P2 | `Semantics.bothNecessarilyTrueAndFalse` | PROVEN | `CL` |
| C38 | P2 | `Necessity.necDistinction : Necessity (¬ N_T ∧ ¬ N_F)` | PROVEN (was AXIOM) | `{}` (E0; C1: identity-model alias; world content = C37) |
| C39 | P4 | `Choice.T11_choiceField` | PROVEN | `{}` (choice field exhibited with the act) |
| C40 | P5/P7 | `Plurality.T12_twoPersons` | PROVEN | `{}` (definitional subject, 2026-09-17: canonical pair of `Person.twoPersonsFromSubject` — origin + addressee; no right/wrong premise, no bridge) |
| C41 | P7 | `Love.T13_someoneLovable` | PROVEN | `{}` (via C40) |
| C48 | P1/§1 | `Plurality.cogito_from_T12` | PROVEN | `{}` (cogito as corollary of the exhibited `Cogito`; plurality also forces the datum, the datum is not *grounded* on plurality) |
| C49 | §13/IM_STUPID | `Choice.meaning_needs_subject` + `Choice.meaning_I_needs_subject` (definitional form: `Meaning_I p → ∃s, Means s p`) | PROVEN | `{}` (analytic; vocab-only — no substantive axiom; see VOCAB.md) |
| C50 | §14 | `Choice.incompatible_self_negation` | PROVEN | **`{}`** (pure logic — the field around any meaning-act) |
| C51 | §14/IM_STUPID | `Choice.person_chooses : Person s → ∃p q, Chooses s p q` — **subject ⇒ choice** (was mislabeled "OPEN" gap) | PROVEN | `{}` (vocab-only — no substantive axiom; see VOCAB.md) |
| C52 | §14 | `Choice.choiceExists` | PROVEN | `{}` (choice is real, from T5 — now `Plurality.T5_personExists`) |
| C53 | §14 | `Choice.noChoice_selfRefutes : (¬∃s p q, Chooses s p q) → False` | PROVEN | `{}` — denying choice is itself an act = a choice |
| C54 | IM_STUPID §2 | `Choice.JUDGE_COMMITTED : (¬N_T ∧ ¬N_F) → ∃s p q, Chooses s p q` — **right/wrong ⇒ choice** | PROVEN | `{}` (premise unused: choice already holds via C52) |
| C55 | §8/§14 | `Order.judge_commits : ∃s p q, A s p ∧ (Correct s p ∨ Incorrect s p) ∧ Chooses s p q` — the judge IS a chooser | PROVEN | `CL` (defs act-relative §8) |
| C56 | P6 | `Value.alone_no_other_help_harm` | PROVEN | `{}` (M1: `Affects` is now the A3 definition `s ≠ t`, so the P6 lemma loses its axiom — measured; see VOCAB.md) |
| C57 | §26 | `Choice.noSubject_selfRefutes : (¬∃_s : Subject, True) → False` — **a subject exists is un-denyable**: the denial is itself an act/choice of a subject; `choiceExists` (C52) supplies the resident witness | PROVEN | `{}` — formal record of §26 "não existe sujeito do ato presente"; the act-datum is the exhibited theorem `Cogito`, never a consequence of the plurality bridge |
| C42 | P8 | `Love.T14_eternalRelation` | PROVEN | `{}` (M1: `Affects := s ≠ t` def + `AxPersonsAffect` theorem vanish; esse-est-agere: `AxPersonStability` is a theorem and `ExistsAt` a def; plurality-discharge: `AxTwoSubjects` retired — canonical pair of `Person.twoPersonsFromSubject`) |
| C43 | P8 | `Love.T14_content` | PROVEN | as C42 |
| C44 | P8 | `Love.T14_world` (`NecessityPH`) | PROVEN | as C42 (world-anchored honest □) |
| C45 | P8 | `Love.T14_square` (alias `Necessity`) | PROVEN | as C42 (image of the old statement shape) |
| C46 | P5 | `Value.valueInterpersonal_of_split` | PROVEN | `{}` (recovery theorem: exact old statement; M1: `Affects`/`AxPersonsAffect` gone; derived outright from `Person.twoPersonsFromSubject`) |
| C47 | P5/P7 | `Plurality.T12_directedPair` | PROVEN | `{}` (chain node — M1: distinctness is already the forward direction under A3, so the pair wears its own inequality; T14 built on this node) |
| C61 | P3 | `Choice.rightWrong_implies_someone_means` — "há certo e há errado → há alguém para quem algo significar" (the full conditional of poem L18) | PROVEN | `{}` (`JUDGE_COMMITTED` C54 ∘ `rightWrongDistinction` C36; the analytic half "significado → sujeito" is C49) |
| C62 | P3 | `Order.rightWrong_implies_meaning` (+ `Order.rightDistinctWrong_implies_meaning`) — "direito e errado precisam de significado": `Correct`/`Incorrect` são agora ato-relativos (forma literal §8 `Correct(A(s,p))`), logo right/wrong desdobra-se num ato `Means`; `Order.rightWrongDistinction_implies_meaning` fecha o condicional poético completo (`CL`) | PROVEN | `{}` (pure bridges; full conditional `CL`; **sem axioma substantivo**; o modelo vazio já não satisfaz o antecedente; ver VOCAB.md/BRIDGE.md) |
| C69 | §15/F1b | `Choice.freeWillOrigin : FreeWill (Sum.inl ()) p` — **the origin can choose both ways**: the act's subject (the judge right/wrong commits) can choose `p` and can choose `¬p` | PROVEN | `{}` (constructive — the origin means every content; instantiation at `someWorld`, deliberately not `canChoose_unfold`) |
| C70 | §15/F1b | `Choice.noFreeWillPosited (q p) : ¬ FreeWill (Sum.inr q) p` — **posited contents cannot choose otherwise** (a self-posited `inr q` can only ever mean `q`) | PROVEN | `CL` (double negation on the `CanChoose → q = p` extraction) — no paradox: such subjects are never the judge right/wrong commits (that witness is the free origin) |
| C71 | §15/F1b | `Choice.originFreedomSelfRefutes : (¬ FreeWill (Sum.inl ()) p) → False` — **"I could not have chosen otherwise" self-refutes**: the denial is itself an act of the free origin | PROVEN | `{}` — the freedom paradox dissolves: the determinist alternative cannot be asserted performatively |
| C72 | §15/F1b | `Choice.judgeIsFree : ∃ s, Person s ∧ ∃ p, FreeWill s p` — the chooser right/wrong commits is free | PROVEN | `{}` (judge = origin via `T5_personExists`; choice-in-the-freedom-sense exists for the act's subject) |
| C73 | P5/P7 | `Person.twoPersonsFromSubject` — **the canonical pair, definitional**: the origin `Sum.inl ()` and the addressee `Sum.inr True` are two distinct persons by what a subject is | PROVEN | `{}` (plurality-discharge, 2026-09-17: no plurality axiom — `AxTwoSubjects` retired; `Person (Sum.inr True)` via `Means (Sum.inr True) True`; distinctness by constructors) |
| C74 | P5 | `Value.aloneExcluded : ¬ ∃ s, Person s ∧ Alone s` — **`ALONE_EXCLUDED` is now a theorem** (`Value.neverAlone : ∀ s, ¬ Alone s`): no subject is alone, the definitional field always supplies an other | PROVEN | `{}` (kills the M2 lone-subject countermodel; the named missing lemma that justified `AxTwoSubjects` no longer exists) |
| C75 | P7 | `Person.everyContentIsAPerson : ∀ p, Person (Sum.inr p)` (+ `Person.positedDistinct : Sum.inr True ≠ Sum.inr False`) — **the plenum seed**: every content, raised to a subject, is a person; incompatible contents are distinct persons | PROVEN | `{}` (honest limit: distinctness of such persons is kernel-visible only for incompatible contents — proposition equality is `propext`-collapsed) |
| C76 | P8 | `Love.T14_canonicalRigid` — **the world-rigid canonical pair**: the origin and the addressee love each other and exist in every world (the *same* pair, `∀ w`) | PROVEN | `{}` (stronger than C42: "Amar é … necessário (de alguma forma)" made literal; no stability bridge needed — esse est agere) |

Declared (Level 3): **M1 (A3, 2026-09-16): `Affects` is now a structural
DEFINITION (`Affects s t := s ≠ t`), no longer the primitive value axiom, and
`AxPersonsAffect` is a THEOREM of that definition** (distinct persons are
distinct — `Or.inl hne`). `Helps`/`Harms` are its definitional projections
(`:= Affects`); `help_affects`/`harm_affects` are `rfl`-theorems;
`Entity`/`EntityOf` dissolved (C2). The plurality bridge `AxTwoSubjects`
(META) is **RETIRED** (plurality-discharge, 2026-09-17): the canonical pair of
`Person.twoPersonsFromSubject` (C73) is a theorem `{}`, and the M2
lone-subject consistency model is superseded — `neverAlone`/`aloneExcluded`
(C74) make solipsism structurally impossible:
`formal/Spikes/Spike_A4_2.lean` built its witness on the OLD axiomatic
`Subject`; the definitional `Subject := Unit ⊕ Prop` has ≥2 inhabitants,
both persons (C73/C75). `AxPersonStability` was the SEM bridge for
world-persistence of persons (M3 spike BLOCKED) — **now a theorem** (esse est
agere, 2026-09-17): `Person → Intentional → Means` with `ExistsAt` as agency.
T14 stands on the derived pair + esse est agere alone.
`Loves` is a *definition* (`:= Affects`, C4), no longer an axiom;
`AxValueInterpersonal` and `AxEternalLove` are dissolved (split / replaced).
M2 is closed: no consistency model for a single subject exists under the
definitional field (the price's *model-justification* dies with the price).
Modal layer is derived (C1): `Necessity: Prop → Prop` is a *definition*
(identity-model alias) and `NecessityPH : (World → Prop) → Prop` the
semantics-grounded operator; `necK/necT/nec4` (alias) and `necKPH/necTPH/nec4PH`
are theorem; `necDistinction` is a theorem. No modal axiom remains.

## Level 2c — the act as initiation (`Logos.Initiation`, 2026-09-17)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C63 | §1 | `Initiation.branches_not_transfer : Branches R → ¬ IsTransfer R` — **iniciação ≠ transferência**: uma relação com alternativas genuínas não é o gráfico de função nenhuma | PROVEN | **`{}`** (lógica pura — sem axioma, sem vocabulário) |
| C64 | §1 | `Initiation.originates_not_transfer : Branches (Moves s) → ¬ IsTransfer (Moves s)` — o movimento do sujeito não é transferência | PROVEN | `{}` |
| C65 | §1/T5 | `Initiation.person_iff_originates : Person s ↔ Originates s` — a pessoa é exactamente o sujeito que origina o ato | PROVEN | `{}` |
| C66 | §1 fnd | `Initiation.Cogito_Init : ∃ s : Subject, Originates s` — o ato exibido relido como fundamento-iniciação | PROVEN | `{}` (relabel of the exhibited `Cogito`) |
| C67 | §1 fnd | `Initiation.noInitiation_selfRefutes : (¬∃ s, Originates s) → False` — negar que alguém origine um ato refuta-se (a origem é exibida) | PROVEN | `{}` (mirror of C58) |

Declared (Level 2c): `State := Prop` (the sustained field) and `Initiates`
(field-toward-posit, by cases on the subject) are *definitions*;
`Means` is the *definition* `Means s p := ∃ w w', Initiates s w w' p` and
`A s p := Means s p`. The subject is exhibited, not postulated: the
definitional underlier supplies the witness, so `Cogito_Init` is derived
(`{}`). Initiation ≠ transfer (C63) is a kernel theorem with empty footprint.

## Faith / DEFERRED

| ID | Poem | Status | Note |
|----|------|--------|------|
| FAITH-1 | P2 necessity | → PROVEN | dissolved in C1: `necDistinction` is now a theorem (C38); world content = C37 |
| FAITH-2 | P8 eternal love | → PROVEN | dissolved in C4: replaced by `AxPersonStability` (theorem, esse-est-agere) + the derived plurality (plurality-discharge: retired `AxTwoSubjects`); T14 is a theorem `{}` (C42–C45, C76) |
| F7 | §15 the bipolar half of freedom | PROVEN/`{}` (weak) · BLOCKED (strong) | = F1b split (2026-09-17): the origin's both-ways capacity is proven (`freeWillOrigin` `{}`); world-level alternativity blocked on missing world-varying vocabulary (`ChoiceAt`) |
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
  (Superseded 2026-09-17 by the plurality-discharge: `ALONE_EXCLUDED` is now
  the theorem `Value.aloneExcluded` C74, and `AxTwoSubjects` was retired.)
- **C3-II** (single exclusion attempt, one-shot): tried to derive a second
  subject directly from the denial of `Alone` via `cogito + T6 + P6 + defs`.
  Stuck (x2_spikeC): the one-person scenario is consistent with every theorem;
  the interpersonal bridge is genuinely separate. Record in DESIGN.md D14b.
  (Superseded 2026-09-17: the one-person scenario is NO LONGER consistent —
  `neverAlone` (C74) refutes `Alone s` outright.)
- **C4** (`Loves := Affects`, structural love): `Loves` is redefined as a
  *definition* (`Affects`); `AxEternalLove` (FAITH/META, D14b) is dissolved.
  A new bridge `AxPersonStability : ∀ s, Person s → NecessarySubject s`
  (SEM, poem's "de alguma forma") carries the *eternal* half of T14, attached to
  the relata. T14 is restated as four theorems (`T14_eternalRelation` with
  `NecessarySubject` relata; `T14_world` with `NecessityPH`; `T14_square` the
  alias-□ image; `T14_content`). FAITH-2 dissolves. Loves is no longer an axiom.
  Exclusion spike x2_spikeD stuck: `Person` structure (T5) gives no fact about
  world-persistence of the entity-correlate. (Superseded 2026-09-17 by
  esse-est-agere: `AxPersonStability` is now a theorem, `ExistsAt` a def.)

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
  real semantics axioms, now over `Subject`. (Superseded 2026-09-17 by
  esse-est-agere: `ExistsAt` is now the agency def; `Ground` alone remains.)
  `{Entity, EntityOf}` leave every
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
  (All three superseded 2026-09-17: `ALONE_EXCLUDED` → C74 theorem;
  `PERSONS_BEAR` → `AxPersonsAffect` theorem of A3; `PERSON_PERSISTS` →
  esse-est-agere, `AxPersonStability` theorem.)

## Batch actualWorld-def + T12_directedPair (2026-09-15) — free fortifications

Two honest cuts with no price, per the reducibility audit (§3 of the plan):
the previous agent's vetoed `someTrue` classical proof is **untouched** — it
remains the explicit reductio that exhibits the transcendental content, and
its footprint stays `CL`.

- **actualWorld → def** (`Modal.lean`): `def actualWorld : World :=
  fun _ => Logos.Semantics.TV.t` (precedent: `Necessity.someWorld`). T7
  invokes `Ground e τ` at *some* fixed world; nothing depends on which, so the
  "present world" is a modeled choice, not a datum. Axiom count 23 → 22;
  C18–C20 lose `actualWorld` (now `{AxGlobalGround, Subject, ExistsAt, Ground}` —
  at batch time; esse-est-agere drops `Subject` (def) and `ExistsAt` (def)).
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

Summary counts (A2-swap-theorem, measured 2026-09-17):

- **PROVEN** (no axioms beyond `CL` where marked) — **44 axiom-free** (`{}`):
  C1, C2, C4–C9, C11, C21–C24, C26–C29, C31, C35, C36, C38, C39,
  C48–C54, C56–C58, C61–C68 (C62: pure bridges `{}`; full conditional `CL`),
  C69, C71, C72 (freedom split — the origin's both-ways capacity), F1a
  (choice-existence resolves to a kernel step).
  `CL`-only: C3, C10, C12–C14, C25, C30, C37, C55, C70 (+ C59 spike, outside barrel).
  Vocab-only (`{Ground}` — the statement's own vocabulary): C15, C16, C17,
  C18, C20, C34, C60 (denial refutes itself by definition — RAA;
  esse-est-agere drops `ExistsAt`, now a def; A2-swap-theorem drops
  `AxGlobalGround`, now a theorem).
  C62 (`rightWrong_implies_meaning`) is the pure bridge: with the §8
  act-relative `Correct`/`Incorrect`, right/wrong unfold to a `Means`-act;
  the bare-distinction form `rightWrongDistinction_implies_meaning` is `CL`.
- **PROVEN↑** (under flagged SEM/META only — no foundation axiom remains):
  C32, C33, C40–C47, F4, F5.
  (`Cogito` is proven — the M0 forced-foundation axiom is retired, its
  degenerate `fun h => h Cogito` with it. `AxPersonalGround` (META, T8)
  is the remaining Level-2 price alongside `GroundPrincipleProp` (SEM);
  `AxTwoSubjects` was **retired** by the plurality-discharge (2026-09-17 —
  canonical pair C73, `ALONE_EXCLUDED` C74);
  `actualWorld` is a def;
  `Exists`/`Content`/`Agent`/`Rational` are analytical defs; `Affects` is the A3
  definition `s ≠ t`; `AxPersonsAffect`, `AxPersonStability` and now
  `AxGlobalGround` (atom-restricted) are theorems.)
- **BLOCKED**: C19 (T7 excluded-middle instance — missing lemma `∃ e,
  Ground e (or θ (not θ))`; transcript in `formal/Spikes/Spike_A6_probe.lean`);
  F1b-strong (world-level alternativity — **vocabulary gap**, not a proof gap:
  no world-varying choice predicate exists; missing
  `ChoiceAt : World → Subject → Prop → Prop`, a new SEM/META bridge,
  deliberately deferred).
- FAITH layer: **empty** (FAITH-1 → C38, FAITH-2 → C4); no claims live at the faith boundary.
- Axioms dissolved (all batches): `T`, `tschema`, `Entity`,
  `EntityOf`, `help_affects`, `harm_affects`; `Affects` (axiom → def, M1);
  `actualWorld` (axiom → def); `Chooses` (axiom → def);
  `Exists`/`Content`/`Agent`/`Rational` (axioms → defs);
  `AxOr`/`AxAnd`/`AxNot` (axioms → theorems via A2);
  `AxPersonsAffect` (axiom → theorem, M1 via A3);
  `Subject`/`State`/`Initiates` (axioms → defs, definitional subject);
  `Cogito` (axiom → theorem, definitional subject);
  `ExistsAt` (axiom → def, esse est agere);
  `AxPersonStability` (axiom → theorem, esse est agere);
  `AxGlobalGround` (axiom → theorem, atom-restricted, A2-swap-theorem);
  `AxTwoSubjects` (axiom → **retired**, plurality-discharge 2026-09-17 — its
  content moved into the definition of a subject: the canonical pair C73 is
  a theorem `{}` and `ALONE_EXCLUDED` is C74; the M2 lone-subject model is
  superseded).
  A1 removed `cogito`; M0 restored it as the FORCED foundation (+1);
  the definitional-subject batch proves it (−1).
  Net inventory: **4 declarations** + `CL`:
  `Ground`,
  `GroundProp`, `GroundPrincipleProp`, `AxPersonalGround`.
- `sorryAx` count across all modules: **0**.
- Verification: `lake build` green (36 jobs, seconds, Lean core only); zero
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
  `Subject` stays an axiom as a *pure-sort postulate* (at Tier1 time): an empty `inductive`
  `Subject` refutes `∃ s` (breaks `Cogito`/T12 → `False`); `Subject :=
  Bool`/`fin 2` would smuggle "exactly two"; `ℕ` asserts infinity; `Unit`
  kills `s₁ ≠ s₂`. Recorded in the file and in DESIGN.md D-Tier1.
  (Superseded 2026-09-17 by the definitional-subject batch:
  `Subject := Unit ⊕ Prop` — the neutral witness `Sum.inl ()` smuggles
  nothing beyond the datum itself.)
- **Choice-realism** (`Choice.lean`, `Order.lean`): the old `def Chooses :=
  False` placeholder made choice unrepresentable — the mislabeled "subject ⇒
  choice" gap. New real definition `Chooses s p q := A s p ∧ Incompatible
  p q`, plus theorems: `incompatible_self_negation` (pure logic `{}` —
  the field around any meaning-act is non-empty), `meaning_needs_subject`,
  `person_chooses` (**subject ⇒ choice**, was OPEN; `{Initiates, State, Subject}`, no
  cogito — at batch time; now `{}`), `choiceExists`, `noChoice_selfRefutes` (denying choice is itself a
  choice), `JUDGE_COMMITTED` (**right/wrong ⇒ choice**), `judge_commits`
  (the §8 judge IS a chooser, `CL + {Cogito, Initiates, State, Subject}` post-M0 — now `CL`),
  `canChoose_unfold` (the aliased-◇ choice collapses to real choice),
  `noSubject_selfRefutes` (a subject exists is un-denyable: the denial is itself
  an act; `{Cogito, Initiates, State, Subject}` post-M0 — now `{}` — formal record of §26).
  `Order.lean` now imports `Logos.Choice` (no cycle).
- **F1 split**: F1a (choice-existence, transcendental) is PROVEN↑ (at batch
  time; now PROVEN); F1b
  (bipolar `◇Choose ∧ ◇Choose¬`, world-level on `NecessityPH`) stays
  DEFERRED — a subject may mean `p` without being able to mean `¬p`.
- Measured (at batch time): `#print axioms` statements **47** (was 39; +7 Choice, +1 Order);
  axiom-free theorems **11** (adds `incompatible_self_negation`); `sorryAx:
  0`; `lake build` green, zero warnings. (Now: 40 axiom-free; see summary.)

## Batch A1-cogito-removal (2026-09-16, superseded by M0) — axiom deleted, content re-homed

A1 was genuine but mechanical: it relocated the datum, not restructured it.
**M0 (2026-09-16, `FORCED_SUBJECT.md`) recognizes the A1 move as the bug the
forced-foundation batch fixes**: deleting cogito and anchoring on T12/AxTwoSubjects
made choosing-subject existence a *consequence* of plurality — the very datum
it must precede. M0 restores cogito as `Agency.Cogito` (FORCED foundation),
T1/T4/T5/cogito_from_T12 re-anchor there, and the A1-derived footprints
`{AxTwoSubjects, Initiates, State, Subject}` become `{Cogito, Initiates, State, Subject}` (measured).
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
  (2026-09-17: all `{}` — the guard holds trivially.)

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
  free VOCAB); `Ground e (or …)` neither asserted nor denied. (Superseded
  2026-09-17 by esse-est-agere for the `ExistsAt` half: existence is now
  agency itself; `Ground` alone stays free VOCAB.)
- Measured footprints (`#print axioms`, scratch `/tmp/opencode/aud.lean`;
  at batch time — `Subject` since demoted to a definition):
  `groundPrinciple_atom` = `{Subject, ExistsAt, Ground}`;
  `noGround_selfRefutes` = `{Subject, ExistsAt, Ground}` (C60 — the denial
  of atom-grounding refutes itself by definition: `TrueAt w (atom n)` unfolds
  to the existential clause, so the denial is `∃e… ∧ ¬∃e…`; RAA, no
  substantive axiom — this is also the justification for C15 being PROVEN,
  not a price);
  `lawExcludedMiddle` = `CL + {Subject, ExistsAt, Ground}`;
  `nonContradiction` = `{Subject, ExistsAt, Ground}` (**no propext** — the
  re-proof avoids `rw` on `Iff`); `T7_necessaryReality`/`T7_excludedMiddleInstance`/
  `noNecessaryTruthIfAllContingent` unchanged from before.
  (2026-09-17: `Subject` demoted — drop it from all four; esse-est-agere
  also drops `ExistsAt` — now `{Ground}`, `CL + {Ground}`, `{Ground}`.)
- Measured totals: axiom declarations **15 → 12**; `#print axioms` statements
  stay **47** (Truthmaker audit still 3); `sorryAx: 0`; `lake build` green,
  zero warnings.

## Batch M0+M1 (2026-09-16) — SUBJECT IS FORCED + definitional affectivity (`FORCED_SUBJECT.md`)

(Historical: M0's FORCED axiom is retired by the definitional-subject batch,
2026-09-17 — `Cogito` is now a theorem, `{}`. What follows is the record
as it stood.)

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
  C30/C55 at `CL +` — all `{Cogito, Initiates, State, Subject}`.
- **M1 — A3 definitional affectivity (`Value.lean`).** `def Affects s t :=
  s ≠ t` (bearing = distinctness; the lone subject affects nothing, P6);
  `def Helps`/`Harms := Affects`; **`AxPersonsAffect` → THEOREM**
  (`Or.inl hne`). Measured: `alone_no_other_help_harm` → `{Subject}` (C56);
  `T12_directedPair`/`valueInterpersonal_of_split` → `{AxTwoSubjects, Initiates, State,
  Subject}` (C46/C47); `T14_*` (C42–C45) → `{AxTwoSubjects, AxPersonStability,
  ExistsAt, Initiates, State, Subject}` (no `Affects`, no `AxPersonsAffect`).
- **Axiom inventory 12 → 11:** +`Cogito` (FORCED) −`Affects` (→ def)
  −`AxPersonsAffect` (→ theorem). `#print axioms` statements 47 → 50
  (adds M0 audit lines). `sorryAx: 0`; `lake build` green, zero warnings.
- **Spike verdicts (all BLOCKED, transcripts in `formal/Spikes/`):**
  * M2 `Spike_A4_2.lean`: `ALONE_EXCLUDED` — the lone-subject consistency
    witness is kernel-checked in-file (single inhabitant refutes the target
    over the whole allowed surface); `AxTwoSubjects` stands as a **price
    justified by a model**. (Superseded 2026-09-17 by the plurality-discharge:
    the witness is built on the OLD axiomatic `Subject`; the definitional
    `Subject := Unit ⊕ Prop` has ≥2 inhabitants, both persons — C73 — so the
    lone-subject model is void and `AxTwoSubjects` is retired; `ALONE_EXCLUDED`
    is now the theorem C74.)
  * M3 `Spike_PersonStability.lean`: `PERSON_PERSISTS` — a necessary relata
    `e₀` exists (T8 content) but `Realizes e₀ f` does not identify it with the
    act's subject; `NecessarySubject s` needs `ExistsAt w s` and no rule links
    `Means` to `ExistsAt`; `AxPersonStability` stays priced (SEM). (Superseded
    2026-09-17 by esse-est-agere: the rule is supplied by definition —
    `AxPersonStability` is now a theorem, `ExistsAt` a def.)
  * M4 `Spike_A6_probe.lean`: weaker `AxGlobalMirror` derives T7-**atom**
    (kernel-checked, no `AxGlobalGround`) but cannot cover the compound
    excluded-middle instance (A2 structural TrueAt has no existential ground
    for compounds) — `AxGlobalGround` **stays priced (smaller)**; recording
    only, not adopted. (Superseded 2026-09-17 by batch A2-swap-theorem:
    esse-est-agere's world-vacuous `ExistsAt` makes the atom swap itself a
    theorem — no axiom at all, weaker or otherwise; the compound instance
    C19 is recorded BLOCKED with its exact missing lemma.)
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
  (M5 verdict superseded 2026-09-17: the choosing subject IS proven —
  `Agency.Cogito`, `{}`, by definitional exhibition of the underlier.)

## Batch freedom-split (2026-09-17) — the "could not have chosen otherwise" paradox dissolved

Driven by the user: "if you could not have chosen otherwise, then choice does
not exist in the freedom sense. Which means right and wrong would not exist.
This is paradoxical. We need to make it clear that it can't be the case."

- **F1b splits in two.** F1b-weak (the performer's both-ways capacity) is
  PROVEN; F1b-strong (world-level alternativity) is BLOCKED at the **vocabulary**
  level — not a proof gap like C19.
- **`freeWillOrigin : FreeWill (Sum.inl ()) p`** (`{}`): the act's own subject —
  the origin, the witness of `Agency.Cogito`/`Plurality.T5_personExists` that
  `JUDGE_COMMITTED` commits to right-and-wrong — can choose `p` AND can choose
  `¬p`. From `Initiates (inl _) _ w' p := w' = p`: the origin means every
  content, so both choices are real; `CanChoose` reached constructively
  (instantiation at `someWorld`), deliberately not via the classical
  `canChoose_unfold`. **C69**.
- **`noFreeWillPosited : ¬ FreeWill (Sum.inr q) p`** (`CL`): the self-posited
  contents provably CANNOT choose otherwise — `inr q` can only mean `q`
  (`Means (inr q) p` iff `q = p`), so both-ways capacity would force
  `q = p ∧ q = ¬p`, impossible. **No paradox**: these subjects are never the
  judge right/wrong commits (that witness is the free origin). **C70**.
- **`originFreedomSelfRefutes : (¬ FreeWill (Sum.inl ()) p) → False`** (`{}`):
  "I could not have chosen otherwise" — asserted by the origin of the present
  act — is itself a both-ways act and refutes itself. The determinist
  alternative cannot be asserted performatively. **C71** — this is the
  kernel-checked dissolving of the user's paradox.
- **`judgeIsFree : ∃ s, Person s ∧ ∃ p, FreeWill s p`** (`{}`): the chooser
  that right/wrong commits is free — choice *does* exist in the freedom sense
  for the subject the undeniable right/wrong demands. **C72**.
- Measured (`#print axioms`, in-file audit lines): `freeWillOrigin` `{}`,
  `noFreeWillPosited` `{propext, Classical.choice, Quot.sound}` = `CL`,
  `originFreedomSelfRefutes` `{}`, `judgeIsFree` `{}`. `lake build` green
  (36 jobs), zero warnings. Axiom inventory unchanged: **5 declarations**.
- **Recorded limitation (F1b-strong, BLOCKED):** a genuine *world-level*
  alternativity `◇PH Choose ∧ ◇PH Choose¬` requires a world-varying choice
  predicate; every predicate below `Semantics` is world-invariant, so
  `NecessityPH` over any of them collapses to identity (`∀ w, P ⟷ P`, world
  inhabited). The missing vocabulary —
  `ChoiceAt : World → Subject → Prop → Prop` — is deliberately NOT added
  (a new SEM/META bridge; not forced by the current chain). This is a
  *vocabulary* gap, unlike C19's formulable-but-unproven lemma.

## Batch plurality-discharge (2026-09-17) — `AxTwoSubjects` retired; the other is the addressee

Driven by the project's own discovery: under the definitional subject
(`Subject := Unit ⊕ Prop`, 2026-09-17) two distinct persons are **derivable** —
the former META price is redundant and is discharged as a demotion, the poem's
interpersonal step is re-found on the *addressee*, and the eternal relation
becomes world-rigid.

- **The fact:** `Person (Sum.inr True)` holds (`Means (Sum.inr True) True`),
  `Sum.inl () ≠ Sum.inr True` by constructors — so
  `∃ s₁ s₂, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` unconditionally, `{}`. The
  second person is the *addressee*: a content positing itself — precisely the
  "alguém para quem significar" of the poem (P5/P7), not a second silent
  origin (one is all `Unit` can carry; any `Index ⊕ Prop` re-reading is
  behaviorally identical in `Means` — Track-B verdict: an equal-origin other is
  not a Λ-relatum, the other is inherently an addressee-content).
- **`Person.twoPersonsFromSubject`** (canonical pair, **C73**, `{}`): the
  origin `Sum.inl ()` and the addressee `Sum.inr True`.
- **`Value.neverAlone`/`Value.aloneExcluded`** (**C74**, `{}`): `∀ s, ¬ Alone s`
  (`otherSubject s ≠ s`) — so the named missing lemma `ALONE_EXCLUDED`,
  the *justification* of the bridge, is now a theorem and the M2 lone-subject
  consistency model (built on the pre-definition `Subject`) is void. The price
  was always, already, the definition.
- **Plenum seed (C75, `{}`)**: `everyContentIsAPerson : ∀ p, Person (Sum.inr p)` —
  every content raised to a subject is a person; `positedDistinct` for the
  extremes. Honest limit: distinctness is kernel-visible only for *incompatible*
  contents (proposition equality is `propext`-collapsed) — the plenum is
  unbounded in content, not in kernel-distinguishable members.
- **`Love.T14_canonicalRigid`** (**C76**, `{}`): the *same* pair (origin +
  addressee) loves in every world and both relata exist in every world —
  "Amar é … necessário (de alguma forma)" literal, strictly stronger than the
  old existential `{AxTwoSubjects}` form.
- **Cascade:** `valueInterpersonal_of_split` (C46) no longer needs the
  right-and-wrong premise; `T12_directedPair` (C47), `T13` (C41), `T14_*`
  (C42–C45), F4, F5 all → **PROVEN `{}`**.
- Measured (`#print axioms`, in-file audit lines): every touched node `{}`
  (no `CL` added). `lake build` green (36 jobs), zero warnings, `sorryAx: 0`.
- **Axiom inventory 5 → 4 declarations** (+`CL`): `Ground`, `GroundProp`,
  `GroundPrincipleProp`, `AxPersonalGround`;
  `AxTwoSubjects` → `RETIRED_AXIOMS` in `scripts/build_deduction.py` and the
  dissolved list; GAPMAP rows C40–C47/F4/F5 re-transcribed to the derived
  status (statuses are pure functions of the kernel; these cells now agree).
- **Philosophical record:** the "leap" was not lost and not faked — it was
  *located*: the interpersonal step lived in the 2026-09-17 decision that a
  subject is a self-positing content, and the addressee IS the other the poem
  needs. The prose registers (base.txt §28, T12–T14) adopt the addressee
  reading: "o outro é o conteúdo tornado sujeito".
