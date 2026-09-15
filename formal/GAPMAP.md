# GAPMAP.md — theorem ledger of Γ (generated from `#print axioms`, 2026-09-15)

Statuses: `PROVEN` (theorem, kernel-checked) · `PROVEN↑` (theorem under
flagged axioms) · `AXIOM` (declared) · `BLOCKED` (missing lemma named) ·
`DEFERRED` (out of scope of this milestone).

`CL` = `{propext, Classical.choice, Quot.sound}` (classical meta-logic, D1).

## Level 0 — performative core (`Logos.Core`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C1 | §4 | `nothingTrueRefutes : ¬ T N_T` | PROVEN | `{T, tschema}` |
| C2 | §4 | `notNothingTrue : ¬ N_T` | PROVEN | `{T, tschema}` |
| C3 | §4 | `someTrue : ∃ p, T p` | PROVEN | `CL + {T, tschema}` |
| C4 | §4 | `atomicTruthWitnessed : T True` | PROVEN | `{T, tschema}` |
| C5 | §5 | `nothingFalseRefutes : ¬ T N_F` | PROVEN | `{T, tschema}` |
| C6 | §5 | `notEverythingTrue : ¬ N_F` | PROVEN | `{T, tschema}` |
| C7 | §5 | `someFalse : ∃ q, IsFalse q` | PROVEN | `{T, tschema}` |
| C8 | T3 §6 | `greatResult : ∃ p q, T p ∧ IsFalse q` | PROVEN | `{T, tschema}` |
| C9 | T3 | `noBothTrueAndFalse` | PROVEN | `{}` (pure logic) |
| C10 | §22 | `excludedMiddle : ∀ p, T (p ∨ ¬ p)` | PROVEN | `CL + {T, tschema}` |
| C11 | §23 | `nonContradiction : ∀ p, T (¬ (p ∧ ¬ p))` | PROVEN | `{T, tschema}` |
| C12 | §10 | `bivalence : ∀ p, T p ∨ IsFalse p` | PROVEN | `CL + {T, tschema}` |

Founding axioms of Level 0: `T : Prop → Prop` (SEM, D2), `tschema`
(SEM, D2; consistency model: boolean `T := id`).

## Level 1 — semantics (`Logos.Semantics`, `Logos.Truthmaker`, `Logos.Modal`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C13 | §22 | `Semantics.lawExcludedMiddle` | PROVEN | `CL` |
| C14 | §23 | `Semantics.nonContradiction` | PROVEN | `{propext}` |
| C15 | §24a | `Truthmaker.groundPrinciple` | PROVEN | `{Entity, ExistsAt, Ground}` (unfolds def) |
| C16 | §22 | `Truthmaker.lawExcludedMiddle` | PROVEN↑ | `CL + {Entity, ExistsAt, Ground, AxOr, AxNot}` |
| C17 | §23 | `Truthmaker.nonContradiction` | PROVEN↑ | `{propext, Entity, ExistsAt, Ground, AxAnd, AxNot}` |
| C18 | T7 | `Modal.T7_necessaryReality` | PROVEN↑ | `{AxGlobalGround, actualWorld, Entity, ExistsAt, Ground}` |
| C19 | T7 | `Modal.T7_excludedMiddleInstance` | PROVEN↑ | as C18 |
| C20 | T7 | `Modal.noNecessaryTruthIfAllContingent` | PROVEN↑ | as C18 |

Declared (Level 1): `Entity`, `Ground` (world-rigid, D6), `ExistsAt`
(SEM, D4); `AxOr`, `AxAnd`, `AxNot` (SEM, D5); `actualWorld` (SEM, D6);
`AxGlobalGround` (SEM, D7 — the named quantifier swap).

## Level 2 — agency and person (`Logos.Agency`, `Person`, `Alternatives`, `Order`, `GroundPerson`)

| ID | Prose | Lean theorem | Status | Axiom footprint |
|----|-------|--------------|--------|-----------------|
| C21 | §1/T1 | `Agency.T1_subjectExists` | PROVEN↑ | `{A, Exists, Subject, act_implies_exists, cogito}` |
| C22 | T2 | `Agency.T2_contentExists` | PROVEN↑ | `{A, Content, Subject, act_implies_content, cogito}` |
| C23 | T4 | `Agency.T4_agentExists` | PROVEN↑ | `{A, Agent, Exists, Subject, act_implies_agent, act_implies_exists, cogito}` |
| C24 | T5 | `Person.T5_personExists` | PROVEN↑ | C23-footprint + `{Means, Rational, act_implies_means, act_implies_rational}` |
| C25 | §24b | `Person.inseparability_24b` | PROVEN↑ | `CL + {A, Subject, T, Means, act_implies_means}` |
| C26 | **T9 (new)** | `Alternatives.T9_incompatibleAlternatives` | PROVEN | `{T, tschema}` |
| C27 | §13 | `Alternatives.incompatible_with_negation` | PROVEN | `{T, tschema}` |
| C28 | T6 | `Order.T6_fallibility` | PROVEN↑ | `{Subject, T, Fallible, fallible_false}` |
| C29 | T6 | `Order.T6_truthTranscendsWill` | PROVEN↑ | as C28 |
| C30 | §8 | `Order.correctness_distinct` | PROVEN↑ | `CL + {A, Subject, cogito, T, tschema}` |
| C31 | §9 | `Order.consequence_preserves_truth` | PROVEN | `{T, tschema}` |
| C32 | T8 | `GroundPerson.T8_personalGround` | PROVEN↑ | `{A, Subject, Means, Entity, ExistsAt, GroundProp, Realizes, AxGroundBearing, AxPersonalGround}` |
| C33 | T8 | `GroundPerson.present_feature_is_grounded` | PROVEN↑ | `{T, GroundProp}` via `GroundPrincipleProp` |
| C34 | T8 | `GroundPerson.necessary_truth_has_necessary_grounder` | PROVEN↑ | as C18 |

Declared (Level 2): `Subject`, `A`, `Exists`, `Content`, `Agent`,
`act_implies_exists/content/agent`, `cogito` (TRANS, D3);
`Rational`, `Means`, `act_implies_means/rational` (T5 components);
`Fallible`, `fallible_false` (T6 premise, boolean consistency model);
`Realizes`, `GroundProp`, `GroundPrincipleProp` (SEM reflection of §24a);
`AxGroundBearing`, `AxPersonalGround` (META, D9 — the price of "personal").

## Deferred / blocked

| ID | Prose | Status | Missing |
|----|-------|--------|---------|
| F1 | §15 Freedom (`FreeWill ↔ ◇Choose ∧ ◇Choose¬`) | DEFERRED | modal choice semantics + derivation (T10) |
| F2 | §21 teleology (`Ought → Goal`) | DEFERRED | deontic layer (normativity → telos) |
| F3–F6 | §28 `Good → Love → EternalRelation → Trinity` | DEFERRED | no argument exists yet (poem sketch only) |
| Q7.2 | weaker `AxGlobalGround` | DEFERRED | research sub-question (DESIGN.md) |

## Summary counts

- PROVEN (no new axioms beyond core `T`/`tschema`/classical): C1–C17, C26–C27, C30–C31.
- PROVEN↑ (under flagged SEM/META/TRANS axioms): C18–C20, C21–C25, C28–C29, C32–C34.
- `sorryAx` count across all modules: **0**.
- Verification: `lake build` green (24 jobs, seconds, Lean core only).
