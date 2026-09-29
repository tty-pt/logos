# Investigation: Right and Wrong, Bivalence, and Retorsion

**Repository:** Γ (Logos)  
**Primary Formal Source:** `formal/Logos/Core.lean`, `formal/Logos/Order.lean`, `formal/Logos/DirectNormativeRetorsion.lean`  
**Kernel Status:** LOGICAL (`{CL}`) / ZERO SUBSTANTIVE AXIOMS  

---

## 1. The Performative Starting Datum

Γ does not begin from a presuppositionless vacuum or an ungrounded axiom. It begins from a performatively undeniable datum:
$$\exists (s : \text{Subject}) (p : \text{Prop}),\; \text{Act}(s, p).$$
To attempt to formulate, debate, or deny any philosophical thesis is already to perform an intentional act.

---

## 2. Refutation of Absolute Universal Nihilisms

Can an opponent deny all truth or all distinction between right and wrong?
Let the two universal nihilisms be:
$$N_T \equiv \forall (p : \text{Prop}),\; p \qquad (\text{"Everything is true"})$$
$$N_F \equiv \forall (p : \text{Prop}),\; \neg p \qquad (\text{"Nothing is true"})$$

In `formal/Logos/Core.lean:145`, the Lean 4 kernel strictly checks:
```lean
theorem rightWrongDistinction : ¬ N_T ∧ ¬ N_F
```
* **Proof:**
  - If $N_T$ holds, then every proposition is true, including $\text{False}$. Hence $\text{False}$ is true, contradiction.
  - If $N_F$ holds, then every proposition is false. In particular, the proposition $N_F$ itself is false ($\neg N_F$), contradiction.
  - Therefore, both universal nihilisms are logically impossible.

---

## 3. The Objective Existence of Strong Truth and Bivalence

From $\neg N_T \land \neg N_F$, classical logic derives propositional non-triviality:
$$\exists (p : \text{Prop}),\; p \land \exists (q : \text{Prop}),\; \neg q \quad (\texttt{Logos.Core.strongTruthExists}, \text{Core.lean:170}).$$
Furthermore, every act $A(s, p)$ is exhaustively partitioned between correctness and error:
$$\text{Act}(s, p) \iff \text{Correct}(s, p) \lor \text{Incorrect}(s, p) \quad (\texttt{Logos.Order.act_iff_correct_or_incorrect}, \text{Order.lean:75}).$$
Where:
- $\text{Correct}(s, p) \equiv \text{Act}(s, p) \land T(p)$
- $\text{Incorrect}(s, p) \equiv \text{Act}(s, p) \land \text{IsFalse}(p)$
- $\text{Incompatible}(\text{Correct}(s, p), \text{Incorrect}(s, p))$ (`Order.correctness_distinct`, `Order.lean:65`).

---

## 4. The Direct Diagonal Retorsion of Normative Correctness

In `formal/Logos/DirectNormativeRetorsion.lean:55`, we formalize the diagonal retorsion of normative Right:
```lean
def NormativeRightExists : Prop :=
  ∃ (s : Subject) (p : Prop), ClaimsCorrect s p ∧ Logos.Order.Correct s p

def NoRight : Prop :=
  ¬ NormativeRightExists

theorem claims_correct_no_right_self_refuting
    (s : Subject) (hClaim : ClaimsCorrect s NoRight) (hTrue : NoRight) : False
```
* **Mechanism:** If someone asserts that no normative judgment is ever correct (`ClaimsCorrect s NoRight`), and if that denial is true, then the denial satisfies the definition of correctness (`Correct s NoRight`), thereby instantiating `NormativeRightExists` and refuting itself.
* **Footprint:** `{Initiates, Means, State, Subject}` (0 substantive axioms).

---

## 4b. Disclosure: the meaningless-world countermodel was defective (2026-09-29)

Recorded here because this file is where a reader looks for the epistemic
foundations of Right/Wrong, and because the defect was in a **model**, not in a
theorem — a distinction this project is not supposed to blur.

**What was wrong.** `NegativeRetorsionSignature` carried `EO : Prop` as an
*uninterpreted* field, and the countermodel witnesses — including the C382
populated-complement model, `the_meaningless_world_remains_a_model` — discharged
`EverythingObjective` by setting `EO := True` in a world whose `Means` was
`fun _ _ => False`. Those worlds therefore asserted the absolute objective order
while denying all meaning. On the author's own principle — *right and wrong can't
exist in meaninglessness* — that is not a countermodel but a contradiction of the
thesis, so the rows read as though they preserved the very order they were
supposed to refute.

**Extent.** 20 witness constructions across two files, not the 10 the plan
estimated. The defect was never confined to C382/C385: every meaning-free world
in the audit file, including M0, M1, M6, the mechanical-trace model and
`level0_model_M1_inanimate_universe_satisfies_noi`, asserted `EverythingObjective`
by the same mechanism. A reader who had trusted the plan's list would have taken
M1 to be a sound countermodel. It was not.

**The fix, and why it is not a documentation patch.**
`NegativeRetorsionSignature` now carries `Free : Subject → Prop` and
`objectivity_grounded : EO → ∃ s, Free s ∧ ∃ p, Means s p`. Reproducing
the pre-fix witness verbatim is now a **compile error** — the `False` is
`Means () True` under `Means := fun _ _ => False`. Two `{}` theorems make the
repaired claim machine-checked rather than asserted:
`objectivity_cannot_obtain_in_a_meaningless_world` and
`objectivity_grounded_yields_a_free_meaning_being`
(`formal/Logos/NegativeRetorsionAudit.lean`).

The parallel repair on the propositional side is C556
(`epistemic_order_requires_a_free_meaning_being`, `{}`), via the
`order_needs_a_meaning_being` signature field in
`formal/Logos/EpistemicPersonalGround.lean`. C528 itself was *not* weakened: its
`Grounds := False` witness is retained, and a **separate** being is supplied, so
the honest content of C528 is the weaker and more interesting claim — the being
the order requires is not the same as a being that grounds.

**What did not change.** No new axiom. The register is 35 (17 VOCAB / 18
substantive) before and after, checked mechanically by
`scripts/gapmap_taxonomy.py --check`. Rows whose *status* is a separation rather
than a PROVEN step (C175, C382, C385) are still `{}` with `COUNTERMODEL` status and
are still excluded from the PROVEN buckets — C382 and C385 keep their `{}` footprint,
but now on a witness that is coherent.

**Standing lesson** (now in `AGENTS.md`): a free-signature countermodel must pass a
**meaning-coherence audit** before it is reported. A model that grants an order
while denying every act of signification is not a countermodel; it is a
self-refuting artifact of the signature. The general rule, for every future
countermodel, is: *check that the model instantiates the vocabulary it is
supposed to deny.*

---

## 5. Summary of Epistemic Status

The foundation of Right and Wrong rests entirely on **pure classical logic** and the **performative impossibility of self-denial**. No metaphysical speculation or stipulative definition is smuggled into the starting point.
