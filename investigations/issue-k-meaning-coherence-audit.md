# Issue K — Step 1: the meaning-coherence audit of the two countermodels

**Date:** 2026-10-02. **Scope:** `ISSUE_K_PLAN.md` Part 3, Step 1 only. Nothing in
the kernel was changed by this step; the repairs it prescribes are Step 2.

**Rule under which the audit is run** (`AGENTS.md`, 2026-09-29, and
`investigations/right-and-wrong.md` §4b):

> Signature models are not candidate states. A free-signature countermodel
> witnesses that a constraint is underivable from a signature; it is never
> evidence about a state of affairs. … *Check that the model instantiates the
> vocabulary it is supposed to deny.* A model that grants an order while denying
> every act of signification is not a countermodel; it is a self-refuting
> artifact of an uninterpreted signature field.

**Evidence.** Every kernel claim below is in
`investigations/issue-k/step1_audit_probe.lean`, an audit artifact outside the
`Logos` lean_lib, run with:

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal && lake env lean ../investigations/issue-k/step1_audit_probe.lean
```

`[]` in a `#print axioms` line means no axiom at all — not `CL`, not `propext`,
not `Classical.em`. A `sorryAx` anywhere would be an audit failure.

---

## Theorem 1 — `AsieticChoice.singleContentModelRefutesBareRejectedHorn` (C273), with `bareRejectedHornCoMeant_is_not_derivable` (C274)

### The vocabulary the surrounding prose claims the model denies

The module is `AsieticChoice.lean`, and the relation under audit is Γ's primitive
meaning-act relation `Means : Subject → Prop → Prop` (`Agency.lean:92`,
`Tag: VOCAB`), "subject *s* means (intentionally relates to) proposition *p*".

### The witness

```lean
def singleContentModel : SingleContentSignature where
  Subject := Bool
  content := fun _ => True
  means := fun _ p => p
  witness := false
  witnessContent := True
  faithful := fun _ _ h => h
```

### Finding 1a — the `Faithful` field is a truth restriction Γ does not impose, and it is load-bearing in the witness: **defect**

`faithful : ∀ (s : Subject) (p : Prop), means s p → p` (`:352`) makes the model's
meaning-relation **truth-only**: no subject can ever relate to a falsehood.

Γ's `Means` is not truth-only, and says so in its own definitions:

| Γ's fact | where |
|---|---|
| `Incorrect s p := A s p ∧ IsFalse p` | `Order.lean:49` |
| `IsFalse p := ¬ T p` | `Core.lean:52` |
| `A s p := Means s p ∧ ∃ w w', Initiates s w w' p` | `Agency.lean:22` |
| ⇒ `Incorrect s p → Means s p ∧ ¬ p` | by the three above |
| `ClaimsNormativeCorrectness s p` requires `Means s (Incorrect s p)` | `NormativeOrder.lean:168` |
| `EntityMeans Entity.ofGround False` | `CanonicalAseity.lean:99` |

Γ therefore has, by construction and in several places, a subject relating to a
**false** content: being *wrong* is a meaning-act. The corpus states the rule the
witness breaks in `Order.rightWrong_implies_meaning`'s own docstring:

> "no model can assert `Correct`/`Incorrect` while denying meaning, because `A s p`
> has `Means s p` as its constitutive content"

A relation under which nothing is ever wrong is not an instantiation of Γ's
`Means`; it is a stricter stand-in for it. This is the same defect class as the
retracted `NegativeRetorsionSignature` worlds (`right-and-wrong.md` §4b) in its
truth-restricted form rather than its emptiness-restricted form.

### Finding 1b — the structure is not a "single-content" structure at all: **defect**

`SingleContentSignature` carries `content : Subject → Prop` (`:348`) and
`faithful` (`:352`), and **no field relating the two**. `content` is never read
anywhere in the module (`grep -n '\.content' formal/Logos/AsieticChoice.lean`
returns nothing). So nothing in this structure says a subject has one content; the
name is a gloss on an inert field. The honest name is "truth-only-`Means`
model".

### Finding 1c — the stated justification for `Faithful` is a false mathematical claim: **defect, `{}`-refuted**

`AsieticChoice.lean:341-344` and `:357-359`:

> "Faithfulness is the load-bearing field. Single-valuedness alone would not do:
> from `p = ¬ p` no contradiction follows in general, because `p` need not be
> provable."

It does follow, and with no axioms:

```lean
theorem probe_eq_negp_is_false (p : Prop) (h : p = ¬ p) : False := by
  have h2 : p → (p → False) := Eq.mp h
  have h1 : (p → False) → p := Eq.mp h.symm
  have f : p → False := fun hp => h2 hp hp
  exact f (h1 f)
-- #print axioms → []
```

Consequence: **genuine** single-valuedness — the constraint the structure's name
promises — refutes the horn at `{}` with no truth restriction at all:

```lean
single : ∀ (s : Subject) (p : Prop), means s p → p = content s
-- probe_singleValuedness_refutes_bareHorn → []
```

and a witness built from it *does* instantiate meaning including falsehood
(`content := fun _ => False`, `means := fun _ p => p = False`,
`probe_singleValuedModel_witnesses_antecedent → []`). So `Faithful` was never
load-bearing; the countermodel was mis-designed, not over-designed.

### Finding 1d — the ledgered conclusion is **false**: Γ derives the bare horn

C273/C274's docstrings and GAPMAP record the block as machine-backed:
`AsieticChoice.lean:406-408` — "The block remains: **Γ does not derive the bare
form**" — and `GAPMAP.md:3418-3419`, row F11 at `:3432`, whose stated ground is
"(2) The single upstream gap is the `Initiates`-existence gap, `∃ s p, Act s p` …
**no axiom of Γ supplies an `Initiates` witness**".

That ground is false. `performative_act_datum : ∃ s p, Act s p` (`Agency.lean:233`,
C454, `Tag: TRANS`) **is** an `Initiates` witness, because `Act s p` unfolds to
`Means s p ∧ ∃ w w', Initiates s w w' p`. With `AxActPolarity : Act s p → Means s
(¬ p)` (`Choice.lean:796`, SEM) the horn follows in two lines:

```lean
theorem probe_bareRejectedHornCoMeant_is_derived :
    Logos.AsieticChoice.bareRejectedHornCoMeant :=
  fun _ => by
    obtain ⟨s, p, hAct⟩ := performative_act_datum
    exact ⟨s, p, act_implies_means hAct, AxActPolarity s p hAct⟩
-- #print axioms →
--   [Initiates, Means, State, Subject, performative_act_datum, AxActPolarity]
```

The same price reaches strictly more:

| conclusion | footprint | probe |
|---|---|---|
| `∃ s p, TrueChoice s p (¬ p)` | `{Initiates, Means, State, Subject, performative_act_datum, AxActPolarity}` | `probe_bareHorn_yields_trueChoice` |
| `∃ s, FreeWill s` | same | `probe_freeWill_from_act_datum_and_polarity` |
| `∃ e, Asiety e` | same | `probe_asiety_from_act_datum_and_polarity` |

For comparison, the *currently ledgered* route to the last two is
`AsieticChoice.freeWill_exists` (C278) and `an_asietic_entity_exists`, both at
`{AxTwoSubjects, Means, Subject, Will, subjectWill}` — and `AxTwoSubjects` is
`Tag: META`. The probes' price is one `TRANS` datum plus one `SEM` constitutive
principle, with **no META bridge on the route**. The corpus already exploits the
same price at C455 (`some_subject_initiates`) and C476/C477
(`genuineChoice_exists_of_act_datum_polarity`, `freeWill_exists_of_act_datum_polarity`,
`ActCascade.lean:263`, `:299`) — which is why F11's premise is stale rather than
merely wrong, and why GAPMAP contradicts itself on the point.

### What survives, stated at the strength it actually has

The countermodel is **formally valid as a model of the bare signature**
`<Subject, Means>`: the bare horn is not a *consequence of that signature alone*.
That is a real and worth-keeping negative result. What must be withdrawn is
everything the ledger built on top of it:

1. "in a **faithful** single-content model" — there is no single-content model
   here, and no faithfulness in Γ's `Means` (Findings 1a, 1b).
2. "Single-valuedness alone would not do" — `{}`-refuted (Finding 1c).
3. "the block is machine-backed / refuted, not merely open / Γ does not derive
   the bare form" — false; Γ derives it at
   `{performative_act_datum, AxActPolarity}` (Finding 1d).

---

## Theorem 2 — `AsietyFreedom.rightWrongFactYieldsNoChooser` (C294), the refutation recorded against F13

### The vocabulary the surrounding prose claims the model denies

Same `Means`. The prose reads the theorem as denying "right/wrong entail a
chooser" (`AsietyFreedom.lean:44-48`, `:439-443`; GAPMAP `:3479`, F13 at `:3491`).

### The witness

```lean
⟨rightWrongDistinction, Unit, fun _ _ => False, fun h => by
  obtain ⟨s, p, q, hM⟩ := h
  exact hM.1⟩
```

### Finding 2a — the statement *forces* every witness to be meaning-free: **defect, `{}`-refuted**

The second conjunct is `¬ (∃ s : S, ∃ p q : Prop, M s p ∧ M s q)`. `p` and `q` are
**not required to be distinct**, so this is *equivalent* to `¬ (∃ s p, M s p)`:

```lean
theorem probe_pairq_forces_meaninglessness
    (M : Unit → Prop → Prop)
    (h : ¬ (∃ s : Unit, ∃ p q : Prop, M s p ∧ M s q)) :
    ¬ (∃ s : Unit, ∃ p : Prop, M s p) := by
  rintro ⟨s, p, hMp⟩
  exact h ⟨s, p, p, hMp, hMp⟩
-- #print axioms → []
```

So the degenerate shape is not the choice of the witness `M := fun _ _ => False`;
it is entailed by the statement. **Every** model satisfying C294's second
conjunct is a world in which no act of signification occurs at all. That is
precisely the object of the objection in `ISSUE_K_PLAN.md` §1.7 ("a
meaning-vocabulary in which the meaning-relation is just the constant-false
predicate") — and, per §1.9, the object of the sentence the author holds to be
stupid.

And in that world right and wrong obtain: `¬ N_T ∧ ¬ N_F` is `{}` pure logic
about contents, so it holds in *every* model of *every* signature. The joint
statement therefore exhibits, by construction, **right and wrong obtaining in a
world where meaning means nothing** — the exact shape the binding rule retracted
on 2026-09-29.

### Finding 2b — the repair is the `NegativeRetorsionSignature` shape and is `{}`: **repaired statement available**

Requiring distinct contents *and* forcing meaning to exist is the C294 analogue of
`NegativeRetorsionSignature`'s added `objectivity_grounded` field, and the
negative result survives at `{}`:

```lean
theorem probe_repaired_rightWrong_no_pairwise_chooser :
    (¬ N_T ∧ ¬ N_F) ∧ ∃ (S : Type) (M : S → Prop → Prop),
      (∃ s : S, ∃ p : Prop, M s p) ∧
      ¬ (∃ s : S, ∃ p q : Prop, p ≠ q ∧ M s p ∧ M s q)
-- #print axioms → []
```

witness `S := Unit`, `M := fun _ p => p = True`. That model **means something**
and denies only that any subject ever relates to two *distinct* contents. That is
the honest negative claim, and it is a real limitation of the right/wrong fact —
which, as GAPMAP's own C294 row already says, "quantifies over no `Subject`".

### What survives, and what F13 now rests on

The *observation* that `rightWrongDistinction` is content-level and yields nothing
by itself is true and worth keeping. The countermodel as stated does not support
it, and cannot be repaired into supporting it without changing the claim (2b).

F13 (`groundFreedomSharedWithSomeone := ∃ s, AsietyFreeWill s`) stays `BLOCKED`,
but for a different and better-stated reason: its first conjunct
`AsietyFreedomOfGround` is the declared ◈ **META** stipulation
(`AsietyFreedom.lean:119`, registered in `Stipulations.lean`) and is not derivable.
Its second conjunct is no longer a gap at all: `Asiety (EntityOf s)` is available
at `{performative_act_datum, AxActPolarity}` (probe D above), strictly cheaper in
kind than the `{AxTwoSubjects}` (META) route the module currently discloses.

---

## Ledger defects found incidentally, to be corrected in Step 6

| where | defect |
|---|---|
| `GAPMAP.md:3418-3419` (C273), `:3432` (F11) | claim Γ does not derive `bareRejectedHornCoMeant`; it does, at `{performative_act_datum, AxActPolarity}` |
| `AsieticChoice.lean:336-345`, `:356-362`, `:398-415`, `:304`, `:319`, `:404-408` | the `Faithful`/`p = ¬ p` justification and the "block remains" claim |
| `GAPMAP.md:3479` (C294), `:3491` (F13) | the refutation rests on a meaning-free witness that the statement forces |
| `AsietyFreedom.lean:44-48`, `:250-270`, `:435-448` | "compatible with a meaning-vocabulary in which no subject means anything", used as a refutation |
| `Choice.lean:41-49` | records the bare horn as "BLOCKED *and refuted*" |
| `GAPMAP.md:1603` vs `:2939` | F1bUncond is `SUPERSEDED` (C278) in one row and "continua BLOCKED" in C557's row |
| `base.txt` §31 "still requires proof" | cites C294/F13 as the reason the sharing obligation is open |

## Step 1 verdict

Both countermodels **fail** the meaning-coherence audit, for different reasons and
not symmetrically:

- **C273/C274** is a *mis-designed* model (truth-only `Means`, inert `content`
  field, false justification) attached to a *false* conclusion — Γ derives the
  horn. It must be repaired and its `BLOCKED`/`refuted` reading withdrawn.
- **C294** is a *correct* observation wearing an *incoherent* witness: the
  statement itself forces meaning-freeness, so it cannot be repaired without
  changing the claim. The repaired form at 2b is the honest version and is `{}`.

No axiom register moved: nothing here adds, removes or demotes a declared axiom.
Step 2 is unblocked and its work is now precisely specified by Findings 1a–1d and
2b.
---

## Finding 2c — the repair LANDED (2026-10-03)

Finding 2b identified the fix but did not apply it. It is now applied in the kernel.

`AsietyFreedom.rightWrongFactYieldsNoChooser` was changed to

```lean
(¬ N_T ∧ ¬ N_F) ∧
  ∃ (S : Type) (M : S → Prop → Prop),
    (∃ s : S, ∃ p : Prop, M s p) ∧                        -- signification instantiated
    (∃ p q : Prop, Incompatible p q ∧ p ≠ q) ∧            -- order granted
    (¬ ∃ s : S, ∃ p q : Prop, p ≠ q ∧ M s p ∧ M s q)      -- but no subject means two
```

witnessed by `S := Unit`, `M := fun _ p => p = True`. Both checks the binding rule asks for now
pass on this row: the model **instantiates** the meaning relation (a subject means `True`), and it
**grants an order** while denying pairwise signification — it is *amoral*, not *voiceless*. That
distinction is the whole point: the old row denied every act of signification and was therefore a
self-refuting artifact; the new row has a world in which a subject signifies and still no chooser
exists, which is the claim the surrounding prose actually needed.

Footprint is **still `{}`**, and this time it is the price of a real statement rather than the price
of a `True` proposition — the distinction GAPMAP C568–C572 (the `Consubstantial` deletion) forced on
`Consubstantial`. `asietyFreedom_summary` (C296) is unchanged because it consumes only the first
conjunct.

Two supporting results, both `{}`:

- `AsietyFreedom.pairwise_denied_forces_meaninglessness` — the *old* form's second conjunct implies
  `¬ ∃ s p, M s p`. This is Finding 2a restated as a kernel lemma, so the claim that the repair was
  *necessary* is machine-checked rather than argued.
- `probe_repaired_rightWrong_no_pairwise_chooser` (section H of
  `investigations/issue-k/step1_audit_probe.lean`) — verified before promotion; it matches the
  landed form.

**One thing this does not fix.** The claim's status in the ledger stays `COUNTERMODEL`, and it should:
the existence limit is real. What changed is that the limit is now witnessed by a coherent world
instead of a degenerate one. `groundFreedomSharedWithSomeone` (F13) remains `BLOCKED`, because
refuted is not the same as discharged.
