> **⚠️ SUPERSEDED IN PART — read `RULE_R_CORRECTION_PLAN.md` §12.9 first.**
> This log is the record of what was *tried*. Its §3.15 and §9 prescribe a fix
> ("hoist the `maxBVarAt` guard above `withLocalDeclsDND`") that was already
> present and could not have worked, and its §4 pins the two guards that were
> subsequently **deleted**. The cause was `Meta.withLocalDeclsDND` being the
> no-dependency variant, and `abstractRange n #[]` throwing on any domain with a
> loose bvar; the fix was `Meta.forallTelescope`, which removes the whole class.
> **Step 1 is now complete** — `formal/goal_audit.json` exists with 6 397 records.
> §3.1–§3.14 of this log remain accurate and worth keeping.

# Investigation log — `scripts/audit_goals.py` (the `formal/goal_audit.json` generator)

**This file is the durable record of the longest debugging session in this repo.**
It exists because the failure modes below are *not* recoverable from the diff: most
of them produce no traceback that points at the cause, two of them are uncatchable
Lean panics, and the correct API was the opposite of what I assumed three times.

Companion to `RULE_R_CORRECTION_PLAN.md` §12.9. That section is the short
version; **this is the long version, with the errors verbatim.**

---

## 0. TL;DR for the next agent

* `scripts/audit_goals.py` is written, compiles, and is **correct on every
  hand-checked declaration** — but a full run aborts, so
  `formal/goal_audit.json` **does not exist yet**.
* Abort cause: 5 **structure-generated** declarations (`mk.noConfusion`, `recOn`,
  `casesOn`, `mk.injEq`) whose types `Meta.withLocalDeclsDND` rejects.
* Fix: hoist the `maxBVarAt` guard above the `withLocalDeclsDND` call, and delete
  the per-declaration `try/catch` (it converts one bad declaration into a
  100-error `maxErrors` abort).
* Then run it **detached with `setsid`**; it takes ~10 minutes because `run_cmd`
  is interpreted.
* Nothing else in the repo has been touched. `scripts/build_deduction.py` is
  pristine.

---

## 1. Environment facts (verified, do not re-derive)

| fact | value | how it was found |
|---|---|---|
| toolchain used by `lake env lean` in `formal/` | **Lean 4.34.0** (`formal/lean-toolchain` = `leanprover/lean4:v4.34.0`) | `cat formal/lean-toolchain` |
| toolchain reported by bare `lean --version` on `$PATH` | **4.34.1** | `$PATH` resolves a *different* elan toolchain than `formal/` pins |
| `lake`/`lean` not on `PATH` by default | — | `export PATH="$HOME/.elan/bin:$PATH"` first (`AGENTS.md`) |
| declarations in `formal/depgraph.json` with kind `thm`/`def`/`axiom` | **5 951** | `scripts/audit_footprints.py` audits the same set |
| entries in `formal/axiom_audit.json` | **5 951** | matches |
| axioms registered by the builder | **35** | `scripts/build_deduction.py` |
| `run_cmd` execution model | **interpreted, not compiled** → ~10 min for 5 951 decls | benchmark, §6 |
| `PrettyPrinter` module | needs `import Lean.PrettyPrinter` **separately** from `import Lean` | §4, item 5 |

Consequence of the toolchain split: backtraces quoted in this document say
`leanprover--lean4---v4.34.0`, but a bare `lean` gives 4.34.1. They are the same
code base with different build numbers; do not treat them as different installs.

---

## 2. The architecture that was chosen, and why

The goal is a per-declaration **claim shape** machine-read from the kernel, so the
badge selector can tell "two routes to the same claim" from "two unrelated
theorems". `AGENTS.md` mandates exactly this pattern for footprints
(`#print axioms` in a temp module → `formal/axiom_audit.json`), so the goal audit
is deliberately the *same* pattern with a different kernel question:

```
formal/goal_audit.json : { "<decl full name>" : {kind, goal, goalTag, quant,
                                            headSyms, headShorts, valueHeads,
                                            boundSorts, binderFree, hypothesis} }
```

Produced by: `scripts/audit_goals.py` writes `formal/.audit_goals.lean`, runs
`lake env lean formal/.audit_goals.lean` from `formal/`, parses the `GA`-prefixed
lines, deletes the temp file, writes the JSON. **Stdlib only, no new Lean
dependency.**

### 2.1 Two conventions that are load-bearing

* **Pi is context, Sigma is claim.** Every leading `forallE`/`lam`/`letE` is
  stripped; the residual expression is the *goal*. A top-level `Exists`
  application stays in the goal and sets `quant: "E"`. A residual `∀` sets `"A"`.
  So `∀ p, P p` is shaped as "the claim `P p`, with `p` in context", and
  "there exists an `s` with `TrueChoice s`" is visibly different from
  "for all `s`, `Asiety (EntityOf s)`". This is exactly the distinction the Asiety
  row needs (identification ≠ existence).
* **Symbols, not strings, wherever a comparison happens.** `headSyms`,
  `boundSorts`, `hypothesis[].type` and `valueHeads` are all *fully qualified
  head symbols* obtained by a structural `match` on `.getAppFn`. Strings are
  produced only for display. Gate G1 needs to distinguish Γ's
  `Logos.Agency.Subject` from a model's
  `Logos.HostileSemantics.…ModelSubject`, and only the symbol can do that
  reliably. Corollary: a declaration is never pretty-printed to decide its shape.

### 2.2 Why a `def` needs its *body* audited too

`Logos.AsieticChoice.Asiety` is `def Asiety (e : Entity) : Prop`. Its signature
goal is literally `Prop`, so:

* `#print axioms Asiety` → `{Means, Subject}` — vocabulary only, no evidence;
* its signature shape → head symbol `Prop`, no evidence;
* its **body** → `TrueChoice e`, head symbol `Logos.AsieticChoice.TrueChoice` —
  the actual identification `Asiety ↔ TrueChoice`.

Hence `defValueHeads` reads `ci.value`. Treat `goal`/`headSyms` as *the claim a
route asserts* and `valueHeads` as *what the definition says*; G4 (◈ marker) still
forbids a `def` from ever rendering `✅`.

---

## 3. The error catalogue — every failure, in the order it happened

This is the part that cannot be recovered from the diff.

### 3.1 `import Logos` is not enough

```
error(lean.unknownIdentifier): Unknown identifier `MetaM`
error(lean.unknownIdentifier): Unknown identifier `CoreM`
Note: The identifier `MetaM` is unknown, and Lean's `autoImplicit` option …
```

`open Lean Meta Elab Command` does not bring these in. **Fix:** `import Lean`
above `import Logos`.

### 3.2 `withReader` is not a MetaM-lifter

```
error: Invalid argument name `reader` for function `withReader`
Hint: Perhaps you meant one of the following parameter names: ρ m self α β f x
```

`withReader (f : ρ → β) (k : ReaderT ρ m α) : m α` — it *transforms the reader*,
it does not supply one. **Fix:** drop it entirely; run the whole audit in `MetaM`
and enter from `run_cmd` with `MetaM.run'` (see §3.4).

### 3.3 `ReaderT.run` does not unify with `MetaM`

```
error: Application type mismatch. The argument
  conjunctHeads goal
has type MetaM (List String)
but is expected to have type ReaderT Meta.Context CoreM (…)
```

`MetaM = ReaderT Meta.Context (StateRefT Meta.State CoreM)`; `ReaderT.run`
demands the underlying monad be literally `CoreM`. **Fix:**

```lean
def MetaM.run (x : MetaM α) (ctx := {}) (s := {}) : CoreM (α × State)
def MetaM.run' (x : MetaM α) (ctx := {}) (s := {}) : CoreM α
```

So: write `run : MetaM Unit` and `run_cmd do liftCoreM (MetaM.run' run)`.
`liftCoreM` is needed because `run_cmd` expects `CommandElabM`, not `CoreM`:

```
error: Type mismatch
  run.run'  has type  CoreM Unit
  but is expected to have type  CommandElabM ?m.2
```

### 3.4 `Expr.instantiate1` is not the substitution I assumed — **the costliest error**

I wrote a recursive substitution that shifted the expression out from under
itself:

```lean
-- WRONG
def instBVars (e : Expr) (i : Nat) (fvars : Array Expr) : Expr :=
  if h : i < fvars.size then e.instantiate1 fvars[i]! (instBVars e (i + 1) fvars) else e
```

```lean
error: Function expected at
  e.instantiate1 fvars[i]!
but this term has type
  Expr
```

`instantiate1` is `opaque instantiate1 (e : @& Expr) (subst : @& Expr) : Expr` —
two arguments, and it **replaces level 0 *and decrements every other level***. The
observed trace of the bug, which is the tell:

```
names = [s, p, q, h]
raw goal = Logos.AsieticChoice.Asiety (Logos.Entity.EntityOf #3)
after 1: Asiety (EntityOf #2)
after 2: Asiety (EntityOf #1)
after 3: Asiety (EntityOf #0)
instBVars: Asiety (EntityOf s)     ← right answer, 6 wasted levels, and note the
                                      printed binder was `h`, not `s`
```

It "accidentally" terminated because the goal ran out of bvars. **Fix:**
`Expr.instantiateRev` substitutes level *i* with `subst[i]` simultaneously:

```lean
def instBVars (e : Expr) (fvars : Array Expr) : Expr := e.instantiateRev fvars
```

```
instBVars: Logos.AsieticChoice.Asiety (Logos.Entity.EntityOf s)
pp instBVars: Logos.AsieticChoice.Asiety (Logos.Entity.EntityOf s)
```

### 3.5 `try/catch` in a pure `def` needs `Id.run` or a `match`

```lean
-- WRONG
def instBVars (e : Expr) (fvars : Array Expr) : Expr :=
  try e.instantiateRev fvars catch _ => e
```
```
error: invalid `do` notation, expected type is not a monad application
  Expr
```
**Fix:** `match (try some (…) catch _ => none) with | some r => r | none => e`.

### 3.6 `Format.pretty` — field notation does not elaborate

```
error(lean.invalidField): Invalid field notation: Type of `fmt` is not known;
cannot resolve field `pretty`
Hint: Consider replacing the field projection with a call to one of the
following: Json.pretty • Format.pretty • PrettyPrinter.OneLine.pretty …
```

`def pretty (f : Format) (width : Nat := defWidth) (indent : Nat := 0)
(column := 0) : String` lives in `namespace Std / namespace Format` in
`Init/Data/Format/Basic.lean:415`. **Fix:** `Std.Format.pretty fmt 240`.

### 3.7 `ppExprLegacy` needs its own import

```
error(lean.unknownIdentifier): Unknown identifier `ppExprLegacy`
```

It is in `namespace Lean.PrettyPrinter`, and `import Lean` does not pull that
module in. **Fix (two parts):** `import Lean.PrettyPrinter`, *and* qualify the
call `PrettyPrinter.ppExpr e` — because `open Lean Meta Elab Command` does not
open `Lean.PrettyPrinter`. (`ppExprLegacy` turns out not to be needed: once the
audit runs in `MetaM`, `PrettyPrinter.ppExpr` is available directly.)

### 3.8 `ConstantInfo` has no `type?`

```
error(lean.invalidField): Invalid field `type?`: … 'Lean.ConstantInfo.type?'
error(lean.invalidField): Invalid field `type!`
error(lean.invalidField): Invalid field `toArray` on List
```

**Fix:**
```lean
def declType : ConstantInfo → Expr
  | .thmInfo i => i.type
  | .axiomInfo i => i.type
  | .defnInfo i => i.type
  | .opaqueInfo i => i.type
  | _ => .sort 0
```
and for arrays, `names.toList.zip sorts.toList |>.toArray` — there is no
`Array.toArray` and no `List.toList`.

### 3.9 `FVarId.mk` takes a `Name`, not a `String`

```
error: Application type mismatch. The argument
  toString "g" ++ toString tag ++ toString "_" ++ toString n
has type String but is expected to have type Name
  in the application { name := ... }
```
**Fix:** `FVarId.mk (Name.mkSimple s!"g{tag}_{n}")`. (This whole `mkLCtx`
approach was then abandoned in favour of `withLocalDeclsDND` + `instantiateRev`.)

### 3.10 `MetaM.run' × MetaM`-typed accumulators

```
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  HAdd MessageData Nat MessageData
```

`let mut seen := 0` then `seen := seen + 1` in a `MetaM do`-block got `seen`
inferred as `MessageData`, because the surrounding `logInfo m!"… {seen}"` was
elaborated first under the error-recovery rules. **Fix:** annotate —
`let mut seen : Nat := 0`.

### 3.11 `mutable variable cannot be shadowed`

```
error: mutable variable `names` cannot be shadowed
```
**Fix:** accumulate into `acc`, then `let names := acc.qsort …`.

### 3.12 Termination on `Expr` recursion

```
error: fail to show termination for LogosGoalAudit.tagOf
failed to infer structural recursion: Cannot use parameter e …
  ⊢ sizeOf b < sizeOf e✝
```
`match … | .mdata _ b => tagOf b` — the subterm is under a constructor Lean will
not see through. **Fix:** `partial def` (needs `Inhabited`, satisfied by `String`
/ `List String`).

### 3.13 `letE` was dropped → bvar levels desynchronised

```
error: unexpected bound variable #2
```

`splitBinders`' `letE` branch originally ignored the let binder, so every
`bvar` below it was off by one. **Fix:** treat `letE` as a binder —
`splitBinders b hyps (headSym t :: sorts) ((n, t) :: binders)`.

### 3.14 `try/catch` cannot catch a Lean panic — **the central discovery**

This is the one that cost the most time and that a `try/catch` will never reveal.
`lake env lean` reports:

```
PANIC at Lean.Meta.whnfEasyCases Lean.Meta.WHNF:391:22: loose bvar in expression
backtrace:
  Lean.Meta.whnfImp / whnfCore / whnf
  Lean.Meta.forallTelescopeReducingAux
  Lean.Meta.isClassExpensive?
  Lean.Meta.isClass?
  Lean.Meta.withNewFVar
  Lean.Meta.withLocalDeclImp
  Lean.Meta.withLocalDecl
  Lean.PrettyPrinter.Delaborator.SubExpr.withBindingBody'   ← the visible top frame
  ...
```

Two separate consumers of `whnf` blow up on an expression with an out-of-range
loose bound-variable level:

1. **`Meta.isProp`** (called once per binder by `splitBinders`).
   **Fix:** abstract the levels away first —
   ```lean
   def isPropClosed (d : Expr) : MetaM Bool :=
     isProp (d.abstractRange (maxBVarAt d 0 + 1) #[])
   ```
   The `+ 1` matters. A hardcoded `abstractRange 32 #[]` leaves level 32 loose on
   any declaration with more than 32 binders and re-arms the panic.
   (`Expr.abstractRange (e : Expr) (n : Nat) (xs : Array Expr) : Expr` — note the
   `Array Expr` third argument; `abstractRange 0 32` does not typecheck.)

2. **The delaborator**, via `PrettyPrinter.ppExpr`. The top frame
   (`withBindingBody'`) points at *pretty-printing*, which is why this was twice
   misdiagnosed as a bug in my `sortKey` helper. **Fix:** measure the levels
   structurally and refuse to print:
   ```lean
   partial def maxBVarAt (e : Expr) (d : Nat) : Nat :=
     match e.consumeMData with
     | .bvar i              => max d (d + i + 1)
     | .app f a             => max (maxBVarAt f d) (maxBVarAt a d)
     | .lam _ _ b _         => maxBVarAt b (d + 1)
     | .forallE _ _ b _     => maxBVarAt b (d + 1)
     | .letE _ _ _ b _      => maxBVarAt b (d + 1)
     | .mdata _ b           => maxBVarAt b d
     | .proj _ _ b          => maxBVarAt b d
     | _                    => d
   ```

   This is a **structural** walk with an upper bound, deliberately over-estimating
   (`max d (d + i + 1)` rather than `d + i`), so it can never under-report.

**The lesson:** a Lean `PANIC` is not a `Lean.Exception`. It is not catchable, it
does not appear in the record as a `GA ERROR`, and it aborts the entire run. Any
future `whnf`-touching kernel API called from this audit needs the `maxBVarAt`
guard in front of it.

### 3.15 The remaining failure: structure-generated declarations

A full run reaches `Logos.ActionChoiceDefinitions` and stops with 5 errors and
then `maximum number of errors (100; from option maxErrors) reached, exiting`:

```
GA ERROR Logos.ActionChoiceDefinitions.DeliberativeContext.mk.noConfusion
GA ERROR Logos.ActionChoiceDefinitions.DeliberativeContext.recOn
GA ERROR Logos.ActionChoiceDefinitions.DeliberatorWithoutLeeway.casesOn
GA ERROR Logos.ActionChoiceDefinitions.DeliberatorWithoutLeeway.mk.noConfusion
GA ERROR Logos.ActionChoiceDefinitions.DeliberatorWithoutLeeway.recOn
```

These are `structure`-generated. Their types contain binder levels that
`splitBinders` never strips, and the *call* that rejects them is
`Meta.withLocalDeclsDND binders`, not `instantiateRev`.

**The fix (two lines, both already partially applied):**

1. The `maxBVarAt` guard is currently *inside* `ppBinders` but the early `return`
   happens before `withLocalDeclsDND` is entered — verify that it really is
   before the call and that the guard uses the **largest** level across goal,
   each hypothesis type and each binder type, not the goal alone. If
   `withLocalDeclsDND` still throws, wrap the whole `ppBinders` body in
   `try/catch` returning `""` — that part *is* a catchable exception, unlike §3.14.
2. Delete the per-declaration `try … catch _ => logError …` in `run`. It is what
   converts one bad declaration into a 100-error `maxErrors` abort, and after fix
   (1) it should never fire. Keep the `GA failed` counter, and keep the Python
   guard that turns any surviving `GA ERROR` into a hard failure — a
   structure-generated declaration legitimately gets `goal: ""` and that must be
   *recorded*, not *swallowed*.

Structure-generated declarations are also nearly irrelevant to badge selection:
they are `mk.injEq`-style facts about records, never routes to a Γ claim. If a
cleaner fix is available later, prefer *skipping their goal string* over
engineering them to print.

---

## 4. Three things to keep exactly as they are

1. **Imports.** `import Lean` **and** `import Lean.PrettyPrinter` **and**
   `import Logos`, and call `PrettyPrinter.ppExpr` qualified.
2. **Entry point.** `def run : MetaM Unit` + `run_cmd do liftCoreM (MetaM.run' run)`.
3. **The two guards.** `isPropClosed` and `maxBVarAt`, together. Removing either
   re-arms an uncatchable panic.

---

## 5. Verified output — check the JSON against these before building anything else

Hand-verified during the session (a full run was not required to obtain these):

```
Logos.AsietyFreedom.weakChoice_implies_asiety
  kind  thm
  goal  Logos.AsieticChoice.Asiety (Logos.Entity.EntityOf s)   ← binder named
  hyp   s : Logos.Agency.Subject ; p, q : Prop
  hyp   h : Logos.IndubitableNormativeFreeWill.GenuineNormativity
  head  Logos.AsieticChoice.Asiety
  sorts Logos.Agency.Subject, Prop, Prop, Logos.IndubitableNormativeFreeWill…

Logos.PersonalGroundOfReality.personal_ground_of_right_wrong
  goal  Logos.Person.Person s
  ← This is the whole point. The old Python extractor produced "Subject"
    (RULE_R_CORRECTION_PLAN.md §12.2). The Lean walker does not.

Logos.AsieticChoice.asietic_summary
  goal  (∀ s p, ChoiceField s p ¬p → ClaimsCorrect s p → Chooses s p ¬p)
        ∧ (∀ s {p q}, Chooses s p q → TrueChoice s p q)
        ∧ ∃ s p q, TrueChoice s p q
  ← the three-way conjunction whose union footprint is what the Asiety row
    currently misreports as one claim

Logos.AsieticChoice.Asiety            (def)
  goal   Prop
  value  Logos.AsieticChoice.TrueChoice        ← the identification, from the body

Logos.ActionChoiceDefinitions.Action   (def)
  goal   Prop
  sorts  Logos.Agency.Subject, Prop

Logos.A14DerivationAudit.NormativeSeparationModel.ModelSubject  (a countermodel)
  sorts  …NormativeSeparationModel.ModelSubject      ← G1 rejects on this symbol
```

The last line is the G1 test case from the plan: a model-local `ModelSubject` is a
*different symbol* from `Logos.Agency.Subject`, so a symbol-based comparator
separates them where a printed string would too easily agree.

---

## 6. Benchmark — is it slow, or is it looping?

**It is slow, and the slowness is interpreted execution, not a loop or a race.**
Measured with a standalone `bench.lean` walking a 200-declaration prefix twice:

```
n=200 pp=false took 822 ms      ← splitBinders + isProp only
n=200 pp=true  took 993 ms      ← + delaborating goal, hypotheses and sorts
```

So pretty-printing is ~17 % of the cost; `Meta.isProp` inference dominates. Yet
the full 5 951-declaration run takes several minutes of wall clock, because
`run_cmd` bodies are **interpreted** by `Lean.Language.Lean.process`, never
compiled. Extrapolated: ~1 s per 200 declarations of real work, but the observed
end-to-end rate is far lower. **Budget ~10 minutes and poll; do not assume a hang.**

If the runtime becomes a problem, the cheap win is to stop delaborating the goal
for `def`/`opaque` (whose goal string is just a sort name and is never shown) and
to keep strings only for `thm`/`axiom`. Do **not** drop shape coverage: the plan's
guard requires a record for all 5 951 declarations.

---

## 7. Process-management traps (each one cost real time)

* **`lake env lean` buffers stdout.** While it runs, `proc.stdout` is empty. An
  **empty log means "still running"**, not "no output". Check
  `ls -la formal/goal_audit.json`, not the log, for completion.
* **`pgrep -f audit_goals.py` false-positives on the polling command itself**,
  because `pgrep -f` matches the `bash -c '… audit_goals.py …'` string of the very
  command doing the polling. This produced three consecutive bogus "STILL RUNNING"
  readings. Use `pgrep -c lean`, or the bracket trick `pgrep -f "[a]udit_goals"`.
* **`nohup … &` is not enough.** The shell tool kills the whole process group when
  its own 120 s timeout fires, taking the detached child with it. Use
  `setsid nohup … < /dev/null &` and keep the polling `sleep`s under 120 s.
* Ignore the `axil -A -p 29xxx -m ./lib/axil-nd` processes (10 of them, ~430 MB RSS
  each). They are unrelated tooling, not Lean.

Canonical launch:

```sh
cd /home/quirinpa/logos
export PATH="$HOME/.elan/bin:$PATH"
setsid nohup python3 scripts/audit_goals.py > /tmp/opencode/goals.log 2>&1 < /dev/null &
# then poll in <120 s chunks:
ls -la formal/goal_audit.json || { tail -5 /tmp/opencode/goals.log; pgrep -c lean; }
```

---

## 8. The Python driver (`scripts/audit_goals.py`, ~409 lines)

Structure, so the next edit does not have to re-read the whole file:

| part | what it does |
|---|---|
| module docstring | states why the audit exists and why it is not string surgery |
| `LEAN_PROLOGUE` | the 176-line raw Lean string, `r"""…"""` (double quotes, because it contains ` ``And` `` quotations) |
| `_strip_log_prefix` | strips `file:line:col:` / `warning:` chatter, keeps `GA …` |
| `parse_ga` | returns `(records, count, errors, failed)`; `GA` tags: `name kind goal goalTag quant hypName hyp head value sort free end count failed ERROR` |
| `main` | writes the temp module, runs `lake env lean`, parses, guards, writes JSON |

Guards in `main`, all fail-closed:

* `depgraph.json` missing → instruct the `lake exe depviz` command.
* `lake env lean` non-zero → print the tail of both streams, `return 1`.
* any `GA ERROR` → `return 1` (**loud**, per §3.15).
* missing record for any of the 5 951 names → `return 1`.
* Lean-reported `GA count` ≠ parsed record count → `return 1`.
* a record with neither goal nor head symbols (excluding `def`/`opaque`) →
  `return 1`; a `thm`/`axiom` with a blank `goal` is a **note**, not an error,
  because `ppBinders` legitimately declines to print an out-of-range expression.
* a `Logos.*` constant appearing in a goal or hypothesis type that is **not a node
  of `depgraph.json`** → `return 1`. This is the cross-check that the shape
  reading is consistent with the graph the badge machinery consumes.

Derived fields computed in Python, not Lean: `headShorts` (basenames of
`headSyms`), and `quant` normalisation (`E`→`∃`, `A`→`∀`, else `null`).

The `lake` lookup mirrors `audit_footprints.py`: try `which lake`, else fall back to
`$HOME/.elan/bin/lake`.

---

## 9. Resume checklist

- [ ] Hoist/confirm the `maxBVarAt` guard so `Meta.withLocalDeclsDND` is never
      entered with an out-of-range expression; make structure-generated
      declarations yield `goal: ""`.
- [ ] Delete the per-declaration `try/catch` in `run`; keep `GA failed`.
- [ ] Run detached with `setsid`; expect ~10 min; poll for `formal/goal_audit.json`.
- [ ] Confirm 5 951 records, zero `GA ERROR`, and the §5 spot-checks.
- [ ] Add `python3 scripts/audit_goals.py` to the regeneration block in `AGENTS.md`,
      between `audit_footprints.py` and `build_deduction.py`.
- [ ] **Only then** implement `RULE_R_CORRECTION_PLAN.md` §7.2:
      `ClaimShape`, `_STRENGTH`, `verdict_of`, `select_route`, gates G1–G8 — then
      W1–W10.

## 10. Appendix — the verified working Lean core

This exact fragment compiles and produces the correct shapes. It is the part that
took the longest to get right; copy it rather than re-deriving it.

```lean
import Lean
import Lean.PrettyPrinter
import Logos

open Lean Meta Elab Command

namespace LogosGoalAudit

partial def maxBVarAt (e : Expr) (d : Nat) : Nat :=
  match e.consumeMData with
  | .bvar i          => max d (d + i + 1)
  | .app f a         => max (maxBVarAt f d) (maxBVarAt a d)
  | .lam _ _ b _     => maxBVarAt b (d + 1)
  | .forallE _ _ b _ => maxBVarAt b (d + 1)
  | .letE _ _ _ b _  => maxBVarAt b (d + 1)
  | .mdata _ b       => maxBVarAt b d
  | .proj _ _ b      => maxBVarAt b d
  | _                => d

def isPropClosed (d : Expr) : MetaM Bool :=
  isProp (d.abstractRange (maxBVarAt d 0 + 1) #[])

def headSym (e : Expr) : String :=
  match e.consumeMData.getAppFn with
  | .const n _ => n.toString
  | _ => "(non-constant)"

def ppBinders (binders : Array (Name × Expr)) (e : Expr) : MetaM String :=
  if maxBVarAt e 0 > binders.size then return ""
  Meta.withLocalDeclsDND binders fun fvars => do
    let fmt ← PrettyPrinter.ppExpr (e.instantiateRev fvars)
    return Std.Format.pretty fmt 240

partial def conjunctHeads (e : Expr) : MetaM (List String) := do
  let e := e.consumeMData
  if e.isAppOf ``And then
    let args := e.getAppArgs
    if args.size == 2 then
      return (← conjunctHeads args[0]!) ++ (← conjunctHeads args[1]!)
  match e.getAppFn with
  | .const n _ => return [n.toString]
  | _ => return []

partial def splitBinders (e : Expr) (hyps : List (Name × String)) (sorts : List String)
    (binders : List (Name × Expr)) :
    MetaM (Expr × List (Name × String) × List String × List (Name × Expr)) := do
  match e.consumeMData with
  | .forallE n d b _ =>
      let isP ← isPropClosed d
      let hyps' := if isP then (n, headSym d) :: hyps else hyps
      splitBinders b hyps' (headSym d :: sorts) ((n, d) :: binders)
  | .lam n d b _ => splitBinders b hyps (headSym d :: sorts) ((n, d) :: binders)
  | .letE n t _ b _ => splitBinders b hyps (headSym t :: sorts) ((n, t) :: binders)
  | _ => pure (e, hyps.reverse, sorts.reverse, binders.reverse)

def run : MetaM Unit := do
  let env ← getEnv
  -- walk env.constants, filter Logos + thm/def/axiom/opaque, qsort, emit
  -- ↑ elided here; see LEAN_PROLOGUE in scripts/audit_goals.py

run_cmd do liftCoreM (MetaM.run' run)

end LogosGoalAudit
```

Two standalone harnesses proved the core pieces before they were folded into the
generator; they are worth re-creating when debugging:

* **`instantiateRev` vs `instantiate1`** — walk a real declaration's type,
  strip its binders by hand, print the raw goal, then print
  `instBVars goal fvars`. The `#3 → #2 → #1 → #0` sequence in §3.4 is the
  whole diagnosis in four lines.
* **`bench.lean`** — time `splitBinders` with and without the delaborator over a
  200-declaration prefix. Answers "is it looping?" in one run (§6).
