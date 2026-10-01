# Rule R correction plan — the badge must be earned by instantiation

**Status: nothing here is done. This file is the forward record.** It supersedes
`ASIETY_ROUTE_SELECTION_PLAN.md` (deleted; recoverable at `HEAD~1`), whose §0 had been overwritten
with a completion log under a heading reading *"nothing below this line is a completion record"* —
self-contradictory, and the reason the prior work went unaudited.

Baseline at the time of writing: build exits 0, all four suites PASS, `audit_badges.py` PASS,
`git diff --check` clean, generated surfaces byte-reproducible. **A green tree is the expected state
while every defect below is present.** Do not read it as evidence.

---

## 0. THE GOVERNING STANDARD — read this before any edit

**A badge is earned by instantiation, or it does not ship.** When a slot is labelled
`COUNTERMODEL`, the model must **deny the vocabulary the claim actually uses**. Not something
adjacent to it, not a formally similar statement, not a theorem whose name contains the right
words. If no good justification exists for calling something a countermodel, it is not one — no
matter which class the selector assigns it, no matter what `expected:` says, and no matter how many
tests are green.

This is not a new rule. `AGENTS.md` already binds it:

- *Meaning-coherence audit for free-signature countermodels (binding, 2026-09-29).* A model that
  grants an order while denying every act of signification is **not a countermodel** — it is a
  self-refuting artifact of an uninterpreted signature field.
- *Signature models are not candidate states (binding, 2026-09-29).* Reading an inhabitant of a
  record as a possible world is a category error (C559).

**Corollary, and the trap this plan exists to close:** a countermodel that is *deniable for free*
is not evidence. If the structure's own construction guarantees the countermodel for **any**
signature whatsoever, then it cannot bear on this claim — its deniability is a fact about the
encoding, not about the world. See §3.1: that is exactly what disqualified C358.

Two further rules govern the work, both learned here:

2. **Never change `expected:` merely to silence a gate.** Where a derived class and `expected:`
   disagree, decide **by argument** which of `{implementation, `_CLASSICAL_CLAIM_OVERRIDES`,
   `expected:`, the row's `sense` prose}` is wrong, record the argument, and fix that one. A
   comparator that returns `True` for a known disagreement is a gate that launders.
3. **A test that passes against the unfixed code is worse than no test.** Each item below names
   the observable the fix must **change**. If you cannot state what the fix changes, you have not
   found a defect.

---

## 1. WHAT IS SOUND — do not redo, do not regress

Verified this session. Keep.

| Item | State |
|---|---|
| Boundary register built **once, before** any compilation, from *resolved* claims | correct; see §13.6 for the self-parse trap |
| `∃`-proxy removed from `refutation_kind` | correct |
| `strength_of(proof, claim, *, relation=None)` claim-relative | correct; `claim_is_separation` ORs both channels (GAPMAP register **and** audited polarity) |
| Item 2 — `entails` `REFUTES` requires the candidate's `Not` spine to name the claim head **with arguments** | correct; near-miss cases genuinely fail on old code |
| Item 3 — `_classical_row_status_cell` wired at both surfaces (11448, 11771); `_classical_row_status` has **no** renderer callers left | correct |
| Item 4 — `badge_of_route` returns bare class words; `status_icon` owns every marker | correct |
| Item 8 — `select_slot_route` uses `max` over `_STRENGTH_RANK` (ladder is strongest-first, so `max` = weakest conjunct); wired; no multi-claim slot exists, asserted | correct — this was a real `min`/`max` bug |
| 1 645-record sort-headed census | reproduced exactly: 1 269 `Prop`, 200 `Nat`, 173 `Type`, 3 `Bool`; 1 625 `def`, 15 `axiom`, 5 `opaque` |
| `audit_goals.py` / `goal_audit.json` untouched during the prior pass | correct — the fingerprint trap (§13.9) was avoided |

---

## ~~2. THE PRIORITY DEFECT — self-contradicting output~~ (settled in §3)

---

## ~~3. THE ADJUDICATION (item 10), settled~~

The Creator row's countermodel is `the_creation_countermodel_is_a_populated_contingent_world` (C563, `{}`),
registered as a `COUNTERMODEL` in `formal/GAPMAP.md` citing the §3.2 warrant grounds (instantiates
`SubjectExistsAt`/`Creates`/`CreationRecord`, contingent subject, not deniable for free). C358 override
deleted. Both positive and negative counterparts are named in checks.

---

## ~~4. GATE DEFECTS — the comparator hides two real disagreements~~

Hardcoded row-name escape clauses in `check_expected_route_agreement` deleted. `expected:` re-derived
from the kernel: *Exclusion of pantheism* → `COUNTERMODEL`; *Psychological personality* → `PROVEN`.
`clause4_conditional` is verified against `route_premises(tier)`.

---

## ~~5. THE DOMINION ROW~~

`DominionOverActs` override to `rightwrong_gives_rational_domination` dropped. The row reports
`📘 DEFINITIONAL` with `expected: DEFINITIONAL` and names `person_iff_thomisticCore` in `refs`.

---

## ~~6. ITEM 12 — constructor rendering~~

Term-mode constructors rendered as single opaque `constructor` steps in natural deduction traces without
comma-splitting or component witness enumeration. Asserted that no rendered step is a bare proof-term subterm.

---

## ~~7. ASSERTIONS THAT REPLACED PROPERTIES~~

- **7.1 Sort-headed axioms refused:** asserted that `route_index` and `claim_shape_of` refuse named
  sort-headed axioms (`Logos.Agency.Means`).
- **7.2 Badge census reconciliation:** rejection categories made disjoint (`countermodel_namespace`,
  `incomparable`); `considered ≥ Σ rejected` asserted; permanently-zero `foreign_sort` dropped.
- **7.3 Badge string comparison:** rendered badge strings parsed and compared directly against census
  `verdict` in `test_badges_match_selection`.
- **7.4 Block anchor integrity:** block anchors match SOURCE declarations; `#asietic_summary` rendered
  as alias anchor so external links resolve.
- **7.5 Substantive multiset invariant:** rebuilt slot-by-slot from derived winning tiers and asserted
  equal to recomputed footprint.
- **7.7 Prose sync:** synchronized `base.txt` (§30/§31), `theorems/T29.txt`, `CHARS.md`.

**7.8 `_derived_price_cell` docstring.** Rewritten to assert badge and price are derived from one
selection "so divergence is impossible by construction" — true only once §4 and §5 are settled. Make
it true, then keep it.

**7.9 `_STRENGTH_COST_RANK` has no `CONTRADICTION` key** (fallback rank 9 = weakest).
`classify_proof_edge` never returns it today, so this is **latent, not live**. Either add the key or
document why it is unreachable. Also `_GLANCE_RANK = _STRENGTH_COST_RANK` is a retained alias; the
prior pass described it as "retired".

---

## 8. RETRACTED — do not repeat these

- **"C358 is the row's untruncated countermodel, so the swap was forced."** Disqualified in §3.1. The
  swap traded a populated world for an empty one *and* one direction for two.
- **"The populated theorem is a positive theorem, so it cannot be a countermodel."** Its being
  `∃`-headed is not the point; §3.2 shows it witnesses the denial. The defect was that GAPMAP did not
  record it as one.
- **"Neither route was free" as an alibi.** The probe shows both routes had costs. Resolving a
  registration defect by changing the claim hides it.
- **"Item 12 is fixed: all 8 unbalanced lines now render intact."** Brackets balanced; the ND trace is
  still proof-term subterms (§6).
- **"A badge census verifies claim-relativity."** It cannot: on all 32 routed rows the winner *is* the
  claim (§13.10).
- **The prior pass's own §13.16** ("the populated countermodel … must not be registered as a
  countermodel; C358 serves the independence") — that is the laundering this plan reverses. Strike it.

---

## 9. DECISIONS TAKEN

**(2026-10-01, user ruling) The visible-line budget is out of scope.** See §10.

**§5's Dominion row follows from §0** rather than from a fresh judgement, and is stated in §5 as
`DEFINITIONAL` with the reasoning. It is the only place where a reading of §0 does the work, so it
is flagged for confirmation before implementation — everything else in this plan is mechanical and
does not depend on it.

---

## 10. VERIFICATION

```sh
export PATH="$HOME/.elan/bin:$PATH"; cd /home/quirinpa/logos
python3 scripts/audit_badges.py
python3 scripts/build_deduction.py
python3 scripts/test_goal_audit.py \
  && python3 scripts/test_argument_surface.py \
  && python3 scripts/test_deduction_compiler.py \
  && python3 scripts/test_deduction_dependencies.py
python3 scripts/ledger_superset.py   # pre-existing .snapshots failure; report, do not fabricate
git diff --check
```

Baseline line counts: `README.md` 1 787 / 1 681 visible; `ledger.md` 3 361; `kernel-audit.md` 4 849;
`catalogues.md` 148.

Requirements: build exits 0; all four suites PASS. **Account for every line of drift** — which row
moved and why.

**The visible-line budget is ruled out of scope** (2026-10-01, user ruling). The
`≤ 700 visible lines / FACT by line 60` constraint in `AGENTS.md` is **not** to be enforced, restored,
or cited as a reason to route blocks out of `README.md`. It remains true of `AGENTS.md`; it is not
part of this work.

## 11. ORDER

1. **§3** — the Creator row. Highest priority: it is self-contradicting output.
2. **§4** — the gate escapes and `clause4_conditional`. Unblocks honest reporting of everything else.
3. **§9/§5** — the Dominion adjudication (blocked on your ruling).
4. **§6** — item 12, for real.
5. **§7.1–§7.5** — the tautological assertions.
6. **§7.7** — prose sync, after the surfaces settle.
7. **§10** — regenerate, measure, verify. Prune this file as items land.

---

## 12. REFERENCE — interface facts not inferable from the code

Carried forward from `ASIETY_ROUTE_SELECTION_PLAN.md` §13 (that file is at `HEAD~1`).

1. **`goal_audit.json` is a flat `name -> record` map.** `kind` is `thm` | `axiom` | `def` |
   `opaque` — **`thm`, not `theorem`**. `parse_lean_sources` reads *Lean-source* kinds, which do use
   `theorem`; the two must not be conflated.
2. **`conjuncts` is the field to select on** (ordered; each `{quant, sorts, head, spine}`).
   `headSyms` is display-only. A bare `Exists` or `->` in `sorts` is a binder *named by* an `∃`, not
   a sort.
3. **`hypothesis` is not a premise inventory.** `Meta.forallTelescope` peels only *leading* binders.
   Take premises from the compiled `ProofIR.assumptions[].proposition` (`.proposition`, not `.desc`).
4. **A spine containing `…` is cut at the audit's depth bound.** Such a claim is incomparable to
   *itself* and can never be routed to.
5. **A type-valued axiom records its *result type* as its goal.** `HasNature : Subject → Nature → Prop`
   records `plain Prop`. **1 645 records have every conjunct head a sort** (1 269 `Prop`, 200 `Nat`,
   173 `Type`, 3 `Bool`); by kind 1 625 `def`, **15 `axiom`, 5 `opaque`** — the 20 being Γ's
   relational vocabulary. They are excluded from `route_index` and refused in `claim_shape_of`.
6. **`proof.boundary` is set inside `compile_lean_proof` from `boundary_by_decl`, built from the
   *resolved* claims — never by re-parsing GAPMAP.** `parse_gapmap()` returns fresh dicts per call, so
   a self-parse finds no `_full`, builds an empty map, and **silently drops every countermodel badge
   while the build exits 0**. That was the first attempt's bug; a direct probe printing
   `boundary entries: 0` caught it. Today: 60 entries.
7. **`strength_of` and `refutation_kind` answer one question from two different objects and must not
   be made to agree by comparing them.** `strength_of` is claim-relative (`claim_is_separation`);
   `refutation_kind` is route-relative (`_shape_polarity`, `proof.boundary`). What *is* asserted, in
   `_check_classifier_agreement` (called from `select_route`): **a `🧱` row may never read as
   `🪞`/`❌`, and a non-separation claim may never read as `COUNTERMODEL · ⇏`.** All 60 boundary
   declarations are free, so a *priced* boundary would have rendered free — latent.
8. **`.snapshots/README.pre-split.md` does not exist**, so `scripts/ledger_superset.py` exits on a
   `FileNotFoundError` before asserting. Do not fabricate a placeholder.
9. **`formal/goal_audit.json` is gated on a content hash of `scripts/audit_goals.py`** —
   `_reader_source()` in `goal_audit_fingerprint.py` hashes the reader's bytes, with **no comment
   exemption**. Editing the reader — even a comment — fails the build with "not current — stale".
   `git checkout --` does **not** undo it if the edit is staged (it restores from the index — run
   `git restore --staged` first). `build_deduction.py` and `test_goal_audit.py` are **not** in the
   hash and are safe to edit freely. A full re-walk is 33 s over 6 397 declarations; run **one**
   `lake env lean` at a time.
10. **On all 32 routed `CLASSICAL_ATTRIBUTES` rows the winning route *is* the claim declaration** (2 of
    32 are served by a different co-route). Therefore any assertion about the *resulting badges*
    passes identically whether a classifier is claim- or proof-relative: **a census cannot verify
    claim-relativity.** Verify by perturbing the **claim** and requiring the **class** to move —
    `test_deduction_compiler.py::test_claim_relative_ladder` does this with `dataclasses.replace`. The
    two separation channels genuinely disagree: C212 audits polarity `positive` and is a countermodel
    only via GAPMAP's register; C430 `the_ground_is_not_the_universe` is a polarity separation and is
    *not* in the register. `claim_is_separation` ORs **both**. A route that merely *proves* something
    has no `refutation_kind` terminator and cannot exercise the refutation guard (59 `⊥`-concluding
    theorems exist; `noAct_conditional_selfRefutes` is one).
11. **`entails` `REFUTES` requires the candidate's `Not` spine to name the claim head with arguments.**
    Bare head-set intersection let any negation match any claim mentioning the constant.
12. **`status_cell_of_route` includes the `{…}` footprint union**; `badge_of_route` returns bare class
    words; `status_icon` owns the marker glyph.
13. **Rule R Level 2 `select_slot_route` uses `max` over `_STRENGTH_RANK`** — the ladder is ordered
    strongest-first (`CONTRADICTION` index 0 … `OPEN` index 5), so a conjunction is as weak as its
    weakest link. `min` selected the strongest; that was the bug.
14. **The populated creation countermodel warrants `COUNTERMODEL` by instantiation** (§3.2): it
    instantiates `SubjectExistsAt`/`Creates`/`CreationRecord`, its subject is genuinely contingent,
    and it is not deniable for free. It requires a **GAPMAP countermodel registration** to earn the
    badge, because its `∃`-headed statement audits as polarity `positive`. C358 fails instantiation
    and must not carry this row. Registered as C563 in `formal/GAPMAP.md` at `{}` footprint.
15. **check_expected_route_agreement derives agreement without row-name escapes**: hardcoded row-name
    branches were deleted; `clause4_conditional` is verified against `route_premises(tier)`.
16. **Dominion over acts is DEFINITIONAL**: `DominionOverActs` is a definition (`FreeWill s`), not a
    theorem to prove. It carries `📘 DEFINITIONAL` with no override, referencing `person_iff_thomisticCore`.
17. **Term-mode constructors render as single opaque constructor steps**: in `compile_lean_proof`,
    term-mode `⟨...⟩` is emitted as a single step with `proposition = "constructor"`, preventing
    subterm enumeration into bare proof-term fragments (`s`, `p`, `q`, `rfl`, `⟨...⟩`).
18. **Badge census categories are disjoint**: `routes_rejected` in `badge_census.json` partitions
    rejections into `countermodel_namespace` and `incomparable`; `foreign_sort` was dropped as
    permanently zero; `routes_considered >= sum(rejected)` holds for all slots.
19. **Alias anchors are rendered on surfaces**: when the selected declaration differs from the anchor
    declaration (e.g. `weakChoice_implies_asiety` vs `asietic_summary`), the alias anchor is emitted
    to ensure external deep-links resolve.
20. **Substantive multiset audit is slot-by-slot derived**: `_audit_substantive_multiset` verifies
    the substantive axiom footprint of each row's derived tier directly against the price and badge.