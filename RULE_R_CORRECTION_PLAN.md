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

## 1. WHAT IS SOUND (retained baseline)
Boundary register built before compilation from resolved claims; `∃`-proxy removed; claim-relative `strength_of`; `entails` argument matching; unified status cell; bare badge words; `max` over `_STRENGTH_RANK`.

## 2. THE PRIORITY DEFECT (self-contradicting output resolved)
Creator row previously cited unpopulated C358 while prose claimed populated world; resolved in §3/§12.14.

## 3. THE ADJUDICATION (Creator row countermodel swap and registration)
Warranted countermodel `the_creation_countermodel_is_a_populated_contingent_world` (C563) registered in GAPMAP; C358 override deleted; see §12.14 for instantiation evidence.

## 4. GATE DEFECTS (comparator escapes removed)
Deleted row-name escapes in `check_expected_route_agreement`; re-derived `Exclusion of pantheism` (`COUNTERMODEL`) and `Psychological personality` (`PROVEN`); `clause4_conditional` verified against `route_premises(tier)`.

## 5. THE DOMINION ROW (definitional resolution)
`DominionOverActs` is a definition (`FreeWill s`), not a theorem; override dropped, expected set to `DEFINITIONAL` (📘), `person_iff_thomisticCore` added to `refs`.

## 6. ITEM 12 (natural deduction constructor rendering)
Term-mode constructors rendered as single opaque `constructor` steps in natural deduction traces without comma-splitting or component witness enumeration.

## 7. ASSERTIONS THAT REPLACED PROPERTIES (property tests landed)
§7.1 sort-headed axioms refused; §7.2 census categories disjoint and reconciled; §7.3 badge strings compared against census verdicts; §7.4 block anchor integrity and `#asietic_summary` alias; §7.5 substantive footprint audit; §7.7 prose sync across `CHARS.md`, `theorems/T29.txt`, `base.txt`.

## 8. RETRACTED CLAIMS
Prior rationalizations for C358 swap, positive-theorem non-countermodel status, and bracket-only Item 12 fixes retracted.

## 9. DECISIONS TAKEN
Visible-line budget ruled out of scope (2026-10-01); Dominion row definitional resolution confirmed.

## 10. VERIFICATION COMMANDS
Standard test suite run (`audit_badges.py`, `build_deduction.py`, all four test suites, `git diff --check`).

## 11. IMPLEMENTATION ORDER
Completed in dependency sequence §§3 → 4 → 5 → 6 → 7 → 10.

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
14. **The populated creation countermodel warrants `COUNTERMODEL` by instantiation**:
    `populatedCreationWorld` witnesses `the_creation_countermodel_is_a_populated_contingent_world`:
    `ExistsAt := fun _ _ => True`, `actualWorld := true`, `SubjectExistsAt := fun w _ => w = true`,
    `Ground := fun _ _ => True`, `Creates := fun _ _ => False`, `g := ()`, `s := ()`, `s_actual := rfl`,
    `s_contingent := ⟨false, …⟩`. It instantiates `SubjectExistsAt`/`Creates`/`CreationRecord`, its
    subject is genuinely contingent, and it is not deniable for free (distinguishing grounding from
    productive creation). It requires a **GAPMAP countermodel registration** (C563, `{}`) to earn
    the badge, because its `∃`-headed statement audits as polarity `positive`. C358 fails instantiation
    and must not carry this row.
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