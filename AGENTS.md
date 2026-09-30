# AGENTS.md — Project conventions (Γ / Logos)

## Sync rule (mandatory)

The prose corpus (`base.txt`, `theorems/*.txt`, `poem.txt`) is the canonical text of Γ and
**must always reflect the current formal status** produced by the Lean formalization in `formal/`.

Whenever the formalization changes:

- **new theorem verified** → create or update the matching theorem file (`theorems/T*.txt`), with
  `Depends on:` listing the exact Lean file and its axiom footprint.
- **step demoted to axiom** → mark it `AXIOM` in the prose (`base.txt`/relevant `T*.txt`).
  Never let prose keep presenting it as derived. Record the consistency-model note.
- **step blocked / still requires proof** → record the exact missing lemma (formal statement)
  in the prose "still requires proof" list (see `base.txt` §28 style).
- **new file added** → update dependency lines and section references in `base.txt` and the theorem files.
- Only something already machine-verified (or an explicitly tagged axiom) may be called
  "derived"/"undeniable" in prose.

Concrete practice: after each milestone, re-read the affected prose files and patch them so the
prose and the Lean theorem ledger agree (see `formal/GAPMAP.md`).

## README.md + investigations/ledger.md (two-tier generated surface)

`README.md` (repo root) is the generated **argument**: ~500 fully-visible lines,
zero collapsed blocks, the thesis (C553 FACT) by line 60. `investigations/ledger.md`
is the generated **audit**: the 14 step-by-step chain blocks, the 39 classical-attribute
rows with full prose, all 40 natural-deduction traces, the ASCII flowchart, the
frontier list, and the full per-step prose. Both files are emitted by one pass of
`scripts/build_deduction.py` over the kernel; the ledger is a superset of the old
single document, and that is machine-checked (`scripts/ledger_superset.py` against
`.snapshots/README.pre-split.md`, plus `scripts/test_argument_surface.py`), not promised.

Statuses are **derived, never transcribed**: each step's badge is a pure function of
(kernel node kind, audited `#print axioms` footprint, declared axiom `Tag:`). The GAPMAP
status/footprint cells are checked against the derived values, never used as their source.
**Never edit either file by hand.** Plan of record: `READINGPATH.md`.

Regeneration (after any Lean/GAPMAP change):

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd formal && lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot
cd .. && python3 scripts/audit_footprints.py && python3 scripts/build_deduction.py
```

- **The Cremation is derivation, not badge (binding, 2026-09-30; `CREMATION.md`,
  `NIHILISM_DIE.md` §17).** Every row of README §13 that claims a death must print the
  compiled premises, the steps, a **derived** terminator and the audited footprint, with the
  Lean anchor. The three terminator kinds (`⊥ CONTRADICTION`, `⊘ DENIAL REFUTED`,
  `COLLAPSE — INCOHERENT`) are selected by `refutation_kind` from the audited goal shape and
  footprint — never typed into JSON. Five gates fail the build: an unresolvable target, a
  substantive axiom on a row claiming a *free* death, a `denial_hypothesis` that is not a real
  premise of the theorem, a `✅` price line that does not read "0 substantive axioms", and a
  dead branch presented as a table row. A priced route is declared `"priced": true` and printed
  `⚠️ AXIOMATIC (<axiom>)` — it is never laundered into a `✅`, which is the defect
  `_GLANCE_RANK` had (it keyed a display string against internal categories, so every §13 link
  read `0 substantive axioms`). A `{}` proof over `NegativeRetorsionSignature`-style premises is
  a **signature artifact**, not a death: see AGENTS.md, 2026-09-29.
- `scripts/build_deduction.py` has a **hand-authored** chain list per batch
  (`ASIETY_FREEDOM_STEPS`): badges and footprints in that block are derived, but the list's
  *membership* is maintained by hand. **Adding a declaration to a chain module does not add it to
  `README.md`** — extend the list in the same change, or the reader-facing chain silently omits
  the new step. (`kernel-audit.md` is unaffected; it reads GAPMAP.)
- `formal/depgraph.json`/`.dot` are produced by the LeanDepViz dep (see `formal/lakefile.toml`),
  rebuilt with `lake build depviz` after a toolchain/dependency change.
- `formal/axiom_audit.json` is produced by `scripts/audit_footprints.py`: a temp
  `import Logos` module with a `#print axioms` line per declaration is run through
  `lake env lean`, giving the exact transitive kernel axiom set (incl. CL) for every
  node. The graph's own `customAxioms` field undercounts transitively and is used
  only for the dependency edges, never for footprints.
- The script is stdlib-only; it parses `formal/Logos/*.lean` (declarations + line numbers),
  `formal/GAPMAP.md` (claim IDs, prose refs), `axiom_audit.json` (authoritative
  footprints), and `depgraph.json` (nodes with kinds, edges), and renders
  `README.md` in English (from the English closed-caption docstrings in the Lean
  sources; the prose corpus `base.txt`/`theorems/*.txt` stays Portuguese).
- Each axiom carries its type on the first line of its `/-- … -/` docstring —
  `Tag: VOCAB` (vocabulary of the statement itself), `Tag: SEM` (semantic choice),
  `Tag: META` (metaphysical bridge) — closed vocabulary; an untagged or mistyped
  axiom is a regeneration error, not a note.
- Statements are displayed in logic symbols (`scripts` `humanise()`); the per-step English
  sentences live in **code**: as the first paragraph of the `/-- … -/` docstring directly
  above each axiom/theorem/def in `formal/Logos/*.lean` (after the `Tag:` line for
  axioms), and as `def NAME : String := "…"`
  values in `formal/Logos/ClaimMeanings.lean` for claims with no kernel declaration.
  Claims/axioms without a gloss are flagged in the consistency section — author the
  sentence in the Lean source, don't leave the row bare.
- `lake`/`lean` are not on PATH by default: export `$HOME/.elan/bin` first.

## Language

- Lean code: comments in **English**.
- Prose corpus (`base.txt`, `theorems/*.txt`): **Portuguese** (keep existing).
- Conversation: match the user.

## Toolchain & verification

- Lean 4 (no mathlib dependency — removed as unused; no file uses any Mathlib
  lemma. Re-add only if a future formalization truly needs it). Project root `formal/`.
- Verification command: `lake build` (run from `formal/`).
- **Meaning-coherence audit for free-signature countermodels (binding, 2026-09-29).**
  Before any `{}` countermodel is reported, check that it actually instantiates the
  vocabulary it is supposed to deny. A model that grants an order while denying
  every act of signification (`Means := fun _ _ => False` alongside `EO := True`)
  is **not a countermodel** — it is a self-refuting artifact of an uninterpreted
  signature field, and reporting it overstates the ledger. It was exactly this
  defect in `NegativeRetorsionSignature` that made C382/C385 read as though they
  preserved the very order they were built to refute
  (`investigations/right-and-wrong.md` §4b). The general rule: *check that the
  model instantiates the vocabulary it denies.*
- **Signature models are not candidate states (binding, 2026-09-29).** A
  free-signature countermodel witnesses that a constraint is underivable from a
  signature; it is never evidence about a state of affairs. Γ’s core vocabulary
  (`Subject`, `Prop`, `State`, `Means`, `Initiates`) contains no `World` sort, so no
  expression of Γ denotes a world-state. Reading an inhabitant of a record (M0, M1,
  M6) as a possible world is a category error — ledgered as C559
  (`EpistemicNecessity.signature_model_reading_discipline`), which governs every
  countermodel row.
- **Alethic discipline (binding, 2026-09-29).** In normative contexts “true” means
  truth-to-a-subject (`TrueTo`/`Correct`, C562: `Correct → TrueTo → T`), never bare-`T`
  satisfaction. `T p` is being-the-case and is free; being-true is disclosure and is
  always to someone. Do not call satisfaction “true” where right/wrong is at issue.
- **README intelligibility (binding, 2026-09-29).** `README.md` is generated; the reading
  path is the argument. No prose block may stand above a table without a C-id or Lean
  anchor in it (no facade); table prose cells are capped at 900 chars (full text one click
  away via footer links); the retorsion/countermodel catalogues live in
  `investigations/catalogues.md`, never in `README.md`. Score block stays verbatim.
  `scripts/build_deduction.py::_lint_readme` enforces caps, catalogue absence, and banned
  snippets machine-checked; the facade rule is enforced in review.
- **Two-tier split (binding, 2026-09-29; see `READINGPATH.md`).** The reading path is
  the argument and nothing else: ≤700 visible lines (amended 2026-09-30, twice: 520 → 522, then 522 → 700 when the cremation became derivations rather than badges), zero `<details>`, no chain blocks,
  no ASCII art, no retired rows, no paragraph over 300 chars outside the locked score
  block, FACT by line 60. Everything moved out lives in generated
  `investigations/ledger.md`, and the move is checked, not asserted
  (`scripts/ledger_superset.py`, `scripts/test_argument_surface.py`,
  `_lint_surfaces`). A block is routed by exactly one `include_*` flag in
  `formal/presentation_spine.json` `presentation_policy`; a block that reaches neither
  sink fails the build. `audience: "full"` restores the pre-split document for
  regression testing only.
- Axiom footprint of every claim must be inspected via `#print axioms` and recorded in
  `formal/GAPMAP.md`. Theorem statuses: `PROVEN`, `PROVEN↑` (proven under flagged axioms),
  `AXIOM`, `BLOCKED`, `DEFERRED`.
- **Display mapping:** `PROVEN↑` is the ledger/GAPMAP status only. Reader-facing
  display in generated `README.md`/`kernel-audit.md` says **AXIOMATIC** (`AXIOMATIC (X)`,
  where `X` is the named axiom) via `classify_proof_edge`/`compute_epistemic_badge`
  in `scripts/build_deduction.py`; internal category strings (`SEMANTIC`/`METAPHYSICAL`)
  stay unchanged so the test suites and IL compilers remain stable. `AXIOMATIC ≠ unproved`
  (machine-verified, rests on a declared axiom); `AXIOM` = the claim itself is an axiom.
- Axiom justification tags: `TRANS` (performative/transcendental), `SEM` (semantic choice,
  with consistency-model note), `META` (metaphysical bridge, with price made explicit).

## Build & cache

- Project modules import only Lean core + each other, so `lake build` is
  seconds and incremental. If mathlib is ever re-added as a dependency, the
  first `lake build` after a fresh `lake update` can take ~45 min on a cache
  miss; then re-run `lake update mathlib` (resolves the exact rev the public
  cache was built at) and build again.
- When a long build is expected, run it as a logged background job
  (`nohup lake build > /tmp/logos-build.log 2>&1 &`) and poll; killing a build only
  costs the resume, never restarts from zero.

## Git

No commits unless the user explicitly asks. When committing, stage intent only.