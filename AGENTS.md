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

## Language

- Lean code: comments in **English**.
- Prose corpus (`base.txt`, `theorems/*.txt`): **Portuguese** (keep existing).
- Conversation: match the user.

## Toolchain & verification

- Lean 4 (no mathlib dependency — removed as unused; no file uses any Mathlib
  lemma. Re-add only if a future formalization truly needs it). Project root `formal/`.
- Verification command: `lake build` (run from `formal/`).
- Axiom footprint of every claim must be inspected via `#print axioms` and recorded in
  `formal/GAPMAP.md`. Theorem statuses: `PROVEN`, `PROVEN↑` (proven under flagged axioms),
  `AXIOM`, `BLOCKED`, `DEFERRED`.
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