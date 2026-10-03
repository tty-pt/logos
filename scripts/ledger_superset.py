"""The move-don't-delete check for the READINGPATH.md two-tier split.

Compares the pre-split README (`.snapshots/README.pre-split.md`) against the
union of the new `README.md` + `investigations/ledger.md` and FAILS if any
machine-identifiable content item is absent:

  1. every Lean identifier (dotted names, underscored names, CamelCase names),
  2. every claim id (C###, F##, FAITH-#),
  3. every table cell (cell-level, so a re-capped cell still passes iff it
     keeps every old cell's content as a substring),
  4. every full spine `summary` from formal/presentation_spine.json, verbatim
     in the ledger,
  5. the ledger's block inventory (chain headings, attribute rows, frontier
     rows, derivation and definition summaries).

Prose paragraphs are REPORTED, not fatal: the split deliberately compresses
prose (`summary` -> `summary_short`), and check 4 is the machine-checkable form
of "no sentence deleted". A dropped prose paragraph that is not covered by a
full summary in the ledger is printed for human review.

Stdlib only. Exit 0 iff every fatal check passes.
"""
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
NEW_README = ROOT / "README.md"
LEDGER = ROOT / "investigations" / "ledger.md"
SPINE = ROOT / "formal" / "presentation_spine.json"

STOPWORDS = {
    "lake", "lean", "make", "bash", "python", "python3", "details", "summary",
    "text", "json", "true", "false", "none", "readme", "ledger",
}

IDENT_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_'.]*?)`")
CLAIM_RE = re.compile(r"\b([CF](?:AITH)?-?\d+[a-z]?)\b")




ROADMAP_CELLS = {
    "**§1**", "**§2**", "**§3**", "**§4**", "**§5**",
    "**§6**", "**§7**", "**§8**", "**§9**", "**§10**",
    "Objective Right/Wrong", "Agential Ought", "Genuine Choice", "Free Will",
    "Free Subject", "Person", "Personal Will", "Ground of Right/Wrong",
    "Necessary Truth", "Constructive Ground",
    "Step", "Milestone", "Core Formula", "Epistemic Status",
    # the old table's transcribed formula/status cells (replaced by derived
    # rows; the typo'd "Boethian" is the old table's, kept here so the
    # allowlist matches exactly what was removed).
    "`¬N_T ∧ ¬N_F`", "`Ought TruthNorm ⟨s, p⟩`",
    "`Chooses s p q ∧ CommittedChoice s p q r`", "`FreeWill(s)`",
    "`FreeSubject(s) ≡ FreeWill(s)`",
    "`Person(s) ↔ Boethian-Thomistic Core`", "`FreeIndependentWill(s)`",
    "`GroundsRightWrong(s)`", "`□ τ ∧ GroundOfReality Entity.ofGround`",
    "`PersonalGroundOfReality Entity.ofGround`",
    "`✅` PROVEN · 0 substantive axioms", "`✅` PROVEN (Route A / Route B)",
    "`📖` DEFINITIONAL",
}


# Cells the pre-split README carried that the new surfaces deliberately do NOT,
# with the kernel change that retired each. Every entry names a replacement
# string that MUST be present in README.md + ledger.md, so an entry cannot be
# reused to smuggle a deletion through. 2026-09-30 (NIHILISM_DIE §16).
INTENTIONAL_REVISIONS: list[tuple[str, str, str]] = [
    (
        "&nbsp;&nbsp;· **F1bUncond** — The precise missing resource (F1b, BLOCKED)",
        "Row SUPERSEDED in GAPMAP (`F1bUncond`)",
        "F1bUncond was the open 'unconditional ∃ s, FreeWill s' frontier. C278 already "
        "proved it on one META bridge and the new corollary `freeSubject_exists` extends "
        "it to the `FreeSubject` name at the same price, so the frontier row is retired "
        "in favour of a named SUPERSEDED status (GAPMAP + ClaimMeanings + prose corpus).",
    ),
    (
        "**15 blocked** ✖ — named individually",
        "**14 blocked** ✖ — named individually",
        "Same retirement: F1bUncond is no longer BLOCKED, so the derived blocked count "
        "falls by one. The counter is derived, not transcribed.",
    ),
    (
        "**427 affirmative claims derived** out of **558** ledger claims — 362 ✅ kernel-verified, 65 ⚠️",
        "**426 affirmative claims derived** out of **558** ledger claims — 362 ✅ kernel-verified, 64 ⚠️",
        "F1bUncond left the affirmative count with its SUPERSEDED status; the new "
        "`freeSubject_exists` is recorded as a corollary of C278 rather than as a new "
        "claim id, so the count drops by one. Derived, never transcribed.",
    ),
    (
        "**965 of 1789 theorems in `formal/Logos/` rest on no Γ axiom at all** (54%)",
        "**965 of 1790 theorems in `formal/Logos/` rest on no Γ axiom at all** (54%)",
        "One theorem was added to the kernel (`Logos.AsieticChoice.freeSubject_exists`), "
        "re-audited at the same footprint as C278. The count is read from axiom_audit.json.",
    ),
    (
        "**One God / strict monotheism** (unity of the Divine Being)",
        "**One God** — unity of the Divine Being (one ground, one nature)",
        "The label carried two claims at two prices and read DEFERRED. Split: unity of "
        "the ground is PROVEN here, the person-level reading is the row below.",
    ),
    (
        "**Strict numerical unitarianism** (ruling out relational internal plurality/persons)",
        "**Numerical unitarianism** (the ground as a *single* Person — a unitarian monad)",
        "Retitled to the question it actually asks. The 2026-09-30 retitle to "
        "'Strict monotheism' was itself the regression and is reverted here: the word "
        "'monotheism' names unity of the Divine Being (one God — PROVEN, C320), so putting it on a "
        "person-count row made that row's 🧱 read as a verdict on monotheism. The row's own text now "
        "says what C212 says — a separation model: unicity does not entail a single Person, so the "
        "person-count is left open (`unicity_does_not_force_unitarian_monad`, `{}`).",
    ),
    (
        "**This label was carrying two claims; only one of them is still open",
        "**Unity of the ground and of the nature**",
        "Superseded by the split above; the sense cell is rewritten around one claim.",
    ),
    (
        "Proving that the universal ground of reality is structurally unique does not force that the internal life",
        "**Independence, not refutation:**",
        "The 2026-09-30 sense cell claimed the countermodel *forbids* the unitarian monad, "
        "which inverts C212: it shows unicity does not *entail* a single-Person ground, "
        "leaving the person-count open. Corrected 2026-10-01 (DISAMB.md).",
    ),
    (
        "`preceding_theory ⇏ trinity` (Binitarian separation model, footprint `{}`). A separate claim",
        "**One God, in three Persons**",
        "C510 (`agape_entails_tripersonality`) derives the three Persons on three declared "
        "META premises; the `{}` separation is kept in the row as the price, and the "
        "Trinity is priced rather than open.",
    ),
    (
        "**THE ACT DATUM IS NECESSARY, NOT STIPULATED — vocabulary-only, no `CL`**",
        "`F1bUncond` is now `SUPERSEDED`",
        "The same cell stated the retired F1bUncond status and was cut at the old 900-char "
        "cap; it is re-emitted uncapped with the corrected status.",
    ),
    (
        "⏸ DEFERRED",
        "DEFERRED — a claimed result whose Lean declaration is not in the live kernel",
        "The attribute table has no DEFERRED row any more: the one deferred row (monotheism) "
        "was split into a PROVEN row and a refuted row. The badge legend still defines the "
        "status, so nothing about DEFERRED is withdrawn from the surface.",
    ),
]


def table_cells(text: str) -> set[str]:
    cells = set()
    for ln in text.splitlines():
        s = ln.strip()
        if not s.startswith("|"):
            continue
        body = [c.strip() for c in s.split("|")[1:-1]]
        if not body or all(set(c) <= {"-", "—", ":"} for c in body):
            continue
        for c in body:
            if c:
                # A cell truncated by `_cap_table_cells` carries a ` […]`
                # marker: compare only the surviving head, which the ledger's
                # longer (higher-capped) cell must keep verbatim.
                head = c.split(" […]")[0]
                cells.add(re.sub(r"\s+", " ", head))
    return cells


def main() -> int:
    errors: list[str] = []

    # --- WHAT THIS SCRIPT NO LONGER CHECKS, AND WHY --------------------------------------
    # Checks 1-3 compared the union (README + ledger) against `.snapshots/README.pre-split.md`,
    # the pre-split README, to prove the 2026-09-30 two-tier move lost nothing: every identifier,
    # claim id and table cell of the old document had to reappear in one of the two new sinks.
    #
    # That baseline **was never committed** (`git log --all -- .snapshots/` is empty), so the
    # comparison could never run: the script raised FileNotFoundError on every invocation and was
    # not in `make`'s path, which is why the breakage went unnoticed. A check that has never
    # executed is not evidence, so those three checks are removed rather than left as dead code
    # that only crashes.
    #
    # The consequence is stated rather than papered over: **the superset property is no longer
    # machine-checked.** Nothing below verifies that the split preserved the old README, and no
    # green run of this script should be read as saying it did. Checks 4-5 survive because they
    # read the ledger and `presentation_spine.json` only. Restoring the property needs the
    # pre-split README itself — regenerate it with `audience: "full"` in
    # `formal/presentation_spine.json` and commit it under `.snapshots/`, then restore checks 1-3.
    print("NOTE: superset-vs-pre-split check is UNVERIFIED — the baseline "
          "`.snapshots/README.pre-split.md` does not exist in this repository. Checks 4-5 only.")

    # 4. full spine summaries verbatim in the ledger
    ledger = LEDGER.read_text(encoding="utf-8")
    spine = json.loads(SPINE.read_text(encoding="utf-8"))
    n_sum = 0
    for node in spine["spine_nodes"]:
        for key in ("summary",):
            full = (node.get(key) or "").strip()
            if not full:
                continue
            n_sum += 1
            if full not in ledger:
                errors.append(f"full {key} of spine node {node['id']} not verbatim in ledger")
        for b in node.get("branches", []):
            full = (b.get("summary") or "").strip()
            if not full:
                continue
            n_sum += 1
            if full not in ledger:
                errors.append(f"full summary of branch {b.get('id')} not verbatim in ledger")
    print(f"full summaries checked verbatim in ledger: {n_sum}")

    # 5. ledger block inventory
    def count(pat: str) -> int:
        return len(re.findall(pat, ledger, re.M))

    checks = {
        "chain block headings": (r"^### .*([Cc]hain, step by step|Chain \d+)", 14),
        "classical-attribute rows": (r"^\| \*\*", None),  # reported, threshold below
        # 33 -> 32 on 2026-09-30: F1bUncond's frontier row was retired when the
        # claim became SUPERSEDED (C278 + freeSubject_exists).
        # 31 -> 32 on 2026-10-03: C573 (strict perichoresis) entered the frontier as an
        # OPEN row. It is an *undefined predicate*, not an unproved lemma — nothing was
        # proved and no price changed; the corpus now names the missing relation instead
        # of leaving the gap implied by a predicate called `Perichoretic` that means
        # homoousios. Paired with the 31 it reverses: one withdrawal, one honest addition.
        # 32 -> 31 on 2026-10-03: C572 left the frontier when plan §24 withdrew it
        # as Modalism. The frontier is generated from statuses BLOCKED/DEFERRED/OPEN
        # (build_deduction.py:5820), so a withdrawn claim correctly stops being an
        # open question. This is a reduction in the *frontier*, not a resolved step:
        # nothing was proved, and C572 must never be counted as discharged. The count
        # is checked against the pin minus retired rows, never by wish.
        # 33 -> 32 on 2026-10-03: C573 (strict perichoresis) left the frontier when S1 showed
        # its content is already derived and free (`two_subsisting_share_one_location`,
        # `each_subsisting_person_is_in_the_other`, both `{Subject}`), leaving only the question
        # of whether to *name* what is already `=`. Its status is `WITHDRAWN (undefined
        # predicate)` — the C572 precedent — which means "not an open question", NOT "proved":
        # no `MutualIndwelling` primitive is declared and the mutual-indwelling formula is still
        # not a theorem of Γ. C574 enters as the OPEN row inheriting the residual naming
        # question, so the net movement is one withdrawal and one honest addition, same as the
        # C572/C573 pair above. Measured: 33 before, 32 after; the pin value is unchanged at 32
        # and the check below is `got < want`, so an under-count fails and an over-count is
        # reported by the printed count rather than silently tolerated.
        # 32 -> 33 on 2026-10-03: C580 (the `Subject`/`DivineHypostasis` correspondence) entered
        # the frontier as the AMOR/2 batch's BLOCKED row, with its missing lemma named and no
        # declaration bought. It is the only movement: C579 sits beside it and is `PROVEN`, so
        # it does not belong in a list of what the corpus cannot reach. Same convention as the
        # C572/C573 pairs above — the pin tracks the measured count and the check below is
        # `got < want`, so a withdrawal fails loudly and an addition is visible in the printout.
        "frontier rows": (r"^\* \*\*`", 33),
        "derivation summaries": (r"^<summary>Formal Derivation", 40),
        "definition summaries": (r"^<summary>Definitions used in this section", None),
    }
    for name, (pat, want) in checks.items():
        got = count(pat)
        print(f"ledger {name}: {got}" + (f" (want {want})" if want else ""))
        if want is not None and got < want:
            errors.append(f"ledger {name}: got {got}, want at least {want}")
    attr_rows = count(r"^\| \*\*")
    if attr_rows < 39:
        errors.append(f"ledger classical-attribute rows: got {attr_rows}, want >= 39")

    # the redesigned ten-step table covers the same ten facts
    readme = NEW_README.read_text(encoding="utf-8")
    ten_sec = readme.split("### The ten steps at a glance")[1].split("## ", 1)[0]
    ten = re.findall(r"^\| \*\*(\d+)\*\*", ten_sec, re.M)
    if sorted(int(t) for t in ten) != list(range(1, 11)):
        errors.append(f"ten-step table rows: got {sorted(ten)}, want 1-10")
    else:
        print(f"ten-step table: rows 1-10 present in README")

    if errors:
        print(f"\nFAIL: {len(errors)} problem(s):")
        for e in errors:
            print(f"  - {e}")
        return 1
    print("\nOK: the ledger's spine summaries are verbatim and its block inventory is complete. "
          "This does NOT certify the pre-split superset property (see the NOTE above).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
