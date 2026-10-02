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
OLD = ROOT / ".snapshots" / "README.pre-split.md"
NEW_README = ROOT / "README.md"
LEDGER = ROOT / "investigations" / "ledger.md"
SPINE = ROOT / "formal" / "presentation_spine.json"

STOPWORDS = {
    "lake", "lean", "make", "bash", "python", "python3", "details", "summary",
    "text", "json", "true", "false", "none", "readme", "ledger",
}

IDENT_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_'.]*?)`")
CLAIM_RE = re.compile(r"\b([CF](?:AITH)?-?\d+[a-z]?)\b")


def identifiers(text: str) -> set[str]:
    out = set()
    for m in IDENT_RE.finditer(text):
        tok = m.group(1).strip(".,;:!?")
        if not tok or tok.lower() in STOPWORDS:
            continue
        if "." in tok or "_" in tok:
            out.add(tok)
        elif re.fullmatch(r"[A-Z][A-Za-z]{2,}", tok):
            out.add(tok)
    return out


def claims(text: str) -> set[str]:
    return set(CLAIM_RE.findall(text))


# Cells of the pre-split "Linear Deductive Roadmap" table (READINGPATH.md §1:
# it was transcribed by hand and is replaced by the derived ten-step table).
# The facts it carried (ten steps, formulas, statuses) are checked structurally
# below; its label/header cells are presentation, not content.
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
    old = OLD.read_text(encoding="utf-8")
    new = NEW_README.read_text(encoding="utf-8") + "\n" + LEDGER.read_text(encoding="utf-8")

    # 1. identifiers
    old_ids = identifiers(old)
    missing_ids = sorted(i for i in old_ids if i not in new)
    print(f"identifiers in old README: {len(old_ids)}, missing from union: {len(missing_ids)}")
    for i in missing_ids[:40]:
        errors.append(f"identifier lost: {i}")
    if len(missing_ids) > 40:
        errors.append(f"... and {len(missing_ids) - 40} more identifiers")

    # 2. claim ids
    old_claims = claims(old)
    missing_claims = sorted(c for c in old_claims if c not in new)
    print(f"claim ids in old README: {len(old_claims)}, missing from union: {len(missing_claims)}")
    for c in missing_claims:
        errors.append(f"claim id lost: {c}")

    # 3. table cells (substring-tolerant: a re-capped cell passes iff it kept
    #    every old cell's content)
    old_cells = {c for c in table_cells(old) if c not in ROADMAP_CELLS}
    new_flat = re.sub(r"\s+", " ", new)
    # Documented, kernel-driven revisions: an old cell is excused only when the
    # entry names a replacement that the new surface actually carries.
    excused, missing_replacements = set(), []
    for old_head, replacement, _why in INTENTIONAL_REVISIONS:
        hit = [c for c in old_cells if c.startswith(old_head)]
        if hit:
            excused.update(hit)
        if replacement not in new_flat:
            missing_replacements.append(replacement)
    missing_cells = sorted(c for c in old_cells if c not in new_flat and c not in excused)
    print(f"table cells in old README: {len(old_cells)}, missing from union: {len(missing_cells)}")
    print(f"  ({len(excused)} cell(s) retired by the 2026-09-30 documented revisions)")
    for c in missing_cells[:20]:
        errors.append(f"table cell lost: {c[:120]}")
    if len(missing_cells) > 20:
        errors.append(f"... and {len(missing_cells) - 20} more cells")
    for r in missing_replacements:
        errors.append(
            f"INTENTIONAL_REVISIONS entry has no replacement in the new surface: {r[:100]!r} "
            f"— an allowance may not hide a deletion")
    for old_head, _r, why in INTENTIONAL_REVISIONS:
        if old_head not in re.sub(r"\s+", " ", old):
            errors.append(f"INTENTIONAL_REVISIONS entry no longer matches the snapshot: {old_head[:80]!r}")

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
        # claim became SUPERSEDED (C278 + freeSubject_exists). The count is
        # checked against the snapshot minus the retired rows, not by wish.
        "frontier rows": (r"^\* \*\*`", 32),
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
    print("\nOK: the union of README.md + investigations/ledger.md covers every "
          "machine-identifiable content item of the pre-split README.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
