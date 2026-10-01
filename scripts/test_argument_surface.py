#!/usr/bin/env python3
"""test_argument_surface.py — the READINGPATH.md two-tier contract, machine-checked.

README.md is the argument (fully visible, no collapsed blocks, FACT early);
investigations/ledger.md is the audit (chains, tables, derivations, full prose);
their union loses nothing from the pre-split README (see ledger_superset.py).

Fails the build on any regression of the split.
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))  # so `import scripts.build_deduction` resolves
import scripts.build_deduction as bd  # noqa: E402
README = ROOT / "README.md"
LEDGER = ROOT / "investigations" / "ledger.md"


def _branches(needles: tuple[str, ...]) -> list[str]:
    """Resolve branch labels from the spine instead of restating them here.

    A needle is a *stable* handle on a row — the `D3`…`D6` tags, or a phrase
    long enough to be unique — and this returns the row's current `branch`.
    Restating whole labels in this file is what broke twice: once for the role
    table (line 218) and once for `"Impersonal normativity (D4)"`, which the
    R10 rename turned stale. A needle that no longer resolves to exactly one row
    aborts: silently skipping it would make the assertions below vacuous, which
    is the failure mode this function exists to remove.
    """
    spine = json.loads((ROOT / "formal" / "presentation_spine.json").read_text(
        encoding="utf-8"))
    rows = next(s for s in spine["reading_sections"] if s.get("cremation"))["cremation"]
    out = []
    for needle in needles:
        hits = [r["branch"] for r in rows if needle in r["branch"]]
        if len(hits) != 1:
            raise SystemExit(
                f"test_argument_surface: needle {needle!r} resolves to {len(hits)} "
                f"branches {hits}; it must name exactly one row in "
                f"formal/presentation_spine.json")
        out.append(hits[0])
    return out


def main() -> int:
    errors: list[str] = []
    readme = README.read_text(encoding="utf-8")
    ledger = LEDGER.read_text(encoding="utf-8")

    def check(cond: bool, msg: str) -> None:
        print(f"  {'✓' if cond else '✗'} {msg}")
        if not cond:
            errors.append(msg)

    # --- the argument surface ---
    check("<details>" not in readme and "</details>" not in readme,
          "README has zero collapsed <details> blocks")
    check("step by step" not in readme,
          "no chain blocks on the reading path")
    check("│" not in readme and "┌" not in readme,
          "no ASCII box-drawing on the reading path")
    visible = [l for l in readme.splitlines()
               if not l.strip().startswith("<")]
    # DEDUCTION.md §8 (D8, 2026-09-30) and `READINGPATH.md` §6: 700 → 1400 for
    # Part II's eighteen characteristic blocks, then 1400 → 1600 re-derived from
    # the measured document when the sixteen `R`-entries and Part IV's seam landed
    # and the 39-row table left the path, then 1600 → 1715 with Phase 3's derived
    # proof-kind line (CLEARER.md §6) — one line per proof body, and the reason it
    # is worth paying for is that a reader can now see a block is a projection or
    # three identities — then 1715 → 1740 with Phase 2's navigation
    # (`CLEARER.md` §5): Part II's eighteen-row index, since characteristic #14
    # was unreachable. Phase 2's other 41 lines are the `▸` component anchors,
    # which cost *nothing* here: the `visible` filter above drops every line
    # starting with `<`. The reading path's real constraint is
    # the shape invariants asserted in `build_deduction._lint_readme` (B1-B6, no
    # `<details>`, unique titles, the declared part order) plus the part-order and
    # score-position checks below; this number catches a block becoming a wall.
    # It tracks `build_deduction.README_VISIBLE_BUDGET` deliberately: when the two
    # disagreed, the looser one was decoration.
    check(len(visible) <= 1740, f"README visible lines {len(visible)} <= 1740")
    check(readme.startswith("# Γ — The Deduction\n"),
          "README opens with the title")
    fact_at = readme.find("for which meaning can mean")
    check(fact_at != -1 and readme[:fact_at].count("\n") + 1 <= 60,
          "thesis sentence (C553 FACT) lands by line 60")
    # The reading path is Parts I–IV in the declared order (DEDUCTION.md §3), with
    # the score LAST. The old assertions pinned `## 11.`–`## 15.` and the score
    # first; both were the defect, so the strings below are the new headings *and*
    # their order is asserted, which is the part that actually matters.
    for sec in ["### Step 1 — Satisfaction Is Free",
                "### Step 9 — The Fact",
                "## Part I — The deduction",
                "## Part II — The characteristics of the ground",
                "## Part III — The refutations",
                "## Part IV — the seam",
                "### Necessity, and Exactly What It Costs",
                "### One God, in Three Persons",
                "### What the Instrument Cannot See",
                "### What Is Not Established",
                "## Where the Rest of the Ledger Lives"]:
        check(sec in readme, f"README carries {sec[:44]}")
    # DEDUCTION.md §3: the declared order is I → II → III → IV, and the score
    # comes after all four. Position, not presence, is the readability contract:
    # a reader who meets Part IV before Part II cannot follow the argument.
    _order = [readme.index(h) for h in
              ("## Part I — The deduction", "## Part II — The characteristics",
               "## Part III — The refutations", "## Part IV — the seam",
               "## The score: what Γ has won")]
    check(_order == sorted(_order),
          f"the parts appear in the declared order I→II→III→IV then the score ({_order})")
    check(readme.index("## The score: what Γ has won") > readme.index("## Part IV — the seam"),
          "the score is the tally, so it comes after the argument, not before it")
    # §11/§12/§14/§15 lose their `## N.` numbers: a reader scrolling past
    # "## 11. Necessity" could not tell a step from a coda.
    for old in ("## 11. Necessity", "## 12. One God", "## 13. The Cremation",
                "## 14. What the Instrument", "## 15. What Is Not Established"):
        check(old not in readme, f"the old numbered section '{old[:28]}' is gone")
    # The 39-row table is the third presentation of facts Part I §8 and Part II
    # already derive, so it is a ledger surface (a cell cannot hold a deduction).
    check("## What Is Established of the Ground, and of the Person" not in readme,
          "the 39-row attribute table is not a third copy on the reading path")
    check("## What Is Established of the Ground, and of the Person" in ledger,
          "the 39-row attribute table reached the ledger instead of being dropped")
    check("### Step 1 — Objective Right and Wrong" not in readme, (
        "the deontic route must not be re-emitted on the reading path"))
    for led_sec in ["## The Deontic Route, in Full (the previous reading spine)",
                    "### 1. Objective Right and Wrong",
                    "### 10. Constructive Personal Ground",
                    "### The Deontic Route in One Map (the previous reading spine)",
                    "## Why Common Skeptical Attacks Fail (The Seven Pillars of Formal Defense)"]:
        check(led_sec in ledger, f"ledger carries {led_sec[:44]}")
    # The pillar count is derived from the rows, so the heading and the table can
    # never disagree again (they did: seven rows under a "Six" title).
    _pil = ledger.partition("Pillars of Formal Defense")[2].split("## ")[0]
    _n = len(re.findall(r"^\| \*\*\d+\. ", _pil, re.M))
    check(f"(The {['One','Two','Three','Four','Five','Six','Seven','Eight','Nine','Ten'][_n-1]} Pillars"
          in ledger, f"the pillar heading counts its own {_n} rows")
    # The thesis and the anti-tritheism line are the two sentences a reader must
    # not be able to miss.
    check("not three gods" in readme.lower(), "README must foreclose tritheism explicitly")
    check("one God in three Persons" in readme or "One God, in Three Persons" in readme,
          "README must state one God in three Persons")
    ten = re.findall(r"^\| \*\*(\d+)\*\*", readme.split("### The ten steps at a glance")[1].split("### Step 1")[0], re.M)
    check(sorted(int(t) for t in ten) == list(range(1, 11)),
          "ten-step table covers steps 1-10")

    # --- the ledger surface ---
    check(LEDGER.exists() and len(ledger.splitlines()) > 2000,
          f"ledger exists ({len(ledger.splitlines())} lines)")
    check(len(re.findall(r"^### .*?(?:chain, step by step|Chain \d+)", ledger, re.M)) == 14,
          "ledger carries all 14 chain blocks")
    # 40 -> >= 40 on 2026-09-30: the deontic route moved to the ledger rendered in
    # full (branches, supporting infrastructure, obstructions and per-step glosses),
    # so the ledger now carries strictly more derivations than the pre-split README.
    n_deriv = len(re.findall(r"^<summary>Formal Derivation", ledger, re.M))
    check(n_deriv >= 40, f"ledger carries all 40 natural-deduction blocks (got {n_deriv})")
    check("## Formal Frontiers" in ledger, "ledger carries the frontier list")
    check("## Which Classical Attributes Are Already Established?" in ledger,
          "ledger carries the full attributes table")
    check("## The Whole Argument in One Map" in ledger,
          "ledger carries the ASCII flowchart")

    # --- the union loses nothing (fast structural form; the full item-level
    #     form is scripts/ledger_superset.py against the snapshot) ---
    for name in ["the_person_supports_the_reality_of_right",
                 "indubitable_normative_free_will",
                 "epistemic_right_wrong_requires_a_free_being_for_which_meaning_can_mean",
                 "necessaryPersonalSubjectExists",
                 "ofGround_necessary_ground_of_reality"]:
        check(name in readme or name in ledger, f"union keeps {name[:50]}")

    # --- Part III: every dead branch is a DERIVATION, not a badge
    # (2026-09-30, CREMATION.md). A row that only says "PROVEN" asserts what the
    # reader cannot check; a row that prints the premises, the steps and the
    # terminator lets the reader check it. Both are required.
    cre = readme.partition("## Part III — The refutations")[2].partition("## Part IV")[0]
    check(cre, "README carries the refutations section")
    # DEDUCTION.md §6: all sixteen are titled `### R`-entries, so they are
    # findable and linkable. The three 🧱 boundaries used to be the only rows in
    # a table, because a table cell cannot hold a derivation — and a `{}`
    # countermodel has one. They are entries now, and the check is that *no*
    # branch is a table row any more.
    entries = re.findall(r"^### R(\d+)\. (.+)$", cre, re.M)
    check(len(entries) == 16, f"Part III promotes all sixteen branches to entries ({len(entries)})")
    check([int(n) for n, _ in entries] == list(range(1, 17)),
          "the R-entries are numbered 1..16 with no gap")
    _rows = [ln for ln in cre.splitlines() if ln.startswith("| **")]
    check(not _rows, f"no branch is a table row any more ({len(_rows)} left)")
    for _dead in _branches(("No right or wrong at all", "Voluntarism",
                            "Descriptivism (D3)", "Ungraspable command (D6)")):
        check(not any(_dead in ln for ln in _rows),
              f"the dead branch '{_dead}' is a derivation, not a table row")
    blocks = re.findall(r"^\*\*(?:\d+\. )?(.+?)\*\* — ", cre, re.M)
    check(len(blocks) >= 12, f"the refutations show every branch ({len(blocks)} found)")
    for term in ("⊥ CONTRADICTION", "⊘ DENIAL REFUTED", "COLLAPSE — INCOHERENT"):
        check(term in cre, f"the refutations derive a '{term}'")
    # The four kinds are all derived from the audited goal shape. The fourth is
    # the one that keeps R16 honest: the proof-self retorsion *identifies* the
    # critic as a person, it refutes nothing, so its kind says "not a death".
    check("🪞 INSTANTIATION — not a death" in cre,
          "the pillar retorsion is labelled an instantiation, not a collapse")
    for d in _branches(("Descriptivism (D3)", "(D4)", "(D5)", "(D6)")):
        check(d in cre, f"the refutations cover {d}")
    # §6: `KILLS BACK` is the step whose claim the branch makes impossible, and it
    # must be a real, linkable step — not a typed step number.
    kills = re.findall(r"^KILLS\s+\[step (\d+)\]\(#step-\1\)", cre, re.M)
    check(len(kills) >= 12, f"each refutation names the step it kills ({len(kills)} found)")
    for sid in re.findall(r"^KILLS\s+\[step (\d+)\]\(#step-(\d+)\)", cre, re.M):
        check(sid[0] == sid[1] and f'<a id="step-{sid[0]}"></a>' in readme,
              f"KILLS step {sid[0]} links an anchor that exists")
    # And the inverse: a step's own KILLS is derived from the refutations that
    # attack it, never transcribed (DEDUCTION.md §6). Split Part I on the step
    # anchors, then look inside each step's own segment — a regex across the whole
    # part with `.*?` and DOTALL spans steps and pairs a step with a later
    # step's KILLS, which is how an earlier version of this check found 4 instead
    # of 8.
    p1 = readme.partition("## Part I — The deduction")[2].partition("## Part II")[0]
    step_ids = re.findall(r'<a id="step-(\d+)"></a>', p1)
    step_kills = {}
    for i, sid in enumerate(step_ids):
        seg = p1.split(f'<a id="step-{sid}"></a>', 1)[1].partition(
            f'<a id="step-{step_ids[i + 1]}"></a>' if i + 1 < len(step_ids) else "\0")[0]
        k = re.search(r"^KILLS\s+(.*\S)$", seg, re.M)
        if k:
            step_kills[sid] = k.group(1)
    check(len(step_kills) >= 8,
          f"the steps carry the refutations that attack them ({len(step_kills)} of "
          f"{len(step_ids)} steps; steps 7 and 10 have none, which is honest)")
    for sid, ref in step_kills.items():
        for tgt in re.findall(r"\(#(r\d+)\)", ref):
            check(f'<a id="{tgt}"></a>' in cre,
                  f"step {sid}'s KILLS {tgt} points at an entry that exists")
    # Each entry, split on its own `### R` heading: a Lean anchor, a price line,
    # and a terminator. The price line must never pair a ✅ with a substantive
    # axiom (the V2 invariant, in prose). Splitting on the `**…** — ` label
    # instead would start each chunk at the *objection* line and read the wrong
    # segment, which is how this check passed for years without testing a block.
    entries_txt = {}
    for mm in re.finditer(r"^### R(\d+)\. .+$", cre, re.M):
        entries_txt[int(mm.group(1))] = cre[mm.end():]
    keys = sorted(entries_txt)
    # Truncate each entry at the *next entry's* heading. The last entry runs to
    # the end of Part III, and using a sentinel that is not a NUL would silently
    # leave it holding the whole tail of the section.
    for i, n in enumerate(keys):
        entries_txt[n] = entries_txt[n].partition(
            f"### R{keys[i + 1]}. " if i + 1 < len(keys) else "\x00")[0]
    # 🧱 boundaries invalidate nothing, so their blocks print no KILLS at all.
    # The set of boundary rows is *read from the spine JSON* rather than written
    # here. It used to be the literal `(13, 14, 15)`, which silently became a
    # second, frozen copy of the role table: when CLEARER.md §8 reclassified R15
    # as a priced result the generator was right and this check was wrong, and
    # the failure it reported was the opposite of the truth. A test that restates
    # a table in the generator is a test that will eventually defend the old table.
    spine = json.loads((ROOT / "formal" / "presentation_spine.json").read_text(
        encoding="utf-8"))
    crem_rows = next(s for s in spine["reading_sections"] if s.get("cremation"))[
        "cremation"]
    non_killing = [i for i, r in enumerate(crem_rows, 1)
                   if r.get("role", "derivation") in ("boundary", "pillar")]
    check(non_killing, f"the spine declares at least one non-killing row: {non_killing}")
    for n in non_killing:
        _blk = entries_txt[n]
        _lab = "BOUNDARY" if crem_rows[n - 1].get("role") == "boundary" else "PILLAR"
        check(_lab in _blk and "KILLS" not in _blk,
              f"R{n} is a {_lab.lower()} and claims no kill")
    # The converse, so the loop above cannot pass vacuously: a 💥 row may kill,
    # and at least one must — otherwise nothing in Part III is a death and the
    # whole "nihilism is cremated" claim is unsupported.
    killing = [i for i, r in enumerate(crem_rows, 1)
               if r.get("role", "derivation") == "derivation"]
    check(any("KILLS" in entries_txt[n] for n in killing),
          f"at least one 💥 derivation claims a kill (of R{killing[:6]}…)")
    # The Seven Pillars are an index onto these entries, derived from the rows'
    # own `pillars` field — not a seventh section with its own claims.
    check("| Pillar of the Seven | Where it is answered |" in cre,
          "Part III indexes the Seven Pillars onto the R-entries")
    for pid in range(1, 8):
        # The icon leads the link, and it is the *R-entry's* kind — the pillar's
        # authored name carries none. Resolving both the R-number and the glyph
        # from the spine, rather than widening the old regex to `[💥🧱🪞]`, is
        # what makes this an assertion instead of a tolerance: a renderer that
        # dropped the icon, or attached the wrong role's, now fails.
        hits = [i for i, r in enumerate(crem_rows, 1) if pid in r.get("pillars", [])]
        check(len(hits) == 1,
              f"pillar {pid} of the Seven is placed on exactly one R-entry")
        if len(hits) != 1:
            continue
        icon = bd._REFTABLE[crem_rows[hits[0] - 1].get("role", "derivation")][0]
        check(re.search(rf"^\| {pid}\. .*\| {icon} \[R\d+ .*\]\(#r\d+\) \|$", cre,
                        re.M) is not None,
              f"pillar {pid} of the Seven is placed on an R-entry marked {icon}")
    for n, blk in entries_txt.items():
        head = re.search(r"^\*\*(.+?)\*\* — ", blk, re.M)
        head = head.group(1) if head else f"R{n}"
        check("lean#L" in blk, f"R{n} ({head[:30]}) links its Lean declaration")
        check("substantive axio" in blk, f"R{n} ({head[:30]}) states its price")
        check("PROOF" in blk or "countermodel **bounds**" in blk,
              f"R{n} ({head[:30]}) shows a derivation or says it is a bound")
    for line in cre.splitlines():
        if line.startswith("> ✅"):
            check("— 0 substantive axioms ·" in line,
                  "a ✅ price line must claim zero substantive axioms: " + line[:70])
    # A priced route is shown priced: the stipulative branch's second derivation
    # rests on AxJudicativeBipolarity and must say so, not borrow a ✅.
    check("⚠️ **AXIOMATIC (AxJudicativeBipolarity)**" in cre,
          "the priced second route to the stipulative death is disclosed as priced")
    check("A second, independently sufficient refutation" in cre,
          "the priced route explains why the free route is the one read")

    # --- reading-path vocabulary is Γ's, not a countermodel's (2026-09-30) ---
    #
    # A `▸` row in a "Vocabulary" block states what a symbol means *in this
    # theory*. Step 9 was printing `M ≡ Unit Content := Bool …` and
    # `Means ≡ True` from `EpistemicPersonalGround` and `M_amoral` — a
    # countermodel's separating model and a hostile model of moral amoralism,
    # wearing the vocabulary block's authority. That is the C559 category error
    # (AGENTS.md: "Signature models are not candidate states").
    #
    # Checked here rather than in `_lint_readme` because this test resolves the
    # *declaration*, not the link: `M_amoral` is a namespace inside
    # `MoralFrontierAudit.lean`, so a `[file#name]` link cannot see it. The
    # rendered-text lint catches the top-level countermodel files; this catches
    # the nested ones.
    glossary_start = readme.find("### The shared vocabulary of the ten steps")
    check(glossary_start != -1,
          "Part I opens with the shared-vocabulary block (DEDUCTION.md D3/D7)")
    if glossary_start != -1:
        # bounded at the next `###`: Part II's component sub-blocks also open
        # with `▸`, and they are components, not vocabulary.
        rest = readme[glossary_start:]
        nxt = rest.find("\n### ", 1)
        glossary = rest if nxt == -1 else rest[:nxt]

        decls = bd.parse_lean_sources()
        # every full name that lives in <file> and is called <name>
        by_file_name: dict[tuple[str, str], list[str]] = {}
        for full, info in decls.items():
            by_file_name.setdefault((info.get("file", ""), info.get("name", "")),
                                    []).append(full)
        # the `▸` row and its `∴`/`📘` continuation lines, up to the next `▸`
        rows, cur = [], None
        for ln in glossary.splitlines():
            if ln.strip().startswith("▸"):
                if cur:
                    rows.append(cur)
                cur = [ln]
            elif cur is not None and ln.strip() == "":
                rows.append(cur)
                cur = None
            elif cur is not None:
                cur.append(ln)
        if cur:
            rows.append(cur)
        check(len(rows) >= 5,
              f"the shared vocabulary defines a real set of symbols (got {len(rows)} rows)")
        for row in rows:
            head = row[0].strip()
            src = " ".join(row)
            m = re.search(r"📘 \[([A-Za-z0-9_]+\.lean)#([A-Za-z0-9_']+)\]", src)
            check(m is not None, f"vocabulary row '{head[:40]}' carries its Lean anchor (B5)")
            if not m:
                continue
            fulls = by_file_name.get((m.group(1), m.group(2)), [])
            check(bool(fulls), f"vocabulary anchor {m.group(1)}#{m.group(2)} resolves to a declaration")
            for full in fulls:
                check(not bd.is_countermodel_declaration(full),
                      f"vocabulary row '{head[:40]}' must not gloss a countermodel "
                      f"declaration, and {full} is one (AGENTS.md C559)")
            # the row's `∴` is an equation only when the declaration fixes one
            kind = decls[fulls[0]].get("kind") if fulls else ""
            has_eq = "∴" in src
            check(not (has_eq and kind in ("axiom", "structure", "inductive", "class")),
                  f"vocabulary row '{head[:40]}' ({kind}) must not print an equation: "
                  f"a {kind} fixes none")

    # Item 4: No doubled markers in rendered markdown
    check("◆ AXIOM **◆ AXIOM**" not in readme, "no doubled marker ◆ AXIOM **◆ AXIOM** in README.md")
    check("◆ AXIOM **◆ AXIOM**" not in ledger, "no doubled marker ◆ AXIOM **◆ AXIOM** in ledger.md")
    check(not re.search(r"[◆✅⚠️🧱📘⏸❌]\s+[A-Z_]+\s+\*\*[◆✅⚠️🧱📘⏸❌]\s+[A-Z_]+\*\*", readme),
          "no doubled marker pattern in README.md")
    check(not re.search(r"[◆✅⚠️🧱📘⏸❌]\s+[A-Z_]+\s+\*\*[◆✅⚠️🧱📘⏸❌]\s+[A-Z_]+\*\*", ledger),
          "no doubled marker pattern in ledger.md")

    # Item 5: Block anchor and block SOURCE agree
    block_matches = re.findall(
        r"<a id=\"([A-Za-z0-9_]+)\"></a>\s*\n\s*▸[^\n]+\n(?:[^\n]+\n)*?\s*SOURCE\s+[^\n]*?\[[A-Za-z0-9_.]+#([A-Za-z0-9_\x27]+)\]",
        readme)
    check(len(block_matches) >= 10, f"expected at least 10 anchored component blocks in README.md, got {len(block_matches)}")
    for anchor, src in block_matches:
        check(anchor == src, f"block anchor <a id=\"{anchor}\"> does not match block SOURCE declaration {src}")
    check('<a id="asietic_summary"></a>' in readme,
          "alias anchor #asietic_summary must be rendered in README.md (RULE_R_CORRECTION_PLAN.md §7.4)")

    # Item 12 (RULE_R_CORRECTION_PLAN.md §6): Natural deduction trace constructor rendering
    # No rendered step may be a bare proof-term subterm (reject ^\d+\.\s+(s|p|q|rfl)$ and
    # any step containing ⟨ or ⟩ in constructor traces), and each step must correspond to a
    # recorded ProofIR step kind.
    asiety_block_m = re.search(
        r'<a id="weakChoice_implies_asiety"></a>.*?(?=<a id=|\Z)',
        readme, re.DOTALL)
    check(bool(asiety_block_m), "weakChoice_implies_asiety block missing from README.md")
    if asiety_block_m:
        asiety_block = asiety_block_m.group(0)
        asiety_steps = re.findall(r"^\s*(\d+\.\s*.*)", asiety_block, re.MULTILINE)
        check(len(asiety_steps) > 0, "no rendered steps found in weakChoice_implies_asiety block")
        for step in asiety_steps:
            check(not re.search(r"^\d+\.\s*(s|p|q|rfl)\b", step.strip()),
                  f"bare proof-term subterm found in weakChoice_implies_asiety: {step}")
            check("⟨" not in step and "⟩" not in step,
                  f"unresolved constructor bracket found in weakChoice_implies_asiety: {step}")

    # Globally across rendered surfaces: no unbalanced brackets, and no bare subterm component witnesses
    for fname, text in [("README.md", readme), ("ledger.md", ledger)]:
        for ln in text.splitlines():
            m = re.match(r"^\s*\d+\.\s*(.*)", ln)
            if m:
                step = m.group(1)
                check(step.count("⟨") == step.count("⟩"), f"balanced ⟨/⟩ in step ({fname}): {step[:60]}")
                check(not re.search(r"component witness \d+:\s*(s|p|q|rfl)$", step.strip()),
                      f"no bare component witness in step ({fname}): {step[:60]}")

    # Item 13 (RULE_R_CORRECTION_PLAN.md §7.2, §7.3): test_badges_match_selection & census reconciliation
    census_path = ROOT / "formal" / "badge_census.json"
    if census_path.exists():
        census = json.loads(census_path.read_text(encoding="utf-8"))
        for s in census.get("slots", []):
            slot_id = s["id"]
            verdict = s["verdict"]

            # Census reconciliation: considered >= sum(rejected)
            rej = s.get("routes_rejected", {})
            check(s["routes_considered"] >= sum(rej.values()),
                  f"census slot {slot_id} routes_considered >= sum(rejected)")

            if s["surface"] == "classical_attributes":
                pattern = rf"^\|\s*\*\*{re.escape(slot_id)}[^*]*\*\*[^\n]*"
                m = re.search(pattern, ledger, re.MULTILINE)
                check(bool(m), f"classical attribute {slot_id} found in ledger.md")
                if m:
                    cells = [c.strip() for c in m.group(0).split("|")]
                    status_cell = cells[3] if len(cells) > 3 else ""
                    if verdict == "PROVEN":
                        check("PROVEN" in status_cell, f"{slot_id} status cell verified as PROVEN")
                    elif verdict == "AXIOMATIC":
                        check("AXIOMATIC" in status_cell, f"{slot_id} status cell verified as AXIOMATIC")
                    elif verdict == "COUNTERMODEL":
                        check("COUNTERMODEL" in status_cell or "INDEPENDENT" in status_cell,
                              f"{slot_id} status cell verified as COUNTERMODEL")
                    elif verdict == "DEFINITIONAL":
                        check("DEFINITIONAL" in status_cell, f"{slot_id} status cell verified as DEFINITIONAL")
                    elif verdict == "AXIOM":
                        check("AXIOM" in status_cell, f"{slot_id} status cell verified as AXIOM")
                    elif verdict in ("ABSENT", "NOT ESTABLISHED"):
                        check("NOT ESTABLISHED" in status_cell or "ABSENT" in status_cell,
                              f"{slot_id} status cell verified as NOT ESTABLISHED")
                    elif verdict == "DEFERRED":
                        check("DEFERRED" in status_cell, f"{slot_id} status cell verified as DEFERRED")
            elif s["surface"] == "characteristic_sections":
                winner_short = s["winner"].rsplit(".", 1)[-1]
                check(winner_short in readme, f"characteristic slot winner {winner_short} found in README")
                check(s["rendered_badge"] in readme or s["rendered_badge"] in ledger,
                      f"characteristic slot {slot_id} rendered_badge verified on surface")
            elif s["surface"] == "seven_pillars":
                num = slot_id.split("_")[1]
                check(f"**{num}." in ledger, f"pillar {num} found in ledger")
                check(s["rendered_badge"] in ledger, f"pillar {num} rendered_badge verified in ledger")

    if errors:
        print(f"\nFAIL: {len(errors)} argument-surface regression(s)")
        return 1
    print("\nOK: two-tier contract holds (argument ~490 lines, ledger complete).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
