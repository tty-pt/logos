#!/usr/bin/env python3
"""Gate the axiom census itself.

`scripts/check_consistency.py` pins the number of declared axioms so that deleting one cannot
silently lower every price in the corpus. That protection is only as good as the parser behind
it, and on 2026-10-03 the parser was counting prose.

`Logos/AsieticChoice.lean:19` reads `axiom of Γ**:` -- a markdown emphasis inside the module's
`/- -/` comment -- and the anchored `^axiom` regex matched it as an axiom named `of`, tagged SEM
by inheritance from the surrounding docstring. The census read 40 when the kernel holds 39, and
`AGENTS.md` recorded "18 VOCAB / 7 SEM / 13 META / 2 TRANS" when the truth is 18 / 6 / 13 / 2.

The failure mode is not the wrong number, it is that a *count* cannot see a phantom. Worse, it
was a laundering vector in the exact edit the pin exists to catch: delete a real axiom, add any
comment line beginning `axiom `, and the total holds steady while every price in the corpus
silently drops.

So these assertions are about the parser, not about the corpus. Every claim made about the
census in a docstring, a plan, or a review must be asserted here rather than read off a number.
Run: python3 scripts/test_axiom_census.py
"""
from __future__ import annotations

import collections
import importlib.util
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"
LOGOS = FORMAL / "Logos"


def load_gate():
    spec = importlib.util.spec_from_file_location(
        "check_consistency", ROOT / "scripts" / "check_consistency.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_builder():
    sys.path.insert(0, str(ROOT / "scripts"))
    import build_deduction
    return build_deduction


CC = load_gate()
FAILURES: list[str] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    if ok:
        print(f"  ok   {label}")
    else:
        print(f"  FAIL {label} :: {detail}")
        FAILURES.append(label)


def write(tmp: Path, name: str, body: str) -> Path:
    p = tmp / name
    p.write_text(body)
    return p


def main() -> int:
    import tempfile

    print("axiom census: parser must not read comments")
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)

        # The exact shape that shipped the bug: a module comment quoting an axiom statement.
        phantom = write(
            tmp,
            "Phantom.lean",
            "/-\n"
            "# Logos.Phantom -- a module comment\n"
            "\n"
            "The line below is prose, not a declaration:\n"
            "\n"
            "axiom of \u0393**:\n"
            "\n"
            "    \u2200 (s : Subject), p\n"
            "-/\n"
            "theorem t : True := trivial\n",
        )
        check(
            "comment line `axiom of ...` is not an axiom",
            CC.axiom_statements(phantom) == [],
            f"got {CC.axiom_statements(phantom)}",
        )

        # A docstring is a comment too, and the corpus quotes statements in docstrings.
        doc_quote = write(
            tmp,
            "DocQuote.lean",
            "/-- Tag: SEM\n"
            "See `Logos.RetorsiveNormativity.AxJudicativeBipolarity`, which is **already an\n"
            "axiom of \u0393**:\n"
            "-/\n"
            "theorem t : True := trivial\n",
        )
        check(
            "docstring line `axiom of ...` is not an axiom",
            CC.axiom_statements(doc_quote) == [],
            f"got {CC.axiom_statements(doc_quote)}",
        )

        # A line comment.
        line_comment = write(
            tmp,
            "LineComment.lean",
            "-- axiom sneaky : True\n"
            "theorem t : True := trivial\n",
        )
        check(
            "line comment `-- axiom ...` is not an axiom",
            CC.axiom_statements(line_comment) == [],
            f"got {CC.axiom_statements(line_comment)}",
        )

        # The laundering vector, stated directly: equal counts, different content.
        real = write(
            tmp,
            "Real.lean",
            "/-- Tag: VOCAB -/\naxiom OnlyOne : \u2200 x : Nat, x = x\n",
        )
        check(
            "one real axiom is one axiom",
            [n for n, _, _ in CC.axiom_statements(real)] == ["OnlyOne"],
            f"got {CC.axiom_statements(real)}",
        )

        nested = write(
            tmp,
            "Nested.lean",
            "/- outer /- inner -/\n"
            "axiom buried : True\n"
            "-/ still outer -/\n"
            "axiom surfaced : True\n",
        )
        check(
            "nested block comments are tracked",
            [n for n, _, _ in CC.axiom_statements(nested)] == ["surfaced"],
            f"got {CC.axiom_statements(nested)}",
        )

        stringy = write(
            tmp,
            "Stringy.lean",
            'theorem t : String := "axiom notReal : True"\n',
        )
        check(
            "`--` inside a string literal is not a comment",
            CC.axiom_statements(stringy) == [],
            f"got {CC.axiom_statements(stringy)}",
        )

    print("\naxiom census: three sources must agree")
    counted = []
    for path in sorted(LOGOS.glob("*.lean")):
        for name, _statement, line in CC.axiom_statements(path):
            counted.append((name, path, line))
    gate_count = len(counted)
    check(
        "gate parser == EXPECTED_AXIOM_STATEMENTS",
        gate_count == CC.EXPECTED_AXIOM_STATEMENTS,
        f"gate {gate_count} != pin {CC.EXPECTED_AXIOM_STATEMENTS}",
    )

    # `depgraph.json` is produced by a real Lean parser, so it is the independent arbiter.
    dep = json.loads((FORMAL / "depgraph.json").read_text())
    nodes = dep["nodes"] if isinstance(dep, dict) and "nodes" in dep else dep
    dep_axioms = [n for n in nodes if n.get("kind") == "axiom"]
    check(
        "depgraph axiom nodes == gate count",
        len(dep_axioms) == gate_count,
        f"depgraph {len(dep_axioms)} != gate {gate_count}",
    )

    names = {n for n, _, _ in counted}
    dep_names = {n.get("name", "").split(".")[-1] for n in dep_axioms}
    missing = sorted(n for n in dep_names if n and n not in names)
    check(
        "no axiom in depgraph is invisible to the parser",
        not missing,
        f"invisible: {missing}",
    )

    tags = collections.Counter()
    for name, path, line in counted:
        tags[CC.axiom_tag(path, line - 1)] += 1
    census = dict(sorted(tags.items(), key=lambda kv: str(kv[0])))
    check(
        "every axiom carries a valid Tag",
        set(census) == set(CC.VALID_TAGS),
        f"census {census} outside {CC.VALID_TAGS}",
    )
    expected = {"VOCAB": 18, "SEM": 6, "META": 13, "TRANS": 3}
    check(
        f"tag census == {expected}",
        census == expected,
        f"got {census}",
    )

    print()
    print("D7: the declaration scanner must not read comments either")
    BD = load_builder()
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)

        def scan(name: str, body: str) -> dict:
            """parse_lean_sources over a one-module directory."""
            d = tmp / name
            d.mkdir()
            write(d, f"{name}.lean", body)
            saved, BD.LEAN_DIR = BD.LEAN_DIR, d
            try:
                return BD.parse_lean_sources()
            finally:
                BD.LEAN_DIR = saved

        def axiom_names(parsed: dict) -> list[str]:
            return [k.split(".")[-1] for k, v in parsed.items() if v.get("kind") == "axiom"]

        # The shipped D7 repro, verbatim in shape: a retirement note quoting the withdrawn
        # declaration, with the keyword at the start of an indented line inside a block comment.
        # `build_deduction.parse_lean_sources` used a *per-line* `strip_block_comments`, which
        # cannot see that a line is the middle of a multi-line `/- -/` block, so this came back as
        # a live axiom with an empty tag -- and `gapmap_taxonomy.py` printed `40 total / 39 tagged`
        # while the kernel held 39. The census pin could not see it: `axiom_statements` had been
        # hardened on 2026-10-03 and this parser had not. Same laundering, one layer over.
        retirement = scan(
            "Retirement",
            "/- RETIRED. The declaration below was DELETED, not re-tagged:\n"
            "\n"
            "    axiom AxWithdrawn :\n"
            "        ∀ x : Nat, x = x\n"
            "\n"
            "  Replaced by something else. -/\n"
            "/-- Tag: VOCAB -/\naxiom AxLive : ∀ x : Nat, x = x\n",
        )
        check(
            "a quoted axiom inside a block comment is not a declaration",
            axiom_names(retirement) == ["AxLive"],
            f"got {axiom_names(retirement)}",
        )

        nested_quote = scan(
            "Nested",
            "/- outer /- inner -/\n"
            "    axiom AxBuried : True\n"
            "-/ still outer -/\n"
            "/-- Tag: VOCAB -/\naxiom AxLive : ∀ x : Nat, x = x\n",
        )
        check(
            "a quoted axiom inside a *nested* block comment is not a declaration",
            axiom_names(nested_quote) == ["AxLive"],
            f"got {axiom_names(nested_quote)}",
        )

        docstring_quote = scan(
            "DocQuote",
            "/-- Tag: SEM\n"
            "See `Axioms.AxJudicativeBipolarity`, which is already an\n"
            "axiom of Γ:\n"
            "-/\naxiom AxLive : ∀ x : Nat, x = x\n",
        )
        check(
            "a quoted axiom inside a docstring is not a declaration",
            axiom_names(docstring_quote) == ["AxLive"],
            f"got {axiom_names(docstring_quote)}",
        )

        line_quote = scan(
            "LineQuote",
            "-- axiom AxSneaky : True\n"
            "axiom AxLive : ∀ x : Nat, x = x\n",
        )
        check(
            "a quoted axiom on a line-comment is not a declaration",
            axiom_names(line_quote) == ["AxLive"],
            f"got {axiom_names(line_quote)}",
        )

        # A comment must not *hide* real code either: the projection is per-line code, so an
        # inline `/- note -/` before a declaration leaves the declaration visible.
        inline = scan(
            "Inline",
            "/- the next line is code, despite the leading comment -/ axiom AxLive : ∀ x : Nat, x = x\n",
        )
        check(
            "an inline comment does not hide the declaration after it",
            axiom_names(inline) == ["AxLive"],
            f"got {axiom_names(inline)}",
        )

    # The assertion that would have caught it on the real tree: the declaration scanner that
    # feeds GAPMAP, the spine, the chain steps and the badges must report exactly the same
    # axioms as the census gate and as depgraph.json. A phantom breaks this even when every
    # count still balances, because the phantom is in the *name set*.
    printed = {k.split(".")[-1]: v for k, v in BD.parse_lean_sources().items() if v.get("kind") == "axiom"}
    printed_names = set(printed)
    loc_of = {n: (p, l - 1) for n, p, l in counted}
    check(
        "declaration scanner sees exactly EXPECTED_AXIOM_STATEMENTS axioms",
        len(printed_names) == CC.EXPECTED_AXIOM_STATEMENTS,
        f"scanner {len(printed_names)} != pin {CC.EXPECTED_AXIOM_STATEMENTS}",
    )
    check(
        "declaration scanner and census gate agree on axiom NAMES",
        printed_names == names,
        f"scanner-only {sorted(printed_names - names)}, gate-only {sorted(names - printed_names)}",
    )
    check(
        "declaration scanner and depgraph agree on axiom NAMES",
        printed_names == {n for n in dep_names if n},
        f"scanner-only {sorted(printed_names - dep_names)}, depgraph-only {sorted(n for n in dep_names if n and n not in printed_names)}",
    )
    untagged = sorted(n for n in printed_names if CC.axiom_tag(*loc_of[n]) is None)
    check(
        "every axiom the declaration scanner sees carries a Tag",
        not untagged,
        f"untagged: {untagged}",
    )

    print()
    print("D9: every `Tag:` reader must agree with the census, TAG BY TAG")
    # `check_consistency.axiom_tag` is the census reader and is authoritative. Three other scripts
    # read the same tags independently: `build_deduction._tag_for` (an anchored whole-line regex
    # over the extracted docstring), `audit_stipulated_defs.axiom_tags`, and
    # `test_personal_ground_kind.axiom_tags`. Independence is what makes the cross-check worth
    # anything -- if they all called one helper, comparing them would prove nothing.
    #
    # On 2026-10-04 the last of these disagreed with the census on 3 of the 39 axioms while all
    # four counted 39 in total. It took whichever tag token appeared first in the order
    # (VOCAB, SEM, META, TRANS) on the nearest `Tag:`-bearing line above the declaration, so a
    # docstring's PROSE about a different tag beat the real opener: `ThomisticAct.lean:111` reads
    # "`Tag: META`: it connects two relations, so `VOCAB`'s 'asserts no connection' rule excludes
    # it", and that `VOCAB` mention made `love_implies_act` read VOCAB. The reimplementation is
    # deleted; this assertion is why the next one cannot be written.
    #
    # The damage was never the count. That map is what `substantive_in` uses to decide which
    # footprints count as priced, so `ThomisticAct.loving_subject_initiates` -- PROVEN↑ at one
    # META, via `love_implies_act` -- was certified FREE, and twelve declarations resting on the
    # VOCAB classifier `DivineSubjectRole` were read as paid. A gate that mislabels which rows
    # are free is worse than no gate.
    #
    # So compare the name -> tag MAPS. Four readers agreeing on 39 is not evidence; four readers
    # agreeing on 39 *assignments* is.
    census_map = {n: CC.axiom_tag(p, l) for n, p, l in counted}
    readers: dict[str, dict[str, str | None]] = {
        "build_deduction": {
            k.rsplit(".", 1)[-1]: (v.get("tag") or None)
            for k, v in BD.parse_lean_sources().items() if v.get("kind") == "axiom"
        },
    }
    for modname in ("audit_stipulated_defs", "test_personal_ground_kind"):
        spec = importlib.util.spec_from_file_location(
            modname, ROOT / "scripts" / f"{modname}.py"
        )
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        readers[modname] = {k.rsplit(".", 1)[-1]: v for k, v in module.axiom_tags().items()}
    spec = importlib.util.spec_from_file_location(
        "test_finitude_bound_scope", ROOT / "scripts" / "test_finitude_bound_scope.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    readers["test_finitude_bound_scope"] = {
        k.rsplit(".", 1)[-1]: v for k, v in module.declared_tags().items()
    }
    for reader, got in readers.items():
        diff = {
            n: (census_map.get(n), got.get(n))
            for n in sorted(set(census_map) | set(got))
            if census_map.get(n) != got.get(n)
        }
        check(
            f"{reader} agrees with the census on every axiom's Tag",
            not diff,
            f"{len(diff)} disagreement(s), first few: {sorted(diff.items())[:4]}",
        )

    # Risk 6 (LOVE-3.md §6), machine-checked. `axiom_statements` returns a 1-based line and
    # `axiom_tag` indexes a 0-based list, so callers disagree by one: `gate_b_syntactic_scan`
    # passes `line`, `test_axiom_census` and `ledger_superset` pass `line - 1`. That has been
    # harmless only because every axiom's docstring opener sits at least two lines above it, and
    # a docstring written on ONE line (`/--Tag: VOCAB -/` immediately above `axiom`) makes the
    # two conventions return different tags -- silently, for whichever caller is wrong. Assert the
    # answer is insensitive to the convention, so the off-by-one can never become load-bearing.
    convention_sensitive = sorted(
        n for n, p, l in counted if CC.axiom_tag(p, l) != CC.axiom_tag(p, l - 1)
    )
    check(
        "no axiom's Tag depends on the caller's line convention (LOVE-3 Risk 6)",
        not convention_sensitive,
        f"one-line docstring, so `line` and `line - 1` disagree: {convention_sensitive}",
    )

    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} assertion(s): {FAILURES}")
        return 1
    print(
        f"axiom census OK: {gate_count} declared axioms, {expected} "
        f"(= {sum(expected.values())}) -- agrees with depgraph.json"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
