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
    expected = {"VOCAB": 18, "SEM": 6, "META": 13, "TRANS": 2}
    check(
        f"tag census == {expected}",
        census == expected,
        f"got {census}",
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
