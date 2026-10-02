#!/usr/bin/env python3
"""Gate: prices written into the generator's own prose must not go stale.

`build_deduction.py` derives every BADGE from `formal/axiom_audit.json`. That
guarantee does not extend to the hand-written `sense` / gloss prose in the same
row: S5 re-tagged the uniqueness bound from `SemanticFinitude` (VOCAB) to
`GroundTranscendence` (META), every derived badge moved correctly, and the
sentence beside them still said "VOCAB" in the reader surface. Nothing failed.

This gate closes that class. It reads the authoritative census, collects the
axioms actually tagged VOCAB / SEM / META / TRANS, and rejects any generator
string that attributes a Tag to an axiom which does not carry it. It is
deliberately narrow: it checks Tag-attribution claims, not prose quality.

Run: python3 scripts/test_generator_price_prose.py
"""
import json
import pathlib
import re
import sys

AUDIT = "formal/axiom_audit.json"
# Every place a price can be written by hand. The S5 staleness lived in THREE of
# them at once (build_deduction.py prose, presentation_spine.json gloss, and
# author_reading_path_prose.py), so gating one file would have missed it twice.
SOURCES = [
    "scripts/build_deduction.py",
    "scripts/author_reading_path_prose.py",
    "formal/presentation_spine.json",
    "AGENTS.md",
]

# An axiom name paired with a tag, in either order. Deliberately requires the
# tag to sit inside backticks or bold so we match deliberate attribution claims
# and not incidental prose.
NAME = r"[A-Za-z_][A-Za-z0-9_.]*"
TAGS = ("VOCAB", "SEM", "META", "TRANS")


def declared_tags():
    """Axiom short-name -> tag, from the Lean sources via the gate's own census."""
    ns = {"__file__": "scripts/check_consistency.py", "__name__": "census"}
    exec(compile(open("scripts/check_consistency.py").read(), "check_consistency.py", "exec"), ns)
    out = {}
    for path in sorted(pathlib.Path("formal/Logos").glob("*.lean")):
        for name, _stmt, line in ns["axiom_statements"](path):
            out[name.split(".")[-1]] = ns["axiom_tag"](path, line)
    return out


def main() -> int:
    audit = json.load(open(AUDIT))
    assert isinstance(audit, dict) and audit, f"{AUDIT} must be a non-empty name->axioms map"

    tags = declared_tags()
    assert tags, "census found no axioms; the parser is broken, not the corpus"
    bad = []

    for src in SOURCES:
        text = open(src).read()
        # Attribution must be INSIDE THE SAME PARENTHETICAL as the name. A loose
        # "tag within N chars of name" window produced three false positives on
        # correct prose: `` `Ground` (VOCAB), `AxTwoSubjects` (META) `` matched the
        # VOCAB against AxTwoSubjects, and ``footprint `{Means, Subject}` - VOCAB
        # only`` matched the footprint's *set member* `Subject`. Both are accurate
        # sentences about different axioms.
        for m in re.finditer(r"`([A-Za-z_][A-Za-z0-9_']*)`\s*\(([^()]{0,60}?)\b(VOCAB|SEM|META|TRANS)\b", text):
            name, tag = m.group(1), m.group(3)
            if name in tags and tags[name] != tag:
                bad.append(f"{src}: `{name}` called {tag}, census says {tags[name]}")

    census = {}
    for t in tags.values():
        census[t] = census.get(t, 0) + 1
    print(f"census from Lean sources: {len(tags)} axioms, {census}")
    print(f"scanned {len(SOURCES)} prose source(s) for stale Tag attributions")

    if bad:
        print("\nSTALE PRICE PROSE — a Tag is attributed to the wrong axiom:")
        for b in sorted(set(bad)):
            print(f"  {b}")
        print("\nBadges are derived; this prose is not. Fix the sentence.")
        return 1
    print("\nOK: no generator prose attributes a Tag an axiom does not carry.")
    return 0


if __name__ == "__main__":
    sys.exit(main())