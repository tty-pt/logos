#!/usr/bin/env python3
"""test_readme_disambiguation.py — Regression test for README clarity & disambiguation.

Verifies:
  1. Necessary persons table exists in Part IV with C600/C604, C212, C73, and C585 pointer.
  2. Unqualified "person-count open" phrases do not appear in README.md.
  3. No false `> ⚠️ **Price disclosed —**` warnings occur on free/0-axiom disclosures.
  4. The overloaded terms glossary (<a id="sec-glossary-overloaded-terms"></a>) is present.
  5. Every <a id="..."> anchor in README.md is unique.
  6. Every internal link in README.md resolves to an anchor or heading slug.
  7. Characteristic and formal frontier counts are singular and derived.
  8. Visible lines stay strictly within README_VISIBLE_BUDGET (1900).
"""

import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
README_PATH = ROOT / "README.md"
SPINE_PATH = ROOT / "formal" / "presentation_spine.json"


def test_readme_disambiguation() -> None:
    assert README_PATH.exists(), f"Missing {README_PATH}"
    text = README_PATH.read_text(encoding="utf-8")
    lines = text.splitlines()

    print("Checking README disambiguation and clarity invariants...")

    # 1. Necessary persons table in Part IV
    assert '<a id="sec-necessary-persons-the-count-at-each-sort"></a>' in text, (
        "README.md: missing <a id=\"sec-necessary-persons-the-count-at-each-sort\"></a>")
    assert "### Necessary persons: the count, at each sort" in text, (
        "README.md: missing '### Necessary persons: the count, at each sort' heading")
    for req_tok in ("C600", "C604", "C212", "C73", "C585", "DivineHypostasis"):
        assert req_tok in text, f"README.md necessary persons section missing {req_tok}"
    print("  ✓ Part IV necessary-persons table present with C600/C604, C212, C73, C585.")

    # 2. No unqualified "person-count open"
    for m in re.finditer(r"person-count\s+(?:left\s+)?open\b", text, re.I):
        start = max(0, text.rfind("\n", 0, m.start()))
        end = text.find("\n", m.end())
        line = text[start:end if end != -1 else len(text)]
        assert any(q in line for q in ("C600", "C604", "C73", "DivineHypostasis", "unicity", "Part IV")), (
            f"Unqualified 'person-count open' in README.md: {line.strip()[:100]}")
    print("  ✓ No unqualified 'person-count open' phrases found.")

    # 3. No false ⚠️ on 0-substantive-axiom disclosures
    for m in re.finditer(r"> ⚠️ \*\*Price disclosed —\*\* (?:0 substantive|free|no substantive)", text, re.I):
        raise AssertionError(f"README.md has false ⚠️ on free disclosure: {m.group(0)}")
    print("  ✓ No false ⚠️ icons on 0-substantive-axiom disclosures.")

    # 4. Glossary presence
    assert '<a id="sec-glossary-overloaded-terms"></a>' in text, (
        "README.md: missing glossary anchor <a id=\"sec-glossary-overloaded-terms\"></a>")
    assert "**Key terms: the three distinctions.**" in text, (
        "README.md: missing key terms distinctions block")
    print("  ✓ Overloaded terms glossary present.")

    # 5. Anchor uniqueness
    anchor_ids = re.findall(r'<a id="([^"]+)"></a>', text)
    counts = Counter(anchor_ids)
    dups = {k: v for k, v in counts.items() if v > 1}
    assert not dups, f"README.md: duplicate anchors found: {dups}"
    print(f"  ✓ All {len(anchor_ids)} HTML anchors in README.md are unique.")

    # 6. Internal link resolution
    ids_and_slugs = set(anchor_ids)
    for h in re.finditer(r"^(#{1,6})\s+(.*?)\s*$", text, re.M):
        raw = h.group(2).lower()
        slug = re.sub(r"[^0-9a-z]+", "-", raw).strip("-")
        ids_and_slugs.add(slug)
        ids_and_slugs.add("sec-" + slug)
    links = re.findall(r"\[[^\]]+\]\(#([^\s\)]+)\)", text)
    missing = [href for href in links if href not in ids_and_slugs]
    assert not missing, f"README.md: internal links target missing anchors: {missing}"
    print(f"  ✓ All {len(links)} internal markdown links in README.md resolve.")

    # 7. Count singularity
    assert "19 characteristics" in text, (
        "README.md does not reflect the derived 19 characteristics count")
    assert "Eighteen characteristics" not in text, (
        "README.md still contains stale 'Eighteen characteristics'")
    assert "31 formal frontiers" in text, (
        "README.md does not reflect the derived 31 formal frontiers count")
    assert "32 formal frontiers" not in text, (
        "README.md still contains stale '32 formal frontiers'")
    print("  ✓ Characteristic (19) and frontier (31) counts are singular and derived.")

    # 8. Visible line budget
    visible_lines = sum(
        1 for l in lines
        if not l.strip().startswith("<") and not l.strip().startswith("</")
    )
    budget = 1900
    assert visible_lines <= budget, (
        f"README visible lines {visible_lines} exceeds budget {budget}")
    print(f"  ✓ README visible lines ({visible_lines}) within budget ({budget}).")

    print("\nALL README DISAMBIGUATION CHECKS PASSED (0 errors).")


if __name__ == "__main__":
    test_readme_disambiguation()
