#!/usr/bin/env python3
"""Census of the inherited `def`-as-bridge debt (VISIBILITY.md Phase 7).

`scripts/audit_stipulated_defs.py` already enforces the *floor*: no NEW
undisclosed bridge, and the inherited set has not grown. What it does not do is
report the inherited set, which is 28 `def`s used as bare-name premises by 54
theorems. Each is a bridge `#print axioms` cannot see, so each is a price the
kernel does not charge and the corpus must disclose in prose.

This script is the *census* of that debt, and it deliberately reports three
different things which are easy to confuse:

  disclosed   the `def` is named in `GAPMAP.md`, so a reader of the ledger can
              find the price stated. Disclosure is the cheap half.
  reviewed    the allowlist entry was checked against the ledger pointer. No
              entry is `reviewed: true` today, so this column is 0 by design.
  paid        the bridge was promoted to a declared `axiom` (`SemanticFinitude`
              is the one precedent) or registered as a `◈`. Also 0 today.

**Disclosure is not compliance.** Making all 28 visible in the ledger does not
pay a single one of them: they remain `def` premises, still invisible to
`#print axioms`, still carried as inherited debt in the allowlist. The census
keeps reporting all three columns precisely so that a future reader cannot
mistake "now in the ledger" for "now paid". The Phase-3 decision per entry
(promote to `axiom` / register `◈` / accept as debt) is a *semantic* one and is
left to the author; this script only measures and checks.

The second job is the one that matters for trust. Each allowlist entry carries a
hand-written `gapmap` field saying whether the `def` is mentioned in the ledger —
exactly the shape of the defects in VISIBILITY Corrections 11, 12 and 14, where a
maintained field asserted a fact nothing derived. So the field is *derived here*
from the text of `GAPMAP.md` and compared against what the allowlist claims.
`--check` fails when the two disagree, in either direction, so the field can no
longer go quietly stale.

Usage:
    python3 scripts/census_stipulated_defs.py            # table + totals
    python3 scripts/census_stipulated_defs.py --check     # exit 1 on drift
    python3 scripts/census_stipulated_defs.py --undisclosed  # the debt only
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWLIST = ROOT / "scripts" / "stipulated_def_allowlist.json"
GAPMAP = ROOT / "formal" / "GAPMAP.md"

# The disclosure table written into GAPMAP.md by hand. Every inherited bridge is
# listed there; this heading is how the script knows a name is *disclosed* rather
# than merely mentioned somewhere in the ledger by accident.
DISCLOSURE_HEADING = "Dívida herdada de `def`-as-bridge"

# Figures quoted in the GAPMAP disclosure section and re-checked by `--check`.
QUOTED = {"total": 28, "disclosed": 28, "theorems": 53}


def load_entries() -> list[dict]:
    raw = json.loads(ALLOWLIST.read_text(encoding="utf-8"))
    out = []
    for e in raw.get("acknowledged", []):
        name = e["def"].rsplit(".", 1)[-1]
        out.append({
            "full": e["def"],
            "name": name,
            "module": e["def"].rsplit(".", 1)[0],
            "claimed": "NOT MENTIONED" in e.get("gapmap", ""),
            "reviewed": bool(e.get("reviewed", False)),
            "dependents": e.get("dependents", []),
            "n": len(e.get("dependents", [])),
        })
    return out


def disclosure_section(text: str) -> str:
    """The whole disclosure section (heading to the next `## `), which is
    where the quoted figures live."""
    i = text.find(DISCLOSURE_HEADING)
    if i < 0:
        return ""
    j = text.find("\n## ", i + 1)
    return text[i:] if j < 0 else text[i:j]


def disclosure_region(text: str) -> str:
    """The disclosure section's own region. Presence *there* is what the census
    counts as a table row; presence anywhere in the ledger is what the allowlist
    field claims, and the two are checked against each other rather than
    conflated -- an entry disclosed in prose only is disclosed, but it has no row
    of its own here."""
    i = text.find(DISCLOSURE_HEADING)
    if i < 0:
        return ""
    j = text.find("\n## ", i + 1)
    section = text[i:] if j < 0 else text[i:j]
    # Narrow to the table body. The section's closing prose deliberately re-names
    # the headline entries, and counting those as "has a row" would make the check
    # unfireable.
    lines = section.splitlines()
    start = next((k for k, l in enumerate(lines)
                  if l.startswith("| `def` |") or l.startswith("| `def` |")), None)
    if start is None:
        return ""
    body = []
    for l in lines[start:]:
        if l.startswith("|"):
            body.append(l)
        elif body:
            break
    return "\n".join(body)


def main() -> int:
    check = "--check" in sys.argv
    only_undisclosed = "--undisclosed" in sys.argv
    entries = load_entries()
    gapmap = GAPMAP.read_text(encoding="utf-8")
    section = disclosure_section(gapmap)
    region = disclosure_region(gapmap)

    for e in entries:
        e["disclosed"] = e["name"] in gapmap
        e["has_row"] = bool(region) and e["name"] in region

    total = len(entries)
    disclosed = [e for e in entries if e["disclosed"]]
    undisclosed = [e for e in entries if not e["disclosed"]]
    no_row = [e for e in entries if not e["has_row"]]
    reviewed = [e for e in entries if e["reviewed"]]
    theorems = sum(e["n"] for e in entries)

    if not only_undisclosed:
        print("Inherited `def`-as-bridge census (VISIBILITY.md Phase 7)")
        print("=" * 74)
        print("Disclosure is NOT compliance: `disclosed` means the price is written")
        print("down in the ledger, not that it is paid. See the module docstring.")
        print()
        print(f"  inherited bridges (allowlist, `reviewed: false`) : {total}")
        print(f"  disclosed in GAPMAP.md                            : {len(disclosed)}")
        print(f"  UNDISCLOSED in the ledger                         : {len(undisclosed)}")
        print(f"  with a row in the disclosure table                 : "
              f"{total - len(no_row)}")
        print(f"  disclosed in prose only (no row of their own)       : {len(no_row)}")
        print(f"  reviewed against the ledger pointer               : {len(reviewed)}")
        print(f"  promoted to a declared `axiom` (paid)              : 0")
        print(f"  theorems resting on a bridge the kernel cannot see: {theorems}")
        print()
        if undisclosed:
            print("Undisclosed bridges, by dependent count (descending)")
            print("-" * 74)
            for e in sorted(undisclosed, key=lambda x: (-x["n"], x["name"])):
                print(f"  {e['n']:>2}  {e['full']}")
        else:
            print("No bridge is invisible to the ledger. (None is *paid*.)")
        print()

    rc = 0
    if check:
        derived = {"total": total, "disclosed": len(disclosed),
                  "theorems": theorems}
        if not section:
            print(f"✗ GAPMAP.md has no `{DISCLOSURE_HEADING}` section, so no bridge "
                  f"can be disclosed. Add it before trusting the count above.")
            rc = 1
        # The hand-written `gapmap` field vs the derived fact. This is the check
        # that makes the field trustworthy rather than merely correct today.
        for e in entries:
            claimed_missing, actual = e["claimed"], e["has_row"]
            if claimed_missing and actual:
                print(f"✗ ALLOWLIST DRIFT: {e['full']} is claimed "
                      f"'NOT MENTIONED in GAPMAP.md' but is named in the disclosure "
                      f"section. Update the `gapmap` field.")
                rc = 1
            elif not claimed_missing and not e["has_row"]:
                print(f"✗ ALLOWLIST DRIFT: {e['full']} claims a GAPMAP mention but has "
                      f"no row in the disclosure section. Add the row, or correct the "
                      f"`gapmap` field to say it is prose-only.")
                rc = 1
            elif e["claimed"] is False and not e["disclosed"]:
                print(f"✗ ALLOWLIST DRIFT: {e['full']} claims a GAPMAP mention but its "
                      f"name appears nowhere in GAPMAP.md.")
                rc = 1
        for e in entries:
            if e["reviewed"]:
                print(f"✗ {e['full']} is marked reviewed: true; the census has no "
                      f"evidence for that and the three-way decision is the author's.")
                rc = 1
        for key, want in QUOTED.items():
            m = re.search(rf"`{key}`[^|\n]*\|\s*\*\*(\d+)\*\*", section)
            if not m:
                print(f"✗ GAPMAP disclosure section does not quote `{key}` "
                      f"as **{want}**; the census cannot be checked against it.")
                rc = 1
            elif m.group(1) != str(derived[key]):
                print(f"✗ GAPMAP DRIFT — {key}: allowlist gives {derived[key]}, "
                      f"quoted {m.group(1)}")
                rc = 1

    if check:
        print("\nRESULT: DRIFT DETECTED" if rc else
              "\nRESULT: census matches the allowlist and the ledger disclosure")
    return 1 if rc else 0


if __name__ == "__main__":
    raise SystemExit(main())
