#!/usr/bin/env python3
"""sync_docstring_footprints.py — Verify every docstring `Footprint:` marker
against the authoritative kernel axiom set (`formal/axiom_audit.json`).

The `Footprint:` field in the `/-- … -/` docstrings of `formal/Logos/*.lean`
is a *copy* of the kernel's `#print axioms` output. The audit is the source of
truth; this checker makes the copy testable forever (STRENGTH.md §7.1).

Normalization (STRENGTH.md §1.3):
  - audit side: base-name each `Logos.*` axiom (`Logos.Agency.Subject` →
    `Subject`), keep the meta-logic trio raw (`propext`, `Classical.choice`,
    `Quot.sound`), and drop the declaration's own full name (declared axioms
    list themselves in their own `#print axioms` output).
  - doc side: split on commas, expand the token `CL` → the trio, strip
    backticks.
  - comparison is set-equality; an empty doc set (`{}`/`[]`) must equal an
    empty audit set.

Two claim forms are verified, identically:
  - the canonical `Footprint: `{…}`` marker; and
  - inline/alternative copies — lowercase `footprint {…}` or colon-less
    `Footprint {…}` (STRENGTH.md §1.3 marker hazards) — the first brace-set
    after the word "footprint" on a line.
A docstring that mentions "footprint" with NO parseable set (e.g. prose
`Footprint: depends on A17.`) cannot be machine-verified: warned, not failed.
A footprint claim on a decl absent from the audit is a D1-class warning, not a
failure.

Exit codes: 0 when every footprint claim matches the audit (warnings allowed);
1 when any mismatch is found. Scope (v1) = decls that make a footprint claim;
decls without one are not errors by design.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from scripts.build_deduction import META_LOGIC, parse_lean_sources

AUDIT_PATH = ROOT / "formal" / "axiom_audit.json"

# Backtick-optional set marker. The corpus wraps sets in backticks
# (`Footprint: \`{Means, Subject}\``); the star `[^}]*` capture stops at the
# first `}` so an optional trailing backtick is matched separately.
FOOTPRINT_RE = re.compile(r"Footprint:\s*`?\{([^}]*)\}`?`?")

# Alternative-form footprint copy: lowercase/inline `footprint {…}` or a
# capital-but-colon-less `Footprint {…}` on the same line. These are footprint
# claims too, so they are verified against the audit the same way (the first
# brace-set after the word "footprint" on that line is the claimed set).
INLINE_RE = re.compile(r"(?i)footprint[^\n]*?\{([^{}\n]*)\}")

# A "footprint" mention with NO parseable set at all (prose such as
# `Footprint: depends on A17.`) — cannot be machine-verified; warned only.
FOOTPRINT_WORD_RE = re.compile(r"(?i)\bfootprint\b")

CL_EXPANSION = frozenset(META_LOGIC)


def load_audit() -> dict:
    import json
    if not AUDIT_PATH.exists():
        raise SystemExit(
            f"ERROR: {AUDIT_PATH} missing. Run `python3 scripts/audit_footprints.py` first."
        )
    return json.loads(AUDIT_PATH.read_text(encoding="utf-8"))


def audit_tokens(audit: dict, full: str) -> tuple[set, bool]:
    """Expected axiom set for `full` (present_in_audit, expected set)."""
    fp = audit.get(full)
    if fp is None:
        return set(), False
    out = set()
    for a in fp:
        if a == full:
            continue  # declared axioms list themselves in their own footprint
        if a in META_LOGIC:
            out.add(a)
        elif a.startswith("Logos."):
            out.add(a.rsplit(".", 1)[-1])
        else:
            out.add(a)
    return out, True


def doc_tokens(marker_text: str) -> set:
    tokens = set()
    for tok in marker_text.split(","):
        tok = tok.strip()
        if not tok:
            continue
        if tok == "CL":
            tokens |= set(CL_EXPANSION)
        else:
            tokens.add(tok)
    return tokens


def scan() -> tuple[list, list, int]:
    """Return (mismatches, warnings, checked_count)."""
    decls = parse_lean_sources()
    audit = load_audit()
    mismatches, warnings = [], []
    checked = 0

    for full, d in sorted(decls.items()):
        doc_full = d.get("doc_full") or ""
        m = FOOTPRINT_RE.search(doc_full)
        if m is not None:
            checked += 1
            expected, present = audit_tokens(audit, full)
            got = doc_tokens(m.group(1))
            if not present:
                warnings.append(
                    f"{full} ({d['file']}:{d['line']}): has a Footprint marker "
                    f"but is absent from the audit (D1-class)"
                )
            elif got != expected:
                mismatches.append({
                    "full": full,
                    "file": d["file"],
                    "line": d["line"],
                    "kind": "canonical",
                    "doc": "{" + ", ".join(sorted(got)) + "}",
                    "audit": "{" + ", ".join(sorted(expected)) + "}",
                })
            continue
        im = INLINE_RE.search(doc_full)
        if im is not None:
            checked += 1
            expected, present = audit_tokens(audit, full)
            got = doc_tokens(im.group(1))
            if not present:
                warnings.append(
                    f"{full} ({d['file']}:{d['line']}): has an inline footprint "
                    f"claim but is absent from the audit (D1-class)"
                )
            elif got != expected:
                mismatches.append({
                    "full": full,
                    "file": d["file"],
                    "line": d["line"],
                    "kind": "inline",
                    "doc": "{" + ", ".join(sorted(got)) + "}",
                    "audit": "{" + ", ".join(sorted(expected)) + "}",
                })
            continue
        if FOOTPRINT_WORD_RE.search(doc_full):
            warnings.append(
                f"{full} ({d['file']}:{d['line']}): mentions \"footprint\" "
                f"without a parseable set (prose) — not machine-verified"
            )

    return mismatches, warnings, checked


def main() -> int:
    mismatches, warnings, checked = scan()

    print("Docstring ↔ audit footprint sync check")
    print(f"  checked {checked} footprint claims (canonical markers + inline copies)")
    for w in warnings:
        print(f"  ⚠ {w}")
    if not mismatches:
        print("  ✓ 0 mismatches — every marker matches formal/axiom_audit.json")
        return 0
    print(f"  ✗ {len(mismatches)} mismatch(es):")
    for mm in mismatches:
        print(f"    {mm['full']} ({mm['file']}:{mm['line']}): "
              f"doc {mm['doc']} ≠ audit {mm['audit']}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())