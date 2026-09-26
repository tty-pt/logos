#!/usr/bin/env python3
"""audit_stipulated_defs.py — machine-enforce the ◈ discipline on asserted `Prop`s.

## The blind spot this closes

`#print axioms` reports the *axioms* a closed term depends on. A `def` is transparent, so the
kernel unfolds it and reports only the constants it mentions. A `Prop` that is **asserted** by a
`def` — as opposed to derived by a `theorem` — is therefore invisible to every axiom-counting
tool in the repo. Writing a load-bearing assumption as a `def` moves it out of the audit's
field of view *without reducing the assumption by one iota*.

That is not hypothetical. `Logos.AsietyFreedom.AsietyFreedomOfGround` is the whole load-bearing
step of the ASIETY-FREEDOM chain, and its footprint is `{Means, Subject}` — which is what the
kernel reports if the bridge were `2 + 2 = 4`. Its visibility rests entirely on the
`Stipulations.lean` registry and the README badge, i.e. on a promise an agent kept by hand.
This script turns the promise into an invariant.

## What counts as a "bridge"

A `def` is a **bridge** when it is (a) used as the *entire* type of a hypothesis binder, and
(b) a global kernel declaration about Γ's own vocabulary. Both halves matter:

- (a) bare-name binder only. `(h : AsietyFreedomOfGround)` and
  `(hBridge : weak_act_implies_strong_act)` are bridges. A compound premise
  `(hG : GroundsEntity Entity.ofGround (EntityOf s))` is a *stated fact*, not an assertion, and a
  structure premise `(h : GenuineNormativity s p q)` carries data. Neither is flagged.
- (b) resolved to a `Logos.*` key present in `formal/axiom_audit.json`, with **local defs
  shadowing globals** (countermodel modules declare generic `Subject`/`Person` of their own; those
  are model components, not claims about Γ, and they have no qualified kernel key).

## The two error classes

1. **Undisclosed.** A bridge with no `Stipulations.lean` registry entry and no reviewed entry in
   `scripts/stipulated_def_allowlist.json`.
2. **A `def` doing axiom work.** A bridge whose audited footprint contains an axiom that is
   *not* `Tag: VOCAB`. Vocabulary axioms are what a definition is expected to mention; a
   `SEM`/`META` footprint under an asserted `Prop` means the assumption is also load-bearing on a
   declared commitment, which must be registered, not merely disclosed.

## The baseline, and why it is not a pass

The corpus already carried inherited debt here, and the honest move is to record it rather than
launder it. `scripts/stipulated_def_allowlist.json` snapshots the bridges that predate this
check, each with `reviewed: false` and a pointer to where it is discussed. Un-reviewed entries
are reported as **inherited debt** and counted, so the debt is visible and cannot grow silently;
they are not counted as compliant. Only `reviewed: true` entries — bridges whose disclosure was
actually checked against the ledger — count as covered.

So a clean run means: *no new undisclosed bridge, and the inherited set has not grown*. It does
not mean the inherited set is paid off, and the summary line says so.

Requires `formal/axiom_audit.json` (run `scripts/audit_footprints.py` first).
`--report` prints findings without failing.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"
LOGOS = FORMAL / "Logos"
LEAN_PATH = FORMAL / "Logos" / "Stipulations.lean"
AUDIT_PATH = FORMAL / "axiom_audit.json"
ALLOWLIST_PATH = ROOT / "scripts" / "stipulated_def_allowlist.json"

DECL_RE = re.compile(r"\b(theorem|lemma|def|example)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
VOCAB_ONLY = {"VOCAB"}


# --------------------------------------------------------------------------- lexing


def strip_comments(text: str) -> str:
    """Remove Lean block comments (`/- -/`, including `/-- -/`) and line comments.

    Block comments nest; docstrings are ordinary block comments, so stripping them uniformly is
    what keeps declaration headers clean.
    """
    out: list[str] = []
    i, n, depth, start = 0, len(text), 0, 0
    while i < n:
        if depth == 0 and text.startswith("/-", i):
            depth, start, i = 1, i, i + 2
            continue
        if depth:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
                continue
            if text.startswith("-/", i):
                depth, i = depth - 1, i + 2
                if depth == 0:
                    out.append("\n" * text.count("\n", start, i))
                continue
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def iter_decls(text: str):
    """Yield (kind, name, header) per declaration. `header` runs to the first `:=` / `where`."""
    for m in DECL_RE.finditer(text):
        tail = text[m.end() :]
        depth, end = 0, len(tail)
        for k, ch in enumerate(tail):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif depth == 0 and tail.startswith(":=", k):
                end = k
                break
            elif depth == 0 and ch == "\n" and re.match(
                r"\s*(theorem|lemma|def|example|axiom|structure|inductive|abbrev|end|namespace)\b",
                tail[k + 1 :],
            ):
                end = k
                break
        yield m.group(1), m.group(2), tail[:end]


def binder_groups(header: str) -> list[str]:
    groups, depth, buf = [], 0, None
    for ch in header:
        if ch == "(":
            if depth == 0:
                buf = []
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and buf is not None:
                groups.append("".join(buf))
                buf = None
        elif depth > 0 and buf is not None:
            buf.append(ch)
    return groups


def binder_type(group: str) -> str | None:
    depth = 0
    for k, ch in enumerate(group):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            return group[k + 1 :].strip()
    return None


BARE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")


# ------------------------------------------------------------------------ vocabulary


def axiom_tags() -> dict[str, str]:
    """Map fully-qualified axiom name -> Tag, read from the `Tag:` first line of its docstring."""
    tags: dict[str, str] = {}
    for path in sorted(LOGOS.glob("*.lean")):
        raw = path.read_text(encoding="utf-8")
        mod = "Logos." + path.stem
        pending: str | None = None
        in_comment = False
        for line in raw.splitlines():
            s = line.strip()
            # --- the `Tag:` marker ------------------------------------------------
            # It lives on the *first line of the docstring*, which in this corpus is
            # written `/--Tag: VOCAB` -- the same physical line as the opening `/--`.
            # Clearing `pending` on `/--` instead of reading the marker off it would
            # miss every tag in the corpus.
            if s.startswith("/--"):
                m = re.match(r"/--\s*Tag:\s*(\w+)", s)
                if m:
                    pending = m.group(1)
            elif s.startswith("Tag:"):
                m = re.match(r"Tag:\s*(\w+)", s)
                if m:
                    pending = m.group(1)

            # --- comment state ----------------------------------------------------
            # A declaration must be recognised only *outside* comments. Prose can wrap
            # onto a line that starts with "axiom ..." (e.g. "...an axiom of Gamma"),
            # and matching that produced the phantom axiom `Logos.AsieticChoice.of`.
            # Both `/-` and `/--` open a comment; `-/` closes it (Lean allows nesting,
            # but this corpus never nests, so a single flag is exact here).
            code = s
            if in_comment:
                idx = code.find("-/")
                if idx == -1:
                    continue
                code = code[idx + 2:]
                in_comment = False
            while True:
                o = code.find("/-")
                c = code.find("-/")
                if o != -1 and (c == -1 or o < c):
                    code = code[:o] + " " + code[o + 2:]
                    in_comment = True
                    idx = code.find("-/")
                    if idx == -1:
                        code = ""
                        break
                    code = code[:idx] + " " + code[idx + 2:]
                    in_comment = False
                else:
                    if c != -1:
                        code = code[:c] + " " + code[c + 2:]
                    break

            # --- declaration ------------------------------------------------------
            am = re.match(r"^axiom\s+([A-Za-z_][A-Za-z0-9_']*)\b", code)
            if am:
                tags[f"{mod}.{am.group(1)}"] = pending or "UNTAGGED"
                pending = None
    return tags


def registry_anchored_defs() -> set[str]:
    names: set[str] = set()
    if not LEAN_PATH.exists():
        return names
    for line in LEAN_PATH.read_text(encoding="utf-8").splitlines():
        m = re.match(r'\s*anchor\s*:=\s*"(.*)"\s*$', line)
        if m:
            names.update(re.findall(r"\bdef\s+([A-Za-z_][A-Za-z0-9_']*)", m.group(1)))
    return names


def load_allowlist() -> dict[str, dict]:
    if not ALLOWLIST_PATH.exists():
        return {}
    raw = json.loads(ALLOWLIST_PATH.read_text(encoding="utf-8"))
    entries = {}
    for e in raw.get("acknowledged", []):
        for field in ("def", "reason", "gapmap"):
            if not e.get(field):
                raise SystemExit(f"ERROR: allowlist entry missing {field!r}: {e!r}")
        e.setdefault("reviewed", False)
        entries[e["def"]] = e
        # Also index the bare name, so an entry may be written either way. The qualified
        # name is the precise key and is what `main` tries first; the bare name is a
        # fallback for hand-written entries.
        entries.setdefault(e["def"].rsplit(".", 1)[-1], e)
    return entries


# ------------------------------------------------------------------------------ main


def main() -> int:
    report = "--report" in sys.argv
    if not AUDIT_PATH.exists():
        print(f"ERROR: {AUDIT_PATH} missing — run scripts/audit_footprints.py first.")
        return 1
    audit = json.loads(AUDIT_PATH.read_text(encoding="utf-8"))
    tags = axiom_tags()

    # (module, name) for every Prop-valued def; and name -> [modules] for the global fallback.
    local_defs: dict[tuple[str, str], str] = {}
    by_name: dict[str, list[str]] = {}
    premise_uses: dict[tuple[str, str], set[str]] = {}

    for path in sorted(LOGOS.glob("*.lean")):
        mod = path.stem
        text = strip_comments(path.read_text(encoding="utf-8"))
        decls = list(iter_decls(text))
        for kind, name, header in decls:
            if kind == "def" and "Prop" in header.split(":=")[0]:
                local_defs.setdefault((mod, name), path.name)
                by_name.setdefault(name, []).append(mod)
            if kind not in {"theorem", "lemma", "def"}:
                continue
            for group in binder_groups(header):
                ty = binder_type(group)
                if ty and BARE.fullmatch(ty):
                    premise_uses.setdefault((mod, ty), set()).add(name)

    # Resolve each bare premise to a qualified kernel name, local defs shadowing globals.
    bridges: dict[str, dict] = {}
    for (mod, ty), users in premise_uses.items():
        if (mod, ty) in local_defs:
            qual = f"Logos.{mod}.{ty}"
        else:
            cands = [f"Logos.{m}.{ty}" for m in by_name.get(ty, []) if f"Logos.{m}.{ty}" in audit]
            if len(cands) != 1:
                continue  # ambiguous shadowing, or not a global declaration
            qual = cands[0]
        if qual not in audit:
            continue  # model component / not a global kernel declaration
        bridges[qual] = {"name": ty, "qual": qual, "module": mod,
                         "users": sorted(users), "footprint": audit[qual]}

    anchored = registry_anchored_defs()
    allow = load_allowlist()

    covered, undisclosed, inherited = [], [], []
    for qual, b in sorted(bridges.items()):
        entry = allow.get(qual) or allow.get(b["name"])
        if b["name"] in anchored:
            covered.append((qual, "◈ registry"))
        elif entry and entry.get("reviewed"):
            covered.append((qual, "allowlist (reviewed)"))
        elif entry:
            b["entry"] = entry
            inherited.append(b)
        else:
            undisclosed.append(b)

    # A `def` doing axiom work: a non-VOCAB axiom under an asserted `Prop`.
    loud = []
    for qual, b in sorted(bridges.items()):
        substantive = sorted({a for a in b["footprint"] if tags.get(a, "UNTAGGED") not in VOCAB_ONLY})
        if substantive:
            loud.append((qual, substantive))

    print("=== audit_stipulated_defs: asserted `Prop`s used as premises ===")
    print(f"  bridges found (globals, bare-name premises) : {len(bridges)}")
    print(f"  covered — ◈ registry                         : {len(covered)}")
    for qual, how in covered:
        print(f"      ✓ {qual}  [{how}]")
    print(f"  covered — allowlist, reviewed                 : "
          f"{len([1 for _, h in covered if h.endswith('reviewed')])}")
    print(f"  INHERITED DEBT (acknowledged, NOT reviewed)   : {len(inherited)}")
    for b in inherited:
        print(f"      · {b['qual']}  ({len(b['users'])} dependent(s))")
    print(f"  UNDISCLOSED (error)                           : {len(undisclosed)}")
    for b in undisclosed:
        # Print the *defining* module (the qualified kernel name), not the using module:
        # `def D` lives in RealityHookAudit but is assumed in ChoiceRepair, so labelling
        # it `ChoiceRepair.D` would name a declaration that does not exist.
        where = "" if b["module"] == b["qual"].split(".")[1] else f" (assumed in {b['module']})"
        print(f"      ✗ {b['qual']}{where}  assumed by: {', '.join(b['users'])}")
    print(f"  `def` resting on a non-VOCAB axiom (error)   : {len(loud)}")
    for qual, ax in loud:
        print(f"      ! {qual}: {ax}")

    rc = 0
    if loud:
        rc = 1
    if undisclosed and not report:
        rc = 1
    if rc:
        print()
        if undisclosed and not report:
            print(f"ERROR: {len(undisclosed)} asserted `Prop`(s) used as premises with no ◈ registry")
            print("entry and no allowlist entry. Each is a load-bearing assumption invisible to")
            print("`#print axioms`. Register it in Stipulations.lean, or acknowledge it in")
            print("scripts/stipulated_def_allowlist.json with a reason and a gapmap pointer.")
        if loud:
            print("ERROR: an asserted `Prop` rests on a non-VOCAB axiom; it must be registered as a")
            print("stipulation with a `Tag:`, not merely disclosed in prose.")
        return 1

    print()
    if inherited:
        print(f"RESULT: no NEW undisclosed bridge, and the inherited set has not grown "
              f"({len(inherited)} acknowledged but still unreviewed).")
        print("The inherited bridges remain OPEN DEBT, not compliant: each is a `def` premise")
        print("invisible to `#print axioms` whose disclosure has not been checked against the")
        print("ledger. Auditing them is tracked in AsietyFreedom.md §0.5 (F-2).")
    else:
        # In `--report` mode the run is informational, so `rc` stays 0 -- but the summary
        # line must still not claim the check passed. An earlier version printed
        # "every asserted `Prop` ... is ◈-registered or reviewed" directly beneath a list
        # of 28 undisclosed bridges, which is the one thing this script exists to prevent.
        if undisclosed:
            print(f"RESULT: NOT PASSING — {len(undisclosed)} asserted `Prop`(s) are used as")
            print("premises with no ◈ registry entry and no allowlist entry. (`--report` is")
            print("informational, so the exit status is still 0; run without `--report` to fail.)")
        else:
            print("RESULT: every asserted `Prop` used as a premise is ◈-registered or reviewed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
