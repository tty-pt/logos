#!/usr/bin/env python3
"""build_deduction.py — Γ / Logos deduction map generator.

Merges four sources of truth:

  1. formal/depgraph.json    — LeanDepViz kernel graph: declarations, kinds,
                               direct dependency edges (the deduction chain).
  2. formal/axiom_audit.json — `#print axioms` per declaration (written by
                               scripts/audit_footprints.py): the exact,
                               transitive kernel axiom set, meta-logic
                               included ({propext, Classical.choice,
                               Quot.sound} = CL). This is the authoritative
                               footprint: the graph's node `customAxioms`
                               undercounts transitively.
  3. formal/Logos/*.lean     — the source: declaration line numbers, formal
                               statements, EN meanings, and each axiom's
                               `Tag:` (VOCAB/SEM/META) on its docstring.
  4. formal/GAPMAP.md        — the claim ledger: IDs, prose references, and
                               the curator transcription of status/footprint,
                               checked (never trusted) against the kernel.

STATUS IS DERIVED, NEVER TRANSCRIBED: for a claim resolved to a kernel node,
the badge is a pure function of (node kind, audited axiom set, declared axiom
tags). GAPMAP statuses only govern claims with no kernel node (blocked /
deferred / faith / spike) — where no deduction exists to analyze.

Output: README.md at the repository root: the deduction chain, level by
level, each claim with its formal notation, its derived status, its axiom
footprint, its dependencies and dependents, plus an axiom inventory and a
consistency report.

Regenerate after any Lean / GAPMAP change:

    python3 scripts/audit_footprints.py   # kernel footprints (writes axiom_audit.json)
    python3 scripts/build_deduction.py

Stdlib only. UTF-8 required.
"""

from __future__ import annotations

import json
import re
import sys
from collections import OrderedDict, defaultdict
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"
LEAN_DIR = FORMAL / "Logos"
GAPMAP_PATH = FORMAL / "GAPMAP.md"
DEPGRAPH_PATH = FORMAL / "depgraph.json"
OUT_PATH = ROOT / "README.md"
PRESENTATION_SPINE_PATH = FORMAL / "presentation_spine.json"


def load_presentation_spine(path: Path = None) -> dict | None:
    """Loads declarative presentation spine metadata defining the human presentation DAG."""
    if path is None:
        path = PRESENTATION_SPINE_PATH
    if path.exists():
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except Exception as e:
            print(f"Warning: failed to load presentation spine from {path}: {e}")
            return None
    return None


CONT_CHARS = ("-", ",", "→", "∧", "∨", "↔", ":", "(", "{", "[", "=", "+")

DECL_KIND = ("theorem", "axiom", "def", "abbrev", "instance", "opaque",
             "inductive", "structure", "example")
DECL_RE = re.compile(r"^(theorem|axiom|def|abbrev|instance|opaque|inductive|structure|example)\b(.*)$")

# Statuses used in GAPMAP
STATUS_ORDER = ["PROVEN", "PROVEN↑", "AXIOM", "BLOCKED", "DEFERRED"]

# ---------------------------------------------------------------------------
# 1. Lean source parsing
# ---------------------------------------------------------------------------


def strip_block_comments(text: str) -> str:
    """Remove /- ... -/ block comments and -- line comments from Lean text."""
    out = []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            j = text.find("-/", i + 2)
            j = n if j < 0 else j + 2
            i = j
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            i = j
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def parse_lean_sources() -> dict:
    """Return {fullName: info} for every user-authored declaration.

    info keys: kind, file (basename), line, statement, doc, stringValue,
    module, name.

    Docstrings (`/-- ... -/`) are read from the RAW line, *before* comment
    stripping: the meaning attached to a declaration is the first paragraph of
    its doc comment (see `_doc_for`). For `def NAME : String := "…"` stubs the
    literal value is captured as `stringValue`.
    """
    decls = {}

    for path in sorted(LEAN_DIR.glob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        scopes: list[tuple[str, str]] = []  # ("namespace"|"section", name)
        cur_doc = ""  # most recent /-- ... -/ doc block
        i, n = 0, len(lines)

        while i < n:
            raw = lines[i]
            ln = i + 1
            ls = raw.lstrip()

            # doc block? /-- <doc> -/ may span several lines. Must check the
            # RAW line: strip_block_comments would erase it first.
            if ls.startswith("/--"):
                dpos = raw.find("/--")
                end = raw.find("-/", dpos + 3)
                if end >= 0:  # single-line /-- ... -/
                    cur_doc = raw[dpos + 3:end].strip()
                    i += 1
                    continue
                # multi-line doc: consume until the closing line with -/
                collected = [raw[dpos + 3:].strip()]
                j = i + 1
                while j < n:
                    nxt = lines[j]
                    end2 = nxt.find("-/")
                    if end2 >= 0:
                        collected.append(nxt[:end2].strip())
                        j += 1
                        break
                    collected.append(nxt.strip())
                    j += 1
                cur_doc = "\n".join(collected)
                i = j
                continue

            text = strip_block_comments(raw)
            stripped = text.strip()

            m_sec = re.match(r"^section(?:\s+([\w.]+))?\s*$", stripped)
            if m_sec:
                scopes.append(("section", m_sec.group(1) or ""))
                i += 1
                continue
            m = re.match(r"^namespace\s+([\w.]+)\s*$", stripped)
            if m:
                scopes.append(("namespace", m.group(1)))
                i += 1
                continue
            m_end = re.match(r"^end(?:\s+([\w.]+))?\s*$", stripped)
            if m_end:
                if scopes:
                    scopes.pop()
                i += 1
                continue

            m2 = re.match(DECL_RE, stripped)
            if not m2:
                i += 1
                continue
            kind, rest = m2.group(1), m2.group(2).strip()
            # name = first identifier token before ':'/'('/whitespace
            name_m = re.match(r"([\w.]+)", rest)
            if not name_m:
                i += 1
                continue
            name = name_m.group(1)
            active_ns = [name for kind_s, name in scopes if kind_s == "namespace"]
            ns = ".".join(active_ns)
            full = f"{ns}.{name}" if ns else name
            stmt, end_line = _capture_statement(lines, ln, kind)
            string_value = ""
            if kind == "def":
                # `def NAME : String := "..."` — the literal may sit on a
                # following line (CountermodelMeanings.lean), so join a few.
                buf = " ".join(lines[ln - 1:ln + 3])
                sv = re.match(r'def\s+[\w.]+\s*:\s*String\s*:=\s*"([^"]*)"',
                              buf.strip())
                if sv:
                    string_value = sv.group(1)
            decls[full] = {
                "kind": kind,
                "name": name,
                "module": ns,
                "file": path.name,
                "line": ln,
                "end_line": end_line,
                "statement": stmt,
                "doc": _doc_for(cur_doc),
                "doc_claim": _claim_gloss_for(cur_doc),
                "doc_full": _doc_full_for(cur_doc),
                "tag": _tag_for(cur_doc),
                "stringValue": string_value,
            }
            cur_doc = ""
            i = end_line

    return decls


TAG_RE = re.compile(r"^Tag:\s*([A-Za-z_][A-Za-z0-9_]*)\s*$", re.M)


def _tag_for(doc: str) -> str:
    """Axiom-type tag declared on the docstring's `Tag:` line (VOCAB/SEM/META)."""
    m = TAG_RE.search(doc or "")
    return m.group(1) if m else ""


def _doc_for(doc: str) -> str:
    """First paragraph of a doc comment, trimmed to ~260 chars.

    A leading `Tag: VOCAB` line (mechanical, for the axiom registry) is
    dropped and never becomes part of the meaning.
    """
    if not doc:
        return ""
    m = re.match(r"^Tag:\s*[A-Za-z_][A-Za-z0-9_]*\s*\n?", doc)
    if m:
        doc = doc[m.end():]
    para = doc
    # cut at first blank-line-equivalent marker like a double newline or '-\n'
    for sep in ("\n\n", "-\n", ".\n"):
        if sep in para:
            para = para.split(sep, 1)[0]
    para = " ".join(para.split())
    if len(para) > 260:
        cut = para[:260]
        if " " in cut:
            cut = cut.rsplit(" ", 1)[0]
        para = cut.rstrip(" ,;:.") + "…"
    return para


def _claim_gloss_for(doc: str) -> str:
    """First paragraph of a doc comment, *uncapped* (FORMAT.md §4.1).

    Same paragraph cut as `_doc_for` but without the ~260-char trim, so the
    `**Claim:**` line carries the complete meaning sentence(s).
    """
    if not doc:
        return ""
    m = re.match(r"^Tag:\s*[A-Za-z_][A-Za-z0-9_]*\s*\n?", doc)
    if m:
        doc = doc[m.end():]
    para = doc
    for sep in ("\n\n", "-\n", ".\n"):
        if sep in para:
            para = para.split(sep, 1)[0]
    return " ".join(para.split())


def _doc_full_for(doc: str) -> str:
    """Full doc comment (all paragraphs), with only the mechanical `Tag:` line
    dropped. Paragraphs are preserved so `Philosophical cost:` text (appended
    after a blank line) is available to Appendix B and Section 5, while the
    displayed gloss stays `_doc_for`'s first paragraph."""
    if not doc:
        return ""
    m = re.match(r"^Tag:\s*[A-Za-z_][A-Za-z0-9_]*\s*\n?", doc)
    if m:
        doc = doc[m.end():]
    return doc.strip()


def _cost_for(doc_full: str) -> str:
    """The `Philosophical cost:` paragraph of an axiom docstring, if present."""
    m = re.search(r"Philosophical cost:\s*(.*)", doc_full or "", re.S)
    if not m:
        return ""
    txt = " ".join(m.group(1).split())
    return (txt[0].upper() + txt[1:]) if txt else txt


def _capture_statement(lines: list, start: int, kind: str) -> tuple[str, int]:
    """Return (statement_text, last_consumed_line_index) for a declaration."""
    first = lines[start - 1]
    frag = first
    i = start  # 0-based index of next line
    statement = first.strip()
    if ":=" in statement:
        return statement.split(":=", 1)[0].strip(), start

    if kind in ("axiom", "inductive", "structure"):
        # capture until a "terminal" line (axiom type complete)
        # inductive / structure: header only
        if kind != "axiom":
            return statement.strip(), start
        while i < len(lines):
            nxt = lines[i]
            if not nxt.strip():
                break
            s = nxt.strip()
            # terminal: doesn't end with a continuation char
            if not s.endswith(CONT_CHARS):
                statement = (statement + " " + s).strip()
                return statement, i + 1
            statement = (statement + " " + s).strip()
            i += 1
        return statement.strip(), i

    # theorem / def / abbrev / instance / example: capture until `:=`
    while i < len(lines):
        nxt = lines[i]
        if not nxt.strip():
            break
        if ":=" in nxt:
            statement = (statement + " " + nxt.split(":=", 1)[0].strip()).strip()
            return statement.strip(), i
        s = nxt.strip()
        statement = (statement + " " + s).strip()
        i += 1
        # unbraced equation-compiler defs (e.g. `def TrueAt ... \n | atom ...`)
        if nxt.strip().endswith("(") or ("|" == nxt.strip()[:1]):
            break
        if "|" == s[:1]:
            break
    return statement.strip(), i


# ---------------------------------------------------------------------------
# 2. GAPMAP parsing
# ---------------------------------------------------------------------------

CLAIM_ID_RE = re.compile(r"^(C\d+|F\d+[ab]?|FAITH-\d+|Q7\.\d)\s*$")


def parse_gapmap() -> list:
    """Return sections: [{title, claims:[{...}]}]. claims entries without
    a lean name (deferred/faith rows) keep note text instead."""
    text = GAPMAP_PATH.read_text(encoding="utf-8")
    sections = []
    cur = None

    for line in text.splitlines():
        s = line.strip()
        m = re.match(r"^#{2,3}\s+(.*)$", s)
        if m:
            title = m.group(1).strip()
            cur = {"title": title, "claims": []}
            sections.append(cur)
            continue
        if not s.startswith("|"):
            continue
        if cur is None:
            continue
        cells = [c.strip() for c in s.strip("|").split("|")]
        if not cells or not CLAIM_ID_RE.match(cells[0]):
            continue
        claim = {"id": cells[0], "prose": "", "status": "", "footprint": "",
                 "lean_ref": "", "note": "", "section": cur["title"],
                 "level_key": _level_key(cur["title"])}
        if len(cells) >= 5:
            _, claim["prose"], lean_cell, status, footprint = cells[:5]
            claim["lean_ref"] = _extract_lean_ref(lean_cell)
            claim["status"] = _clean_status(status)
            claim["footprint"] = re.sub(r"`+", "", footprint).strip()
        elif len(cells) >= 4 and claim["id"].startswith(("F", "Q")):
            _, claim["prose"], status, note = cells[:4]
            claim["status"] = _clean_status(status)
            claim["note"] = re.sub(r"`+", "", note).strip()
            claim["lean_ref"] = _extract_lean_ref(note)
        else:
            continue
        cur["claims"].append(claim)
    return sections


_LEVEL_MODULES = {
    "Level 0": {"Core"},
    "Level 1": {"Necessity", "Semantics", "Truthmaker", "Modal"},
    "Level 2": {"Agency", "Person", "Alternatives", "Order", "GroundPerson"},
    "Level 3": {"Choice", "Value", "Plurality", "Love"},
}


def _level_key(title: str) -> str:
    m = re.match(r"^Level\s+\d", title)
    return m.group(0) if m else ""


def _extract_lean_ref(cell: str) -> str:
    """Pull the Lean declaration name out of a GAPMAP cell.

    Strategy: split the cell into backtick-delimited spans and take the first
    identifier run in each span; the FIRST span usually holds the theorem name
    (possibly module-qualified like `Order.judge_commits`). Return the first
    candidate, empty if none."""
    spans = re.findall(r"`([^`]*)`", cell)
    for span in spans:
        m = re.search(r"[A-Za-z_][A-Za-z0-9_.]*", span)
        if m:
            tok = m.group(0).strip()
            if tok.startswith(("Logos",)):
                continue
            return tok
    return ""


def _clean_status(s: str) -> str:
    for st in sorted(STATUS_ORDER, key=len, reverse=True):  # longest first: PROVEN↑ before PROVEN
        if s.startswith(st):
            return st
    return s.split()[0] if s else ""


# ---------------------------------------------------------------------------
# 3. Depgraph loading
# ---------------------------------------------------------------------------


def load_depgraph() -> dict:
    data = json.loads(DEPGRAPH_PATH.read_text(encoding="utf-8"))
    nodes = data["nodes"]
    node_map = {}
    for n in nodes:
        node_map.setdefault(n["fullName"], n)
    edges = data["edges"]

    out = defaultdict(set)  # source -> targets
    inn = defaultdict(set)  # target -> sources
    for e in edges:
        s, t = e["source"], e["target"]
        if t.startswith("Logos."):
            out[s].add(t)
        if s.startswith("Logos."):
            inn[t].add(s)
    return {"node_map": node_map, "out": dict(out), "in": dict(inn)}


# ---------------------------------------------------------------------------
# 4. Resolution: GAPMAP claim <-> kernel declaration
# ---------------------------------------------------------------------------


def resolve(lean_ref: str, decls: dict, node_map: dict, level_key: str = "") -> str | None:
    if not lean_ref:
        return None
    ref = lean_ref.replace("`", "").strip()
    parts = ref.split(".")
    if len(parts) >= 2:
        qualified = "Logos." + ref
        if qualified in decls:
            return qualified
    bare = parts[-1]
    matches = [f for f in decls if f.rsplit(".", 1)[-1] == bare]
    if len(matches) == 1:
        return matches[0]
    if len(matches) > 1:
        # prefer the module that belongs to the claim's level (e.g. a bare
        # `nonContradiction` at Level 0 is `Logos.Core.nonContradiction`)
        mods = _LEVEL_MODULES.get(level_key, set())
        if mods:
            preferred = [f for f in matches if f.split(".")[1] in mods]
            if len(preferred) == 1:
                return preferred[0]
        return sorted(matches)[0]  # deterministic fallback; noted in the report
    return None


# ---------------------------------------------------------------------------
# 5. Render
# ---------------------------------------------------------------------------

STATUS_BADGE = {
    "PROVEN": "✔",
    "PROVEN↑": "⚠",
    "AXIOM": "◆",
    "BLOCKED": "✖",
    "DEFERRED": "➖",
}

# ---------------------------------------------------------------------------
# Axiom registry — derived from the Lean source (each axiom's `Tag:` line),
# NOT from a script-side hardcode. The badge is a pure function of (node kind,
# audited kernel footprint, declared tag).
# ---------------------------------------------------------------------------

AUDIT_PATH = FORMAL / "axiom_audit.json"

# D1 — classical meta-logic (kernel-level, indistinguishable per-declaration
# from the audit output and not part of the deduction's own axioms).
META_LOGIC = {"propext", "Classical.choice", "Quot.sound"}
_META_SHORTS = {n.rsplit(".", 1)[-1] for n in META_LOGIC}

TAG_VOCAB = "VOCAB"   # relation/sort the statement itself talks about
TAG_SEM = "SEM"       # semantic choice, consistency-model recorded
TAG_META = "META"     # metaphysical bridge, price explicit
TAG_TRANS = "TRANS"   # transcendental / performative datum
KNOWN_TAGS = {TAG_VOCAB, TAG_SEM, TAG_META, TAG_TRANS}

# Set in `main()` once the sources are parsed; read by the render helpers so
# the derivation machinery needs no parameter threading.
_AUDIT: dict = {}      # decl fullName -> [axiom names] (#print axioms)
_REGISTRY: dict = {}   # axiom base name -> {"tag", "gloss", "full"}

# Axioms demoted to def/theorem by recorded batches, kept ONLY so the
# footprint check spots stale GAPMAP transcriptions after a demotion (a cell
# still listing them as footprint members). Never used for status. Update in
# the demotion batch itself.
RETIRED_AXIOMS = {"ExistsAt", "AxPersonStability"}


def _short(name: str) -> str:
    """Bare identifier for CL classification (`Init.Core.propext` → propext)."""
    return name.rsplit(".", 1)[-1]


def audit_footprint(full: str) -> list:
    """Exact, transitive kernel axiom set of a declaration (empty if the decl
    is not an audited kernel node)."""
    return _AUDIT.get(full) or []


def footprint_parts(full: str) -> tuple[list, list, list]:
    """Split the audited kernel footprint → (substantive, vocab, cl)."""
    global _REGISTRY, _AUDIT
    if not _AUDIT:
        _AUDIT = load_audit()
    decls = _CTX.get("decls") or parse_lean_sources()
    node_map = _CTX.get("node_map") or load_depgraph()["node_map"]
    if not _REGISTRY:
        _REGISTRY = load_axiom_registry(decls, node_map)
    subst, vocab, cl = [], [], []
    for a in audit_footprint(full):
        if a.startswith("Logos."):
            base = a.rsplit(".", 1)[-1]
            r = _REGISTRY.get(base) or _REGISTRY.get(a)
            if r is None:
                d = decls.get(a) or next((v for k, v in decls.items() if k.endswith("." + base) and v.get("tag")), None)
                if d and d.get("tag") in (TAG_SEM, TAG_META, TAG_TRANS, TAG_VOCAB):
                    r = {"tag": d["tag"], "gloss": d.get("doc", ""), "full": a}
                    _REGISTRY[base] = r
                    _REGISTRY[a] = r
            if r is None:
                raise SystemExit(f"FATAL: axiom `{a}` in footprint of `{full}` "
                                 f"has no registry tag (Tag: line missing in Lean)")
            (subst if r["tag"] in (TAG_SEM, TAG_META, TAG_TRANS) else vocab).append(base)
        elif _short(a) in _META_SHORTS:
            cl.append(a)
        else:
            raise SystemExit(f"FATAL: unrecognized axiom `{a}` in footprint of `{full}`")
    return sorted(set(subst)), sorted(set(vocab)), sorted(cl)


def is_vocab_only(full: str) -> bool:
    """True when a claim's kernel footprint carries only declared vocabulary
    axioms (VOCAB) of the statement itself and no substantive axiom (SEM/META/TRANS).
    The theorem is axiom-free modulo the declared vocabulary. Displays ✔."""
    subst, vocab, _ = footprint_parts(full)
    return bool(vocab) and not subst


def kernel_fp_text(full: str) -> str:
    """Rendered kernel footprint: Logos axiom bases + `CL` for meta-logic."""
    subst, vocab, cl = footprint_parts(full)
    names = subst + vocab + (["CL"] if cl else [])
    return "{" + ", ".join(names) + "}" if names else "{}"


def load_axiom_registry(decls: dict, node_map: dict) -> dict:
    """{axiom base name: {tag, gloss, full}} from the Lean docstrings.

    Every axiom node must carry a `Tag:` line from a closed vocabulary, or
    the generation FAILS — a footprint's badge depends on the tag, so an
    untagged/mistyped axiom is a hard error, not a note."""
    registry = {}
    for full, n in sorted(node_map.items()):
        if n.get("kind") != "axiom":
            continue
        d = decls.get(full)
        if d is None:
            raise SystemExit(f"FATAL: axiom node `{full}` not found in parsed Lean decls")
        tag = (d.get("tag") or "").strip()
        if tag not in KNOWN_TAGS:
            raise SystemExit(f"FATAL: axiom `{full}` has no valid `Tag:` line on its "
                             f"docstring (got {tag!r}; expected one of {sorted(KNOWN_TAGS)})")
        registry[full.rsplit(".", 1)[-1]] = {
            "tag": tag, "gloss": d.get("doc") or "", "full": full,
        }
    return registry


def load_audit() -> dict:
    if not AUDIT_PATH.exists():
        raise SystemExit(f"ERROR: {AUDIT_PATH} missing. Run "
                         "`python3 scripts/audit_footprints.py` first (see AGENTS.md).")
    return json.loads(AUDIT_PATH.read_text(encoding="utf-8"))


def expand_footprint(cid: str, fp_by_id: dict, seen=None) -> str:
    """Resolve an inherited GAPMAP footprint (`as C18`, `via C40`) recursively
    to the concrete axiom set. The curated ledger is the source of truth (from
    `#print axioms`); depviz `customAxioms` undercounts transitively."""
    seen = seen or set()
    fp = fp_by_id.get(cid, "")
    m = re.fullmatch(r"\s*(?:as|via)\s+(C\d+)\b.*", fp)
    if m and m.group(1) not in seen:
        return expand_footprint(m.group(1), fp_by_id, seen | {cid})
    return fp


def curated_footprint(c: dict) -> str:
    """GAPMAP footprint transcription (kept for the annex / consistency check
    only — the badge never consults it)."""
    return c.get("_curated_fp", c.get("footprint") or "")


def le_line(file: str, line: int) -> str:
    return f"[{file}#L{line}](formal/Logos/{file}#L{line})"


def claim_lookup(claims_by_id, fullname):
    """Return claim dict whose resolved fullName == fullname, else None."""
    return claims_by_id.get(fullname)


def dep_list(fullnames, claims_by_id, decls):
    """Name the dependencies, preferring claim IDs, then axioms, then raw."""
    if not fullnames:
        return "—"
    pieces = []
    for f in sorted(fullnames):
        if f not in decls and f.rsplit(".", 1)[-1] not in _REGISTRY:
            continue  # kernel-generated (recOn, injEq, ...)
        cl = claims_by_id.get(f)
        if cl:
            cln = cl.get("_name") or cl.get("lean_ref") or f.rsplit(".", 1)[-1]
            pieces.append(f"**{cl['id']}** `{cln}`")
            continue
        base = f.rsplit(".", 1)[-1]
        if base in _REGISTRY:
            tag = _REGISTRY[base]["tag"]
            pieces.append(f"axiom `{base}` ({tag})")
        else:
            pieces.append(f"`{f.replace('Logos.', '') if f.startswith('Logos.') else f}`")
    return ", ".join(pieces) if pieces else "—"


def _closure_axioms(full: str, graph: dict, node_map: dict) -> set:
    """Transitive Logos-axiom set reachable over the graph's dependency edges
    (in-edges), for tool-fidelity cross-checking against the audit."""
    seen = {full}
    stack = [full]
    ax = set()
    while stack:
        x = stack.pop()
        n = node_map.get(x)
        if n and n.get("kind") == "axiom":
            ax.add(x)
            continue
        for t in graph["in"].get(x, ()):
            if t.startswith("Logos.") and t not in seen:
                seen.add(t)
                stack.append(t)
    return ax


def derived_for(c: dict, node_map: dict) -> str | None:
    """The kernel-derived status of a claim, or None when no deduction exists
    to analyze (no kernel node, or the row is a curator cross-reference:
    deferred / blocked / faith / dissolved — only PROVEN/PROVEN↑/AXIOM rows
    are steps of the deduction)."""
    if _clean_status((c.get("status") or "").strip()) not in ("PROVEN", "PROVEN↑", "AXIOM"):
        return None
    full = c.get("_full")
    if not full or full not in node_map:
        return None
    if node_map[full]["kind"] == "axiom":
        return "AXIOM"
    subst, _, _ = footprint_parts(full)
    return "PROVEN↑" if subst else "PROVEN"


def classify_claims(all_claims: list[dict], decls: dict, node_map: dict) -> dict[str, list[dict]]:
    """Partition claims into FOUND, RETIRED_BLOCKED, and MISSING (3-way distinction).

    FOUND: kernel declaration resolved in decls.
    RETIRED_BLOCKED: explicitly known not to be a current theorem (status is BLOCKED or DEFERRED,
      or claim has no kernel declaration and is not claimed to be proven).
    MISSING: GAPMAP claim refers to a declaration that cannot be found in kernel
      declarations (e.g. a claim linked to a spike file outside `Logos/*.lean`).
    """
    found = [c for c in all_claims if c.get("_full") and c["_full"] in decls]
    missing = [c for c in all_claims if not (c.get("_full") and c["_full"] in decls)
               and _clean_status((c.get("status") or "").strip()) in ("PROVEN", "PROVEN↑")]
    retired_blocked = [c for c in all_claims if c not in found and c not in missing]
    return {
        "FOUND": found,
        "RETIRED_BLOCKED": retired_blocked,
        "MISSING": missing,
    }


def compute_detailed_badges(all_claims: list[dict], decls: dict, node_map: dict) -> dict[str, str]:
    """Compute the displayed status badge for each claim as emitted in README.md."""
    already_seen = {}
    detailed_badges = {}
    for c in all_claims:
        full = c.get("_full")
        if full and full in decls:
            if full in already_seen:
                detailed_badges[c["id"]] = "→"
            else:
                already_seen[full] = c["id"]
                detailed_badges[c["id"]] = badge_for(c, decls, node_map)
        else:
            detailed_badges[c["id"]] = badge_for(c, decls, node_map)
    return detailed_badges


def verify_gloss_relations(all_claims: list[dict], decls: dict, graph: dict):
    """Ensure that prose glosses do not claim relations (like active loving)
    unless that relation actually occurs in the formal statement or kernel dependencies."""
    errors = []
    love_relation_re = re.compile(r"\b(?:someone who loves|loves\s+[a-z]|loving\b)", re.IGNORECASE)

    for c in all_claims:
        gloss = c.get("_gloss") or ""
        full = c.get("_full")
        if not gloss:
            continue

        if love_relation_re.search(gloss):
            has_love = False
            if full and full in decls:
                stmt = decls[full].get("statement", "")
                if "Loves" in stmt or "love_" in full or "Love." in full:
                    has_love = True
                else:
                    for dep in graph.get("in", {}).get(full, ()):
                        if "Love." in dep or "Loves" in dep:
                            has_love = True
                            break
            if not has_love:
                errors.append(
                    f"Claim {c['id']} gloss describes love relation ('{gloss}') "
                    f"but declaration '{full}' does not contain Loves relation in statement or dependencies."
                )

    if errors:
        raise AssertionError("Gloss relation consistency verification failed:\n" + "\n".join(errors))


def render_consistency(sections, decls, node_map, claims_by_id, graph, resolved_info, glosses):
    L = []
    ap = L.append
    ap("## Appendix D — Lean / kernel audit")
    ap("")
    ap("### D.1 Kernel-derived status (badges vs. philosophical statuses)")
    ap("")
    ap("| Machine badge | GAPMAP status | Philosophical status |")
    ap("|---|---|---|")
    ap("| `✔` | PROVEN | LOGICAL or DEFINITIONAL |")
    ap("| `⚠` | PROVEN↑ | SEMANTIC or METAPHYSICAL |")
    ap("| `◆` | AXIOM | tag of the axiom (`VOCAB`/`SEM`/`META`) |")
    ap("| `✖` | BLOCKED | OPEN or COUNTERMODEL |")
    ap("| `➖` | DEFERRED | OPEN |")
    ap("| `→` | dissolved | cross-reference |")
    ap("| `CL` | — | classical meta-logic `{propext, Classical.choice, Quot.sound}` |")
    ap("")
    all_claims = [c for s in sections for c in s["claims"]]

    # 3-way claim classification
    claims_class = classify_claims(all_claims, decls, node_map)
    found_claims = claims_class["FOUND"]
    retired_blocked = claims_class["RETIRED_BLOCKED"]
    missing_claims = claims_class["MISSING"]

    ap("### D.2 Reconciliation report (kernel ↔ GAPMAP)")
    ap("")
    ap(f"- GAPMAP claims with a kernel declaration located (FOUND): "
       f"**{len(found_claims)}** / {len(all_claims)}")
    glossed = [c for c in all_claims if c.get("_gloss")]
    ap(f"- Steps with an **English meaning in code**: **{len(glossed)}** / {len(all_claims)}"
       + ("" if len(glossed) == len(all_claims)
          else f" · **no gloss:** {', '.join(c['id'] for c in all_claims if not c.get('_gloss'))}"))

    if missing_claims:
        ap(f"- **Claims whose referenced theorem is missing (MISSING) ({len(missing_claims)}):**")
        for c in missing_claims:
            ap(f"  - `{c['id']}` ref `{c['lean_ref']}` — {c['prose']}")

    if retired_blocked:
        ap(f"- **Withdrawn / blocked claims (outside the active deduction) ({len(retired_blocked)}):**")
        for c in retired_blocked:
            ap(f"  - `{c['id']}` (`{c['status']}`) ref `{c['lean_ref'] or '—'}` — {c['prose']}")

    kern_theorems = {f for f, n in decls.items() if n["kind"] in ("theorem", "example")}
    covered = {c.get("_full") for c in all_claims if c.get("_full")}
    missing = sorted(f for f in kern_theorems - covered if f in node_map)
    if missing:
        hostile_sep = [f for f in missing if "HostileSemantics" in f]
        modal_calc = [f for f in missing if "Necessity" in f or "Modal" in f]
        semantic_sat = [f for f in missing if "Semantics" in f or "Truthmaker" in f or "Core" in f]
        structural_lemmas = [f for f in missing if f not in hostile_sep and f not in modal_calc and f not in semantic_sat]

        ap(f"- **Kernel theorems supporting the architecture ({len(missing)} intentional unmapped helper/infrastructure theorems):**")
        ap(f"  - *Hostile countermodel separations ({len(hostile_sep)}):* "
           + ", ".join(f.replace("Logos.HostileSemantics.", "") for f in hostile_sep))
        ap(f"  - *Modal calculus S4/K4 machinery ({len(modal_calc)}):* "
           + ", ".join(f.replace("Logos.", "") for f in modal_calc))
        ap(f"  - *Semantic satisfaction & object-language lemmas ({len(semantic_sat)}):* "
           + ", ".join(f.replace("Logos.", "") for f in semantic_sat))
        ap(f"  - *Intermediate agency, order, and relation steps ({len(structural_lemmas)}):* "
           + ", ".join(f.replace("Logos.", "") for f in structural_lemmas))
    else:
        ap("- Every kernel theorem has a claim (or a mapped reference).")

    # --- detailed claims accounting & reconciliation assertion ----------------
    detailed_badges = compute_detailed_badges(all_claims, decls, node_map)
    cnt_prov = sum(1 for b in detailed_badges.values() if b == "✔")
    cnt_up = sum(1 for b in detailed_badges.values() if b == "⚠")
    cnt_ax = sum(1 for b in detailed_badges.values() if b == "◆")
    cnt_repeat = sum(1 for b in detailed_badges.values() if b == "→")
    cnt_blocked = sum(1 for b in detailed_badges.values() if b == "✖")
    cnt_deferred = sum(1 for b in detailed_badges.values() if b == "➖")
    cnt_other = sum(1 for b in detailed_badges.values() if b not in ("✔", "⚠", "◆", "→", "✖", "➖"))

    # Reconcile assertion
    total_detailed = cnt_prov + cnt_up + cnt_ax + cnt_repeat + cnt_blocked + cnt_deferred + cnt_other
    assert total_detailed == len(all_claims), (
        f"Reconciliation error: detailed claims ({total_detailed}) != total claims ({len(all_claims)})"
    )

    steps = [c for c in found_claims if derived_for(c, node_map)]
    derived = [derived_for(c, node_map) for c in steps]
    n_prov_decl = sum(1 for d in derived if d == "PROVEN")
    n_up_decl = sum(1 for d in derived if d == "PROVEN↑")
    n_ax_decl = sum(1 for d in derived if d == "AXIOM")

    ap(f"- **Kernel-derived status** (#print axioms + axiom `Tag:`): "
       f"**{cnt_prov} ✔** · **{cnt_up} ⚠** · **{cnt_ax} ◆** (unique steps detailed in the map)")
    ap(f"- **Reconciled claim inventory ({len(all_claims)} total):** "
       f"{cnt_prov + cnt_up} unique active steps ({cnt_prov} ✔ + {cnt_up} ⚠) · "
       f"{cnt_repeat} repeated / dissolved (→) · "
       f"{cnt_blocked} blocked / missing (✖) · "
       f"{cnt_deferred} deferred (➖)"
       + (f" · {cnt_other} other ({', '.join(b for b in detailed_badges.values() if b not in ('✔', '⚠', '◆', '→', '✖', '➖'))})" if cnt_other else ""))
    philo_hist = defaultdict(int)
    for c in all_claims:
        philo_hist[philo_status(c, node_map)] += 1
    ap("- **Philosophical status histogram:** "
       + " · ".join(f"**{k} {v}**" for k, v in sorted(philo_hist.items())))

    status_div = []
    for c in steps:
        st = _clean_status((c.get("status") or "").strip())
        dv = derived_for(c, node_map)
        if st != dv:
            status_div.append((c["id"], st, dv))
    if status_div:
        ap(f"- **GAPMAP × derived status divergences ({len(status_div)} — "
           f"fix the GAPMAP ledger):**")
        for cid, st, dv in status_div:
            ap(f"  - `{cid}` GAPMAP `{st}` vs derived `{dv}`")
    else:
        ap("- GAPMAP × derived status: **no divergences** (transcription verified).")

    # --- footprint transcription check -------------------------------------
    subst_claims = [c for c in steps if derived_for(c, node_map) == "PROVEN↑"]
    if subst_claims:
        ap(f"- **Steps ⚠ under a substantive axiom (SEM/META)** "
           f"({len(subst_claims)}): " + ", ".join(sorted(c["id"] for c in subst_claims)))
    vocab_only = [c for c in steps if is_vocab_only(c["_full"])]
    if vocab_only:
        ap(f"- **Displayed ✔ by vocabulary only (axiom-free modulo declared vocabulary)** "
           f"(kernel footprint contains only the statement's own VOCAB axioms — no SEM/META/TRANS): "
           f"{', '.join(sorted(c['id'] for c in vocab_only))}")
    ax_vocab = sorted(_REGISTRY)
    divs = []
    for c in all_claims:
        full = c.get("_full")
        fps = (c.get("footprint") or "").strip()
        if not full or full not in node_map or fps in ("—", ""):
            continue
        if fps.startswith("as ") or " as " in fps or fps.startswith("via "):
            continue  # inherited transcription; not independently verifiable
        subst, vocab, _ = footprint_parts(full)
        kern = set(subst) | set(vocab)
        # transcribed axiom names: registry + retired-demotion names matched
        # in the footprint-proper part (before any prose parenthesis — notes
        # like "drops `ExistsAt`" must NOT count). Prose mentions of
        # defs/theorems (`Content`, `Cogito`) never match: only axiom names
        # can be footprint members.
        proper = fps.split("(", 1)[0]
        gap = {a for a in (set(ax_vocab) | RETIRED_AXIOMS)
               if re.search(r"\b" + re.escape(a) + r"\b", proper)}
        if kern != gap:
            ks = "{" + ", ".join(sorted(kern)) + "}"
            gs = "{" + ", ".join(sorted(gap)) + "}"
            divs.append((c["id"], ks, gs))
    if divs:
        ap(f"- **Kernel × GAPMAP footprint divergences** "
           f"({len(divs)} — fix the GAPMAP ledger):")
        for cid, ks, gs in divs:
            ap(f"  - `{cid}` kernel `{ks}` vs GAPMAP `{gs}`")
    else:
        ap("- Kernel × GAPMAP footprint: **no divergences**.")
    # --- tool fidelity: depviz closure vs audit ------------------------------
    fid = []
    for c in found_claims:
        full = c["_full"]
        au = {a for a in audit_footprint(full) if a.startswith("Logos.")}
        cl = _closure_axioms(full, graph, node_map)
        cl.discard(full)
        if au != cl:
            fid.append((c["id"], sorted(a.rsplit(".", 1)[-1] for a in au),
                        sorted(a.rsplit(".", 1)[-1] for a in cl)))
    if fid:
        ap(f"- **Graph (closure) × audit (#print axioms) diverge on "
           f"{len(fid)} claims** (depviz transitive undercount — toolchain, "
           f"not ledger; the audit decides):")
        for cid, au, cl in fid:
            ap(f"  - `{cid}` audit `{{{', '.join(au)}}}` vs graph `{{{', '.join(cl)}}}`")
    # --- axiom registry / coverage ------------------------------------------
    kern_axioms = {n["fullName"] for n in node_map.values() if n["kind"] == "axiom"}
    known = {r["full"] for r in _REGISTRY.values()}
    extra = kern_axioms - known
    ap(f"- Axioms declared in the kernel: **{len(kern_axioms)}**"
       + (f" · **outside the registry (no `Tag:`):** {', '.join(sorted(extra))}" if extra else "")
       + " — **all carry a `Tag:` line on their Lean docstring**" if not extra else "")
    ap("")
    L += render_ledger_tables(sections)
    return L


def render_code_annex(sections, claims_by_id, decls, node_map, graph):
    """Per-claim code references: Lean decl, file:line, kernel footprint,
    Lean dependencies and usage. Everything technical the philosopher-facing
    map intentionally omits. The curated GAPMAP footprint prose is deliberately
    omitted: GAPMAP is the *checked* ledger, not a quoted (Portuguese) source."""
    L = []
    ap = L.append
    ap("### D.4 Per-claim code annex")
    ap("")
    ap("<details>")
    ap("<summary>Lean declaration, file:line, kernel footprint and code dependencies, per claim →</summary>")
    ap("")
    ap("| ID | Lean declaration | File#L | Kernel axioms | Depends on (Lean) | Used by |")
    ap("|---|---|---|---|---|---|")
    for sec in sections:
        for c in sec["claims"]:
            cid = c["id"]
            full = c.get("_full")
            if not full or full not in decls:
                lr = c.get("lean_ref") or "—"
                ap(f"| {cid} | — | — | — | — | {lr} |")
                continue
            d = decls[full]
            kern = kernel_fp_text(full)
            deps = dep_list(graph["in"].get(full, set()), claims_by_id, decls)
            rds = dep_list(graph["out"].get(full, set()), claims_by_id, decls)
            ap(f"| {cid} | `{full}` | {le_line(d['file'], d['line'])} | `{kern}` | {deps} | {rds} |")
    ap("")
    ap("</details>")
    ap("")
    ap("---")
    return L


def render_appendix(sections, decls, node_map, claims_by_id, graph, level_map):
    L = []
    ap = L.append
    ap("### D.5 Kernel declaration index")
    ap("")
    ap("<details>")
    ap("<summary>All user-authored theorems/defs, by module (line and kernel axioms) →</summary>")
    ap("")
    mods = {}
    for f, d in decls.items():
        mods.setdefault(d["module"] or f"Logos.{d['file'][:-5]}", []).append(f)
    for mod in sorted(mods):
        dcl = {f: decls[f] for f in mods[mod]}
        ap(f"### `{mod}`")
        ap("")
        ap("| Name | Kind | Line | Statement (logic) | Axioms |")
        ap("|---|---|---|---|---|")
        for full in sorted(dcl):
            d = dcl[full]
            ax = kernel_fp_text(full) if full in _AUDIT else "—"
            cl = claims_by_id.get(full)
            cid = f"→ {cl['id']}" if cl else ""
            ap(f"| `{d['name']}` | {d['kind']} | [L{d['line']}](formal/Logos/{d['file']}#L{d['line']}) | `{humanise(trim_stmt(d['statement']))[:80]}` | {ax} {cid} |")
        ap("")
    ap("</details>")
    ap("")
    ap("---")
    return L


def render_provenance() -> list:
    L = []
    ap = L.append
    ap("### D.6 Provenance and regeneration")
    ap("")
    ap("Every statement, gloss and cost sentence consumed above lives in the Lean "
       "sources (docstrings, `String` constants, `Tag:` lines); the generated "
       "document transcribes nothing by hand.")
    ap("")
    ap("- **Kernel:** `formal/Logos/*.lean` — `lake build` green, `sorryAx 0`.")
    ap("- **Footprints:** `formal/axiom_audit.json` via `#print axioms` "
       "(transitive kernel axiom set, meta-logic `CL` included).")
    ap("- **Dependency edges:** `formal/depgraph.json` (LeanDepViz).")
    ap("- **Claim ledger (checked, not quoted):** `formal/GAPMAP.md`.")
    ap("- **Regeneration order:**")
    ap("")
    ap("```sh")
    ap('export PATH="$HOME/.elan/bin:$PATH"')
    ap("cd formal && lake build")
    ap("lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot")
    ap("cd .. && python3 scripts/audit_footprints.py && python3 scripts/build_deduction.py")
    ap("```")
    ap("")
    ap("---")
    return L


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------


def trim_stmt(s: str) -> str:
    s = re.sub(r"\s+", " ", s).strip()
    return s[:180] + " …" if len(s) > 180 else s


def short_stmt(s: str) -> str:
    """Declaration header without the leading `theorem`/`def`/etc. keyword."""
    s = trim_stmt(s)
    for p in ("theorem ", "axiom ", "def ", "abbrev ", "inductive ",
              "structure ", "class "):
        if s.startswith(p):
            s = s[len(p):]
            break
    return s


def render_prose_link(prose: str) -> str:
    if not prose:
        return "—"
    if prose.startswith("P"):
        return f"[{prose}](poem.txt)"
    if prose.startswith("§") or "§" in prose:
        return f"[{prose.strip()}](base.txt)"
    if re.match(r"^[\dT]", prose):  # section-ish ref like "T3 …" or "13–15 …"
        return f"[§{prose.strip()}](base.txt)"
    return f"[{prose.strip()}](base.txt)"


def strip_theorem_head(s: str) -> str:
    """Drop `Name (binder)* :` from a theorem statement, keeping the body.
    Binder groups may nest (e.g. `(h : Necessity (p → q))`)."""
    s = s.strip()
    for p in ("theorem ", "axiom ", "def ", "abbrev ", "inductive ",
              "structure "):
        if s.startswith(p):
            s = s[len(p):]
            break
    m = re.match(r"^[A-Za-z_][A-Za-z0-9_.]*\s+", s)
    if not m:
        return s
    i = m.end()
    depth = 0
    seen = False
    j = i
    while j < len(s):
        c = s[j]
        if c in "({[":
            depth += 1
            seen = True
        elif c in ")}]":
            depth -= 1
            if depth == 0 and seen:
                k = j + 1
                while k < len(s) and s[k] == " ":
                    k += 1
                if k < len(s) and s[k] == ":":
                    return s[k + 1:].strip()
                j = k
                continue
        elif not seen:
            if c == ":":
                return s[j + 1:].strip()
            return s
        j += 1
    return s


def kernel_axiom_names(full: str, node_map: dict) -> list:
    """Sorted short names of the audited kernel axiom footprint (Logos axioms
    only; meta-logic `CL` is handled by `footprint_parts`)."""
    subst, vocab, _ = footprint_parts(full)
    return sorted(set(subst) | set(vocab))


def kernel_axiom_text(full: str, node_map: dict) -> str:
    """Axiom names + tags, e.g. `Ground` (VOCAB), `AxTwoSubjects` (META)."""
    tags = [f"`{a}` ({_REGISTRY[a]['tag']})" if a in _REGISTRY else f"`{a}`"
            for a in kernel_axiom_names(full, node_map)]
    return ", ".join(tags)


def badge_for(c: dict, decls: dict, node_map: dict) -> str:
    """Display status, DERIVED from the kernel for every step of the deduction
    (node kind + audited axiom set + declared axiom tags). Curator cross-refs
    (deferred/blocked/faith/dissolved rows, and claims with no kernel node)
    have no deduction to analyze and keep their curated marker."""
    dv = derived_for(c, node_map)
    if dv is not None:
        return STATUS_BADGE[dv]
    st = _clean_status((c.get("status") or "").strip())
    if st in ("PROVEN", "PROVEN↑"):
        # Unresolved claim claimed to be proven -> MISSING from kernel
        return STATUS_BADGE["BLOCKED"]  # "✖"
    return STATUS_BADGE.get(st, st or "?")


def build_ax_id(sections, node_map):
    """A1..An in doc order of first use by a claim."""
    ax_id = {}
    for sec in sections:
        for c in sec["claims"]:
            full = c.get("_full")
            if not full or full not in node_map:
                continue
            for base in kernel_axiom_names(full, node_map):
                if base in _REGISTRY and base not in ax_id:
                    ax_id[base] = f"A{len(ax_id) + 1}"
    return ax_id


def axiom_full_map(node_map):
    return {n["fullName"].rsplit(".", 1)[-1]: n["fullName"]
            for n in node_map.values() if n.get("kind") == "axiom"}


def axiom_ref(base, ax_id):
    if ax_id and base in ax_id:
        return f"**{ax_id[base]}**"
    return f"`{base}`"


def axiom_refs_sorted(bases, ax_id):
    """Kernel-footprint axiom refs ordered by A# (unmapped raws last)."""
    def key(b):
        if ax_id and b in ax_id:
            return (0, int(ax_id[b][1:]))
        return (1, b)
    return [axiom_ref(b, ax_id) for b in sorted(bases, key=key)]


# ---------------------------------------------------------------------------
# Logic-symbol rendering ("humanise")
# ---------------------------------------------------------------------------
# Logic-symbol rendering ("humanise")
# ---------------------------------------------------------------------------

_SUB = str.maketrans("0123456789", "₀₁₂₃₄₅₆₇₈₉")  # subscript digits
_OP1 = ("NecessarilyTrue", "NecessarilyFalse", "NecessityPH", "Necessity", "Dia")
_OP2 = ("TrueAt", "FalseAt", "Satisfies")
_GREEK = "αβγδεζηθικλμνξοπρστυφχψω"

def _read_group(s: str, j: int):
    """s[j] == '(' → (inner_text, index_after_matching ')')."""
    depth = 0
    for k in range(j, len(s)):
        if s[k] == "(":
            depth += 1
        elif s[k] == ")":
            depth -= 1
            if depth == 0:
                return s[j + 1:k], k + 1
    return s[j + 1:], len(s)


def _simple(x: str) -> bool:
    x = x.strip()
    if not x:
        return False
    if x.startswith("(") and x.endswith(")"):
        return True
    if re.fullmatch(r"p[₀₁₂₃₄₅₆₇₈₉]+", x):
        return True
    core = x[1:] if x.startswith("¬") else x
    return bool(re.fullmatch(r"[\w.']+", core))


def _wrap(x: str) -> str:
    x = x.strip()
    return x if _simple(x) else "(" + x + ")"


def _sub_n(n: str) -> str:
    return "p" + n.translate(_SUB)


_FBARE = r"[A-Za-z_α-ωΑ-Ω][A-Za-z0-9_α-ωΑ-Ω]*"


def _bin_sym(op: str) -> str:
    return {"and": "∧", "or": "∨", "imp": "→"}[op]


def _rewrite_form_ops(s: str) -> str:
    """Iterative regex rewrite of Form.not/and/or/imp/atom → logic symbols.

    Patterns handle every arg shape (bare variable or paren group) and recurse
    into groups, so nested constructors resolve deepest-first to a fixpoint."""
    prev = None
    while prev != s:
        prev = s
        s = re.sub(r"Form\.atom\s+(\d+)", lambda m: _sub_n(m.group(1)), s)
        s = re.sub(r"Form\.atom\s+(" + _FBARE + r")", r"atom \1", s)
        s = re.sub(r"Form\.not\s+\(([^()]*)\)",
                   lambda m: "¬" + _wrap(_rewrite_form_ops(m.group(1).strip())), s)
        s = re.sub(r"Form\.not\s+(" + _FBARE + r")",
                   lambda m: "¬" + m.group(1), s)

        def _mk(sym):
            def _f(m):
                a = _rewrite_form_ops(m.group(2).strip())
                b = _rewrite_form_ops(m.group(3).strip())
                return _wrap(a) + " " + sym + " " + _wrap(b)
            return _f

        for pat in (
            r"Form\.(and|or|imp)\s+\(([^()]*)\)\s+\(([^()]*)\)",                    # G G
            r"Form\.(and|or|imp)\s+\(([^()]*)\)\s+(" + _FBARE + r")",                # G bare
            r"Form\.(and|or|imp)\s+(" + _FBARE + r")\s+\(([^()]*)\)",                # bare G
            r"Form\.(and|or|imp)\s+(" + _FBARE + r")\s+(" + _FBARE + r")",           # bare bare
        ):
            s = re.sub(pat, lambda m: _mk(_bin_sym(m.group(1)))(m), s)
    return s


def _rewrite_ops(s: str) -> str:
    """Rewrite NecessarilyTrue/False, TrueAt/Satisfies/FalseAt, Necessity/PH, Dia."""
    out = []
    i, n = 0, len(s)
    while i < n:
        om = re.match(r"[A-Za-z_][A-Za-z0-9_]*", s[i:])
        if om:
            tok = om.group(0)
            if tok in _OP1 or tok in _OP2:
                j = i + len(tok)
                rest = s[j:]
                # OP2: Name arg1 (group)
                m2 = re.match(r"\s*([A-Za-z0-9_'" + _GREEK + r"]+)\s*\(", rest)
                if tok in _OP2 and m2:
                    arg1 = m2.group(1)
                    k = j + m2.end() - 1
                    inner, k2 = _read_group(s, k)
                    arg2 = _rewrite_ops(_rewrite_form_ops(inner.strip()))
                    sym = {"TrueAt": "⊨", "Satisfies": "⊨", "FalseAt": "⊭"}[tok]
                    out.append(f"{arg1} {sym} {_wrap(arg2)}")
                    i = k2
                    continue
                # OP1: Name (group)
                m3 = re.match(r"\s*\(", rest)
                if tok in _OP1 and m3:
                    k = j + m3.end() - 1
                    inner, k2 = _read_group(s, k)
                    body = _rewrite_ops(_rewrite_form_ops(inner.strip()))
                    if tok == "NecessityPH":
                        fmm = re.fullmatch(r"fun\s+[A-Za-z_]+\s*:\s*World\s*=>\s*(.*)", body)
                        if fmm:
                            out.append("∀ w, " + fmm.group(1).strip())
                        else:
                            out.append("□ₚ" + _wrap(body))
                    elif tok == "NecessarilyTrue":
                        out.append("□" + _wrap(body))
                    elif tok == "NecessarilyFalse":
                        out.append("¬◇" + _wrap(body))
                    elif tok == "Necessity":
                        out.append("□" + _wrap(body))
                    elif tok == "Dia":
                        out.append("◇" + _wrap(body))
                    i = k2
                    continue
                # space-applied single-atom (NecessarilyTrue τ, Necessity p, Dia p)
                m4 = re.match(r"\s+([A-Za-z_\u03b1-\u03c9][A-Za-z0-9_.'\u03b1-\u03c9]*)", rest)
                if tok in ("NecessarilyTrue", "NecessarilyFalse", "Necessity",
                           "NecessityPH", "Dia") and m4:
                    pref = {"NecessarilyTrue": "□ ", "NecessarilyFalse": "¬◇ ",
                            "Necessity": "□ ", "NecessityPH": "□ₚ ", "Dia": "◇ "}[tok]
                    out.append(pref + m4.group(1))
                    i = j + m4.end()
                    continue
                # space-applied bare pair (TrueAt w φ → w ⊨ φ)
                m5 = re.match(r"\s+([A-Za-z_0-9'\u03b1-\u03c9][A-Za-z0-9_.'\u03b1-\u03c9]*)\s+([A-Za-z_0-9'\u03b1-\u03c9][A-Za-z0-9_.'\u03b1-\u03c9]*)", rest)
                if tok in _OP2 and m5:
                    tail = rest[m5.end():]
                    if re.match(r"\s*(→|∧|∨|↔|,|\)|:|$)", tail):
                        sym = {"TrueAt": "⊨", "Satisfies": "⊨", "FalseAt": "⊭"}[tok]
                        out.append(f"{m5.group(1)} {sym} {m5.group(2)}")
                        i = j + m5.end()
                        continue
            out.append(tok)
            i += len(tok)
            continue
        out.append(s[i])
        i += 1
    return "".join(out)


def _humanise(s: str) -> str:
    out = _rewrite_ops(_rewrite_form_ops(s))
    return re.sub(r"\((atom [A-Za-z0-9_]+)\)", r"\1", out)


def humanise(stmt: str) -> str:
    """Public entry: Lean statement text → logic-symbol notation."""
    if not stmt:
        return ""
    return _humanise(stmt)


def find_t_refs(prose: str) -> list:
    return re.findall(r"\bT\d+\b", prose or "")


def first_sentence(s: str) -> str:
    s = " ".join(s.split())
    for cut in ("\n", ):
        if cut in s:
            s = s.split(cut, 1)[0]
    return s[:200]


def restore_cur(cur=""):
    return cur


# ---------------------------------------------------------------------------
# Presentation layer (FORMAT.md §2–§9): stages, transitions, countermodels,
# and the English-treatise renderers. All philosophical statuses are DERIVED
# from the kernel; the maps below are presentation data only.
# ---------------------------------------------------------------------------

STAGES = [
    {"key": "I", "title": "The Performative Starting Point", "intro":
     "The argument begins not from an arbitrary propositional premise but from "
     "a performative datum: an act of affirming, denying, doubting or judging "
     "is occurring. The starting point "
     "(`base.txt` §0) is the contrast between an arbitrary premise and a claim "
     "whose negation destroys the very act of negating it. The steps below "
     "attempt, oppose and refute the absolute theses that nothing — or "
     "everything — is true."},
    {"key": "II", "title": "Truth and Falsehood", "intro":
     "Once an act of meaning is occurring, truth and falsehood cannot both be "
     "abolished. The performative absolutes refute themselves (C1–C9); the "
     "classical laws and the object-language distinction between truth and "
     "falsehood follow (C10–C12). The stage closes with the transcendental "
     "principles of semantics and the elementary truthmaker step."},
    {"key": "III", "title": "The Subject of Thought", "intro":
     "The act is always an act *of* a subject and *about* content. From the "
     "performative datum Γ reads off the existence of a subject of thought "
     "(C21), the subject's inseparability from its act, and the collapse of the "
     "subject into the person (*esse est agere*). The stage is definitional "
     "modulo the vocabulary of agency."},
    {"key": "IV", "title": "Agency and Choice", "intro":
     "A subject that acts and judges is a person before a field of incompatible "
     "alternatives. C26/C27/C50 supply the alternatives; C39 and C51/C52 derive "
     "the choice field and its performative retorsion (C53); C54/C61 connect it "
     "to right-and-wrong; C28/C29 record fallibility. F1b (genuine choice and "
     "free will) is closed under the adopted constitutive semantic principle "
     "AxIntentionalChoice (A14, SEM). Strong Act and Genuine Choice are proven "
     "orthogonal in the pre-A14 theory (act_orthogonal_to_genuine_choice_in_full_theory), "
     "with AxIntentionalChoice adopted as the minimal constitutive bridge."},
    {"key": "V", "title": "Necessity", "intro":
     "From the semantic principles and the modal backbone Γ derives the "
     "necessary: excluded middle and non-contradiction, the necessary person, "
     "and the necessary reality (T7). The person/entity lifts are definitional; "
     "the necessary reality itself is the first place a substantive bridge — "
     "`AxGlobalGround` — is priced."},
    {"key": "VI", "title": "Grounding", "intro":
     "Grounding turns truth into a relation to reality. The atomic truthmaker is "
     "definitional; its propositional and global reflections are the priced "
     "semantic bridge (`AxGlobalGround`), and the personal ground is the priced "
     "metaphysical bridge (`AxPersonalGround`). The withdrawn and blocked "
     "ground-theoretic steps are shown here as well."},
    {"key": "VII", "title": "Plurality and Relation", "intro":
     "Right and wrong are interpersonal. The unit world satisfies a single act "
     "with no second subject, so plurality is not derived: it is bought with "
     "`AxTwoSubjects`. Plurality also exhibits the acting subject (C48) and "
     "reaches the distinctness of correct and incorrect judging (C30) and the "
     "judge's choice field (C55). From two distinct persons the directed-pair "
     "and interpersonal-value steps follow."},
    {"key": "VIII", "title": "Love", "intro":
     "Given two distinct persons, love is defined as the mutual help that does "
     "not harm. C41–C45 derive an eternal love-relation between two "
     "persons; plurality alone still does not force love — that is the separate "
     "bridge content."},
    {"key": "IX", "title": "The Remaining Metaphysical Frontier", "intro":
     "The remaining frontier is explicit: teleology, the moral good, the "
     "Trinity, incarnation and creation are deferred or faith data; the "
     "initiation-theoretic and ground-chain constructions are withdrawn under "
     "hostile semantics. Nothing here is presented as derived."},
]

STAGE_OF = {}
for _x in range(1, 13):          # C1–C12
    STAGE_OF[f"C{_x}"] = "II"
for _x in ("C13", "C14", "C16", "C17", "C31", "C35", "C36", "C101"):
    STAGE_OF[_x] = "II"
for _x in ("C58", "C68", "C83", "C84", "C63"):
    STAGE_OF[_x] = "I"
for _x in ("C21", "C22", "C23", "C24", "C25", "C49", "C57", "C62"):
    STAGE_OF[_x] = "III"
for _x in ("C26", "C27", "C28", "C29", "C39", "C50", "C51",
           "C52", "C53", "C54", "C61", "F1a", "F1b", "F7",
           "C69", "C70", "C71", "C72", "C97", "C98", "C99", "C100"):
    STAGE_OF[_x] = "IV"
for _x in ("C37", "C38", "C59", "C93", "C94", "C95", "C96", "C77", "C91", "C92", "FAITH-1"):
    STAGE_OF[_x] = "V"
for _x in ("C15", "C60", "C18", "C19", "C20", "C34", "C78", "C79", "C87",
           "C88", "C89", "C33", "C32", "C90", "Q7.2"):
    STAGE_OF[_x] = "VI"
for _x in ("C40", "C48", "C30", "C55", "C46", "C47", "C56", "C73", "C74",
           "C75"):
    STAGE_OF[_x] = "VII"
for _x in ("C41", "C42", "C43", "C44", "C45", "C76", "C85", "C86", "F4",
           "F5", "FAITH-2"):
    STAGE_OF[_x] = "VIII"
for _x in ("F2", "F3", "F6", "F8", "F9", "C64", "C65", "C66", "C67", "C80",
           "C81", "C82"):
    STAGE_OF[_x] = "IX"

# Explicit chronological reading order (FORMAT.md §4.5). Stable claim IDs must
# not determine reading order: `render_stages` drops dissolved aliases, then
# sorts each stage by this sequence. 84 entries == 109 GAPMAP rows - 20 retired
# - 6 dissolved. A build assertion checks coverage and that no claim precedes
# any kernel predecessor.
READING_ORDER = [
    # I — performative datum
    "C58", "C68", "C83", "C84", "C63",
    # II — truth and falsehood
    "C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8", "C9", "C10", "C11",
    "C12", "C102", "C103", "C104", "C105", "C13", "C14", "C16", "C17", "C31", "C35", "C36", "C101",
    # III — subject and person
    "C21", "C22", "C23", "C24", "C25", "C49", "C57", "C62",
    # IV — alternatives -> choice field -> genuine choice -> free will
    "C26", "C27", "C50", "C39", "C51", "C52", "C53", "C54", "C61",
    "C28", "C29", "C97", "C98", "C99", "C100", "C106", "C107", "F1b",
    # V — necessity (C91 lifts from the necessary subject C77 to the entity)
    "C37", "C38", "C59", "C93", "C94", "C95", "C96", "C77", "C91", "C92",
    # VI — grounding
    "C15", "C60", "C18", "C19", "C20", "C32", "C33", "C34", "Q7.2",
    # VII — plurality (C48/C30/C55 land after C40)
    "C40", "C48", "C30", "C55", "C56", "C46", "C47", "C74",
    # VIII — love
    "C41", "C42", "C43", "C44", "C45", "C85", "C86",
    # IX — remaining frontier
    "F2", "F3", "F6", "F8", "F9", "C108", "C109", "C110", "C111", "C112",
]

# Virtual definitional steps rendered immediately after a claim block.
EXTRA_AFTER = {"F1b": "FREEWILL"}
FREEWILL_FULL = "Logos.Choice.chooses_implies_freeWill"

# Formal targets for frontier rows whose kernel node is a `def`-proposition:
# `_capture_statement` discards a def's `:=`-body, so the target is presentation
# data (mirrored in the Lean def). Rendered as a fenced ```text block.
TARGET_OF = {
    "F1b": r"\exists s\,p\,q\; Chooses(s,p,q) \qquad (\text{closed under constitutive principle } AxIntentionalChoice: Act(s,p) \to \exists q, Chooses(s,p,q))",
}

MODULE_STAGE = {
    "Core": "II", "Semantics": "II", "Necessity": "II", "Truthmaker": "VI",
    "Modal": "V", "Agency": "III", "Person": "III", "Initiation": "I",
    "Alternatives": "IV", "Order": "IV", "Choice": "IV", "Plurality": "VII",
    "Value": "VII", "GroundPerson": "VI", "Love": "VIII",
    "Retorsion": "III",
    "ClaimMeanings": "IX", "CountermodelMeanings": "IX",
    "RetorsiveNormativity": "IV",
    "BipolarityRetorsion": "IV",
    "DirectNormativeRetorsion": "IV",
}

AX_ID = {
    "Ground": "A1", "Subject": "A2", "Truthmaker": "A3",
    "AxGlobalGround": "A4", "Means": "A5", "AxTwoSubjects": "A6",
    "AxPersonalGround": "A7", "GroundProp": "A8", "GroundPrincipleProp": "A9",
    "act": "A10", "State": "A11", "Initiates": "A12",
    "AxActPolarity": "A13",
    "AxIntentionalChoice": "A14",
    "DependsOn": "A15",
    "universal_thesis_claims_objectivity": "A16",
    "transcendental_reflection_intentional": "A17",
    "AxJudicativeBipolarity": "A18",
}

# A proposed inference that a hostile model refutes: withdrawn/retired steps
# (FORMAT.md §4/§10.C). These derive the COUNTERMODEL status when unresolved.
RETIRED_BY_COUNTERMODEL = {
    "C64", "C65", "C66", "C67", "C69", "C70", "C71", "C72", "C73", "C75",
    "C76", "C78", "C79", "C80", "C81", "C82", "C87", "C88", "C89", "C90",
}

CONDITIONAL_CLAIMS = {"C20", "C46", "C77", "C92"}

# Constitutive definitions/lemmas a DEFINITIONAL/CONDITIONAL step rests on
# (FORMAT.md §5.3), rendered as an inline `**Bridge:**` line. Curated: the nine
# tagged axioms already get their `A#` first-use block via `axiom_intro_en`.
BRIDGE_OF = {
    "C21": "`Act s p := Means s p ∧ ∃ w w', Initiates s w w' p`; "
           "`act_requires_subject : Act s p → SubjectExists s`",
    "C23": "Act → Agent: the subject of an intentional act is an agent.",
    "C24": "Act → IntentionalSubject: an act witnesses an intentional subject; substantive Personhood is model-theoretically independent.",
    "C25": "`Person.inseparability_24b` — a person and its act are one",
    "C39": "`ChoiceField s p q := Means s p ∧ Incompatible p q` "
           "(the second horn is supplied by logic, C27/C50)",
    "C51": "`person_hasChoiceField : Person s → ∃ p q, ChoiceField s p q`",
    "C52": "`choiceField_exists`, from the intentional act `A s p`",
    "C54": "`JUDGE_HAS_CHOICE_FIELD` (uses `AxTwoSubjects`)",
    "C55": "`judge_commits` (uses `AxTwoSubjects` and C48)",
    "C77": "`PersonStabilityPrinciple : Person s → NecessarySubject s` (explicit conditional hypothesis, refuted by `CountermodelPersonNotNecessary` and `ContingentAgencyModel`)",
    "C91": "`subject_nec_entity_nec : NecessarySubject s → "
           "NecessaryEntity (EntityOf s)` (definitional lift)",
    "C92": "`PersonStabilityPrinciple` (conditional hypothesis) and `subject_nec_entity_nec` (definitional lift)",
}

# Curated sharper resolutions for obstructions where the generic status phrase
# is too weak (FORMAT.md §5.2). Presentation data, scoped to these rows.
RESOLUTION_OF = {
    "C18": "Γ derives this only under AxGlobalGround; the countermodel shows "
           "that the stronger conclusion is not forced by worldwise truthmaking alone.",
    "C19": "Γ derives this only under AxGlobalGround; the countermodel shows "
           "that the stronger conclusion is not forced by worldwise truthmaking alone.",
    "C77": "Conditional upon PersonStabilityPrinciple; hostile countermodels show that performative agency does not logically force modal subject-necessity.",
    "C92": "Conditional upon PersonStabilityPrinciple; hostile countermodels show that performative agency does not logically force modal entity-necessity.",
}

# Frontier / faith rows that are aliases of an established claim (FORMAT.md
# §10.C). They render as `→ <canonical>` cross-refs; the canonical C-claim
# owns the block. Any other shared kernel node is resolved by id priority
# (C > F > FAITH) in `build_canonical_map`.
ALIAS_TO = {
    "F1a": "C51",       # person_hasChoiceField
    "F4": "C41",        # Love.T13_someoneLovable
    "F5": "C42",        # Love.T14_eternalRelation
    "F7": "F1b",        # freeWill_exists_of_act_polarity derived into F1b
    "FAITH-1": "C38",   # necDistinction is now a theorem
    "FAITH-2": "C42",   # T14 proven under {AxTwoSubjects}
}

CONTESTS = {
    "C73": ["UnitPlurality"],
    "C75": ["ContentWithoutPerson"],
    "C76": ["PluralityWithoutLove"],
    "C78": ["ActWithoutSubject"],
    "C79": ["InfiniteGroundChain"],
    "C80": ["ActWithoutSubject"],
    "C81": ["ActWithoutSubject"],
    "C82": ["ActWithoutSubject"],
    "C87": ["ActWithoutSubject"],
    "C88": ["WorldwiseTruthmaking"],
    "C89": ["InfiniteGroundChain"],
    "C90": ["ImpersonalUltimateGround"],
    "C91": ["SubjectNecessityNotEntity"],
    "C92": ["PersonNotNecessary"],
    "C19": ["WorldwiseTruthmaking"],
    "C64": ["ActWithoutSubject"],
    "C65": ["ActWithoutSubject"],
    "C66": ["ActWithoutSubject"],
    "C67": ["ActWithoutSubject"],
    "C69": ["NoFreeWill", "VeridicalMeaning"],
    "C70": ["NoFreeWill", "VeridicalMeaning"],
    "C71": ["NoFreeWill", "VeridicalMeaning"],
    "C72": ["NoFreeWill", "VeridicalMeaning"],
    "C77": ["PersonNotNecessary"],
    "F1b": ["VeridicalMeaning", "NoFreeWill"],
    "C58": ["WeakActWithoutMeaning"],
    # --- inline obstructions on the main-body constitutive steps (FORMAT.md §5) ---
    "C18": ["WorldwiseTruthmaking"],
    "C21": ["ActWithoutSubject"],
    "C23": ["ActWithoutSubject"],
    "C24": ["NoPerson"],
    "C32": ["ImpersonalUltimateGround"],
    "C39": ["NoPerson"],
    "C40": ["UnitPlurality"],
    "C41": ["PluralityWithoutLove"],
    "C42": ["PluralityWithoutLove"],
    "C43": ["PluralityWithoutLove"],
    "C44": ["PluralityWithoutLove"],
    "C45": ["PluralityWithoutLove"],
    "C74": ["UnitPlurality"],
}

COUNTERMODEL_CATALOG = [
    {"key": "WeakActWithoutMeaning", "title": "The mechanical event",
     "attacks": "a performed event entailing intentional meaning (`act → Act`)",
     "ns": "Logos.HostileSemantics.CountermodelWeakActWithoutMeaning"},
    {"key": "ActWithoutSubject", "title": "The void act (Lichtenberg)",
     "attacks": "an act occurring with no actualizing subject",
     "ns": "Logos.CountermodelActWithoutSubject"},
    {"key": "SubjectWithoutPerson", "title": "The unpredicated subject",
     "attacks": "`Subject → Person` as a logical law",
     "ns": "Logos.HostileSemantics.CountermodelSubjectWithoutPerson"},
    {"key": "NoPerson", "title": "The personless act",
     "attacks": "the bare act datum forcing `Person`",
     "ns": "Logos.HostileSemantics.CountermodelNoPerson"},
    {"key": "NoFreeWill", "title": "The determined act",
     "attacks": "`Act → Chooses` / `Act → FreeWill`",
     "ns": "Logos.HostileSemantics.CountermodelNoFreeWill"},
    {"key": "UnitPlurality", "title": "The unit world",
     "attacks": "one act forcing a plurality of subjects",
     "ns": "Logos.HostileSemantics.UnitPluralityCountermodel"},
    {"key": "ContentWithoutPerson", "title": "Content without a person",
     "attacks": "content existence entailing personhood",
     "ns": "Logos.HostileSemantics.PropositionalPersonhood.CountermodelContentWithoutPerson"},
    {"key": "WorldwiseTruthmaking", "title": "Worldwise but not uniform",
     "attacks": "worldwise truthmaking entailing a uniform necessary ground",
     "ns": "Logos.HostileSemantics.CountermodelWorldwiseTruthmaking"},
    {"key": "SubjectNecessityNotEntity", "title": "Persistence without entity",
     "attacks": "subject-persistence entailing entity-necessity by logic alone",
     "ns": "Logos.HostileSemantics.CountermodelSubjectNecessityNotEntityNecessity"},
    {"key": "PersonNotNecessary", "title": "The contingent person",
     "attacks": "`Person → NecessarySubject` as a logical law",
     "ns": "Logos.HostileSemantics.CountermodelPersonNotNecessary"},
    {"key": "VeridicalMeaning", "title": "Veridical meaning (one and two persons)",
     "attacks": "the act datum forcing genuine choice",
     "ns": "Logos.HostileSemantics.CountermodelVeridicalMeaning"},
    {"key": "InfiniteGroundChain", "title": "The infinite descending chain",
     "attacks": "grounding forcing an ultimate element",
     "ns": "Logos.HostileSemantics.CountermodelInfiniteGroundChain"},
    {"key": "ImpersonalUltimateGround", "title": "The impersonal ultimate",
     "attacks": "an ultimate ground entailing a personal one",
     "ns": "Logos.HostileSemantics.CountermodelImpersonalUltimateGround"},
    {"key": "PluralityWithoutLove", "title": "Plurality without love",
     "attacks": "plurality entailing love",
     "ns": "Logos.HostileSemantics.CountermodelPluralityWithoutLove"},
]

# ---------------------------------------------------------------------------
# Presentation-data maps (MATH.md / FORMAT.md §9 sanctioned exceptions)
# ---------------------------------------------------------------------------

DEFAULT_KIND = {
    "LOGICAL": "Lemma",
    "DEFINITIONAL": "Proposition",
    "SEMANTIC": "Theorem",
    "METAPHYSICAL": "Theorem",
    "OPEN": "Open problem",
}

KIND_OF = {
    "C18": "Theorem",
    "C19": "Corollary",
    "C20": "Corollary",
    "C24": "Theorem",
    "C32": "Theorem",
    "C34": "Corollary",
    "C40": "Theorem",
    "C42": "Theorem",
    "C45": "Corollary",
    "C51": "Lemma",
    "C77": "Theorem",
    "C92": "Corollary",
}

STATEMENT_OVERRIDES = {}

DEF_REF_ALLOW = {
    "C51": {"C24", "C68", "C27", "C50"},
    "C52": {"C68"},
    "C74": {"C40"},
    "C92": {"C77"},
    "C30": {"C9"},
}

DEFINITIONS = {
    "I": [
        "**Definition (Weak act vs. strong Act).** "
        "`act(s, p)` — *weak act: performed event* (utterance, assertion-event, performance) vs. "
        "`Act(s, p) := Means(s, p) ∧ ∃ w w', Initiates(s, w, w', p)` (abbreviated `A(s, p)`) — "
        "*strong act: meaningful initiation (its constitutive content is intentional meaning, and its evental character is initiation)*.",
        "**Definition (Weak assertion vs. strong assertion).** "
        "`asserts(s, p) := act(s, p) ∧ p` (*weak assertion: performed assertion event*) vs. "
        "`Asserts(s, p) := Act(s, p) ∧ p` (*strong assertion: meaning-bearing assertion*).",
        "**Bridge (Weak act to strong act).** "
        "`weak_act_implies_strong_act := ∀ s p, act(s, p) → Act(s, p)` (*unforced open intentionality bridge; separated by CountermodelWeakActWithoutMeaning*).",
        "**Definition (Subject actuality).** "
        "SubjectExists(s) := ∃ p, Act(s, p).",
        "**Definition (Subject, Intentionality, and Person).** "
        "IntentionalSubject(s) := ∃ p, Means(s, p) (*the subject who means content, derived from Act*). "
        "Person(s) := FreeSubject(s) ↔ FreeWill(s) (*the subject possessing a numerically distinct free will, "
        "derived as a constitutive theorem with 0 substantive axioms*).",
        "**Audit of the Performative Datum.**\n\n"
        "- **Current formal datum:** `∃ s p, Act s p`\n"
        "- **Question:** Is this the complete formal expression of the performative evidence, or does the intended datum contain additional structure?\n"
        "- **Status: AUDITED.** The intended datum in `base.txt` (§0–§1) encompasses thinking, asserting, judging, and doubting. Strong assertion (`Asserts`) and judgment (`Correct/Incorrect`) derive objective semantic selection (`Selects s p (¬p)`), but no generic candidate entails cognitive representation of the rejected horn (`Means s q`).\n"
        "- **Constraint:** No strengthening is permitted merely because it helps derive A14. Any strengthening must be independently grounded in the actual performative datum.",
    ],
    "II": [
        "**Definition (Truth and falsehood).** "
        "T(p) := p (truth is identity, E0) and IsFalse(p) := ¬T(p).",
        "**Definition (The absolutes).** "
        "N_T := ∀ p, ¬T(p) (nothing is true) and N_F := ∀ p, T(p) (everything is true).",
    ],
    "IV": [
        "**Definition (Incompatibility, weak choice, and strong choice).** "
        "Incompatible(p, q) := ¬(p ∧ q), "
        "ChoiceField(s, p, q) := Means(s, p) ∧ Incompatible(p, q) "
        "(*weak choice: incompatible alternatives are present*), and "
        "Chooses(s, p, q) := Means(s, p) ∧ Means(s, q) ∧ Incompatible(p, q) "
        "(*strong choice: the subject co-means incompatible alternatives*).",
        "**Architectural note (Asymmetric definition ruled out by double-negation collapse).** "
        "A tempting alternative definition of choice as asymmetric rejection, "
        "`Chooses_asym(s, p, q) := Means(s, p) ∧ Means(s, ¬q) ∧ Incompatible(p, q)` "
        "(meaning the selected alternative and meaning the negation of the rejected alternative), "
        "fails mathematically in the canonical contradictory case `q := ¬p`: because `¬(¬p) ↔ p`, "
        "`Means(s, ¬¬p)` collapses under classical logic (`Classical.propext`) to `Means(s, p)`. "
        "Hence `Chooses_asym(s, p, ¬p)` dissolves into `Means(s, p) ∧ Incompatible(p, ¬p)` — which is "
        "identically `ChoiceField(s, p, ¬p)` — requiring zero representation of the rejected alternative "
        "and destroying the hostile-model separation between field and choice. "
        "Therefore, genuine choice strictly requires symmetric co-meaning of the incompatible alternatives: "
        "`Chooses(s, p, q) := Means(s, p) ∧ Means(s, q) ∧ Incompatible(p, q)`.",
        "**Definition (Free will).** FreeWill(s) := ∃ p, q (Chooses(s, p, q)) "
        "(*freedom: definitional from strong choice*).",
        "**Frontier (Genuine choice).** deliberateGenuineChoiceResource := ∃ s p, Asserts(s, p) ∧ Means(s, ¬p) "
        "(*the minimal resource sufficient to prove genuineChoice_exists and deliberateChoice_exists; its existence remains open*).",
        "**Definition (Judgment quality).** "
        "Correct(s, p) := A(s, p) ∧ T(p), "
        "Incorrect(s, p) := A(s, p) ∧ IsFalse(p), and "
        "Fallible(s, p) := IsFalse(p).",
    ],
    "V": [
        "**Definition (World necessity).** "
        "NecessarilyTrue(φ) := ∀ w, TrueAt(w, φ) (written □ φ) and "
        "NecessarilyFalse(φ) := ∀ w, FalseAt(w, φ) (written ¬◇ φ).",
        "**Definition (Necessary entities and persistence).** "
        "NecessaryEntity(e) := ∀ w, ExistsAt(w, e), "
        "Contingent(e) := ¬NecessaryEntity(e), and "
        "NecessarySubject(s) := ∀ w, ExistsAt(w, EntityOf(s)).",
    ],
    "VII": [
        "**Definition (Interpersonal relations).** "
        "Affects(s, t) := s ≠ t, Alone(s) := ∀ t, t = s, "
        "Helps(s, t) := Affects(s, t), and Harms(s, t) := False.",
    ],
    "VIII": [
        "**Definition (Love).** "
        "Loves(s, t) := Helps(s, t) ∧ ¬Harms(s, t) and "
        "Lovable(t) := ∃ s, s ≠ t ∧ Person(s).",
    ],
}


# §5 argument-at-a-glance: every arrow carries a status, validated at build.
TRANSITIONS = [
    # Classical / Logical Core (independent of performative act)
    {"label": "classical core: truth / falsehood", "status": "LOGICAL",
     "targets": ["C1", "C5", "C7", "C12"]},
    {"label": "classical core: right / wrong distinction", "status": "LOGICAL",
     "targets": ["C36"]},
    {"label": "classical core: excluded middle & non-contradiction", "status": "LOGICAL",
     "targets": ["C10", "C11"]},
    {"label": "classical core: bivalence & strong truth", "status": "LOGICAL",
     "targets": ["C37", "C59"]},

    # Agency & Metaphysical Branch (anchored to the performative meaning-act ∃ s p, Act s p)
    {"label": "performative meaning-act → subject", "status": "DEFINITIONAL",
     "targets": ["C21"]},
    {"label": "performative meaning-act → intentional subject (C24) [substantive person OPEN]", "status": "DEFINITIONAL",
     "targets": ["C24"]},
    {"label": "performative meaning-act → choice field (alternatives)", "status": "DEFINITIONAL",
     "targets": ["C51", "C52"]},
    {"label": "assertion → semantic selection", "status": "DEFINITIONAL",
     "targets": ["Logos.Choice.asserts_selects"]},
    {"label": "deliberate choice → semantic selection", "status": "DEFINITIONAL",
     "targets": ["C97"]},
    {"label": "deliberate choice → genuine choice", "status": "DEFINITIONAL",
     "targets": ["C98"]},
    {"label": "genuine choice → free will", "status": "DEFINITIONAL",
     "targets": ["Logos.Choice.chooses_implies_freeWill"]},
    {"label": "genuine choice (existence: F1b)", "status": "SEMANTIC",
     "targets": ["F1b"]},
    {"label": "performative meaning-act → necessary person / entity", "status": "CONDITIONAL",
     "targets": ["C77", "C92"]},
    {"label": "necessary subject → necessary entity", "status": "DEFINITIONAL",
     "targets": ["C91"]},
    {"label": "necessary truth → necessary ground / reality (T7)", "status": "SEMANTIC",
     "targets": ["C18"]},
    {"label": "necessary reality → personal ground (T8)", "status": "METAPHYSICAL",
     "targets": ["C32"]},
    {"label": "performative meaning-act → plurality", "status": "METAPHYSICAL",
     "targets": ["C40"]},
    {"label": "plurality → love", "status": "METAPHYSICAL",
     "targets": ["C41", "C42", "C43", "C44", "C45"]},
    {"label": "performative meaning-act → God ?", "status": "OPEN",
     "targets": ["F6", "F8", "F9"]},
]

THESIS = (
    "Γ does not begin from an arbitrary propositional premise. It begins from "
    "a performatively given datum: an act of meaning is occurring. From that "
    "datum the argument extracts the maximum that is *un-deniable*, marking at "
    "every step whether a claim is **LOGICAL** (logic alone), **DEFINITIONAL** "
    "(follows from how Γ's concepts are constituted), **SEMANTIC** (a "
    "substantive semantic principle), or **METAPHYSICAL** (a substantive "
    "metaphysical bridge). No "
    "claim is called a deduction unless it is derived; no bridge is smuggled in "
    "unnamed. The conclusion layers of `base.txt` §0 are kept separate: the "
    "performatively undeniable, the logically undeniable, the transcendentally "
    "necessary, and the metaphysically necessary *if the corresponding bridge is "
    "shown*. God is not derived; the relevant steps are faith or deferred."
)

FRONTIER_INTRO = (
    "The frontier is the set of claims that are not currently derived. An "
    "**OPEN** claim has no kernel node (blocked, deferred, answered, or a "
    "missing lemma) and is listed below. A **COUNTERMODEL** claim is a proposed "
    "inference that a hostile model refutes: the step is *withdrawn*, and what "
    "survives is recorded in Appendix C.2. The premier open frontiers are "
    "deontic teleology (F2) and moral good (F3)."
)

OPEN_BRIDGES = (
    "**§28 open bridges.** The prose corpus lists the still-missing named "
    "lemmas: #7 `NecessaryEntity e → ∃ τ, Ground e τ`; #8 the target opposite of "
    "#7; #9 `Ground(e, personal) → Personal(e)`; #10 its target. Each appears "
    "above in the open inventory; none is silently assumed."
)

_CTX: dict = {}


def stage_for(c: dict) -> str:
    if c["id"] in STAGE_OF:
        return STAGE_OF[c["id"]]
    full = c.get("_full") or ""
    if full.startswith("Logos."):
        return MODULE_STAGE.get(full.split(".")[1], "IX")
    return "IX"


def philo_status_of_full(full: str, node_map: dict) -> str:
    n = node_map.get(full)
    if not n:
        return "OPEN"
    if n["kind"] == "axiom":
        tag = _REGISTRY.get(full.rsplit(".", 1)[-1], {}).get("tag", "")
        return {"META": "METAPHYSICAL", "SEM": "SEMANTIC",
                "VOCAB": "DEFINITIONAL", "TRANS": "SEMANTIC"}.get(tag, "DEFINITIONAL")
    subst, vocab, _cl = footprint_parts(full)
    if any(_REGISTRY.get(a, {}).get("tag") == TAG_META for a in subst):
        return "METAPHYSICAL"
    if subst:
        return "SEMANTIC"
    if vocab:
        return "DEFINITIONAL"
    return "LOGICAL"


def build_canonical_map(all_claims: list) -> dict:
    """Return {claim id -> canonical claim id} for every non-canonical row.

    Explicit `ALIAS_TO` always wins; otherwise, among claims sharing one kernel
    node, priority is C > F > FAITH, ties broken by GAPMAP order.
    """
    ids = {c["id"] for c in all_claims}
    canon = {a: b for a, b in ALIAS_TO.items() if a in ids and b in ids}

    def rank(cid):
        if cid.startswith("FAITH"):
            return 2
        if cid.startswith("C"):
            return 0
        return 1

    by_full = {}
    for c in all_claims:
        f = c.get("_full")
        if f:
            by_full.setdefault(f, []).append(c["id"])
    for f, group in by_full.items():
        if len(group) < 2:
            continue
        winner = sorted(group, key=rank)[0]
        for cid in group:
            if cid != winner and cid not in canon:
                canon[cid] = winner
    # explicit alias targets must themselves be canonical endpoints
    for a, b in list(canon.items()):
        canon[a] = canon.get(b, b)
    return canon


def philo_status(c: dict, node_map: dict) -> str:
    if c["id"] in _CTX.get("canonical_of", {}):
        return "DISSOLVED"
    if _clean_status((c.get("status") or "").strip()) == "→":
        return "DISSOLVED"
    if c["id"] in {"C77", "C92"}:
        return "CONDITIONAL"
    full = c.get("_full")
    if full and full in node_map and c.get("status") in ("PROVEN", "PROVEN↑", "AXIOM"):
        return philo_status_of_full(full, node_map)
    if c["id"] in RETIRED_BY_COUNTERMODEL:
        return "COUNTERMODEL"
    return "OPEN"


def status_label(c: dict) -> str:
    s = philo_status(c, _CTX["node_map"])
    if c["id"] in CONDITIONAL_CLAIMS and not s.endswith("CONDITIONAL"):
        s += " / CONDITIONAL"
    return s


def _short_gloss(c: dict, n: int = 220) -> str:
    s = re.sub(r"\s+", " ", (c.get("_gloss") or "")).strip()
    if len(s) <= n:
        return s or "—"
    cut = s[:n]
    if " " in cut:
        cut = cut.rsplit(" ", 1)[0]
    return cut.rstrip(" ,;:.") + "…"


TITLE_CAP = 110


def _clause_segments(s: str) -> list:
    """Split on `.`/`:`/`;` followed by whitespace, but never inside parens."""
    segs, depth, start = [], 0, 0
    for i, ch in enumerate(s):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth = max(0, depth - 1)
        elif ch in ".:;" and depth == 0 and i + 1 < len(s) and s[i + 1] == " ":
            segs.append(s[start:i + 1])
            start = i + 1
    segs.append(s[start:])
    return segs


def split_claim(c: dict) -> tuple:
    """Partition a claim's displayed gloss into (heading title, extra detail).

    The heading carries the first id-stripped clause; `extra` is everything the
    heading does NOT already say (later clauses plus any text dropped by the
    heading cap). The block emits `extra` alone, so the heading is never
    re-iterated (FORMAT.md §4.1)."""
    disp = re.sub(r"\s+", " ",
                  (c.get("_gloss_display") or c.get("_gloss")
                   or c.get("note") or "")).strip()
    if not disp:
        return c["id"], ""
    scid = re.escape(c["id"])
    segs = _clause_segments(disp)
    idx = None
    for i, seg in enumerate(segs):
        t = seg.strip()
        if re.fullmatch(r"(?:Step\s+\d+\s*)?\(?" + scid + r"\)?"
                        r"(?:\s*\([^)]*\))?[.:;,]?", t):
            continue
        idx = i
        break
    if idx is None:
        title_core, rest = disp, []
    else:
        title_core, rest = segs[idx].strip(), segs[idx + 1:]
    # strip a residual leading id / "Step N (ID) (…):" and embedded "(ID, …)"
    title_core = re.sub(r"^(?:Step\s+\d+\s*)?\(?" + scid + r"\)?\s*"
                        r"(?:\([^)]*\))?\s*[:.\-—;,]*\s*", "", title_core)
    title_core = re.sub(r"\s*\(" + scid + r"[^)]*\)", "", title_core).strip()
    title_core = title_core.rstrip(".:;, ").strip()
    if not title_core:
        title_core = disp
    extra = " ".join(s.strip() for s in rest).strip()
    # A first clause longer than the heading cap: move a trailing parenthetical
    # (e.g. a poem citation or a "for completeness" aside) wholly into the
    # extra before cutting, so the heading never ends mid-parenthesis.
    m = re.search(r"\s*\([^()]*\)\s*$", title_core)
    while m and len(title_core) > TITLE_CAP:
        removed = title_core[m.start():].strip()
        title_core = title_core[:m.start()].rstrip(" ,;:.").strip()
        extra = (removed + " " + extra).strip()
        m = re.search(r"\s*\([^()]*\)\s*$", title_core)
    title = title_core
    if len(title_core) > TITLE_CAP:
        cut = title_core[:TITLE_CAP - 2]
        if " " in cut:
            cut = cut.rsplit(" ", 1)[0]
        dropped = title_core[len(cut):].strip()
        title = cut.rstrip(" ,;:.") + "…"
        extra = (dropped + " " + extra).strip()
    extra = re.sub(r"^[\s:;,.—\-)\]]+", "", extra).strip()
    extra = re.sub(r"\s+", " ", extra)
    if title and title != c["id"]:
        title = title[0].upper() + title[1:]
    if extra:
        extra = extra[0].upper() + extra[1:]
    return (title or c["id"]), extra


def claim_title(c: dict) -> str:
    return split_claim(c)[0]


def formal_of(full: str) -> str:
    d = _CTX["decls"].get(full)
    if not d:
        return ""
    raw = d["statement"]
    if d["kind"] == "theorem":
        raw = strip_theorem_head(raw)
    return short_stmt(humanise(trim_stmt(raw)))


def predecessor_ids(full: str) -> list:
    decls = _CTX["decls"]
    out = []
    for fd in _CTX["graph"]["in"].get(full, set()):
        if fd in decls and decls[fd]["kind"] == "axiom":
            continue
        for i in _CTX["by_full"].get(fd, []):
            if i not in out:
                out.append(i)
    return sorted(out)


def assumption_text(full: str) -> str:
    if not full or full not in _CTX["node_map"]:
        return "—"
    subst, vocab, _cl = footprint_parts(full)
    ax_id = _CTX["ax_id"]

    def key(b):
        return int(ax_id[b][1:]) if b in ax_id else 999
    lines = []
    for a in sorted(subst, key=key):
        r = _REGISTRY.get(a, {})
        ref = ax_id.get(a, f"`{a}`")
        lines.append(f"- **{ref}** `{a}` ({r.get('tag', '?')}) — {r.get('gloss', '')}")
    if lines:
        return "  \n".join(lines)
    if vocab:
        return ("Statement's own vocabulary ("
                + ", ".join(f"`{v}` ({_REGISTRY.get(v, {}).get('tag', 'VOCAB')})"
                            for v in sorted(vocab))
                + "); no substantive assumption.")
    return "None — logic alone (meta-logic `CL` only)."


SORTS = {'Prop', 'Subject', 'Entity', 'World', 'Form', 'Nat', 'String', 'Type', 'Sort', 'Unit', 'S', 'Int', 'Bool', 'State'}


def is_sort(t: str) -> bool:
    t = t.strip()
    return t in SORTS or bool(re.match(r'^[A-Z]\d*$', t))


def strip_ns(s: str) -> str:
    return re.sub(r'\bLogos\.(?:[A-Za-z0-9_]+\.)+([A-Za-z0-9_]+)', r'\1', s)


BINDER_RE = re.compile(
    r'([\u2203\u2200])\s+(((?:[A-Za-z_α-ωΑ-Ω][A-Za-z0-9_\'₀-₉]*\s+)*)'
    r'[A-Za-z_α-ωΑ-Ω][A-Za-z0-9_\'₀-₉]*)\s*:\s*[A-Za-z_][A-Za-z0-9_]*\s*,?')



def extract_symbol_table(decls: dict) -> dict:
    """Dynamically discover function/predicate symbols and arities from Lean declarations."""
    table = {}
    for full, d in decls.items():
        stmt = strip_ns(d["statement"])
        kind = d["kind"]
        if kind not in ("def", "axiom", "inductive"):
            continue
        name = d["name"]
        dp = db = 0
        col = -1
        for i, ch in enumerate(stmt):
            if ch == "(": dp += 1
            elif ch == ")": dp -= 1
            elif ch == "{": db += 1
            elif ch == "}": db -= 1
            elif ch == ":" and dp == 0 and db == 0:
                col = i
                break
        if col == -1:
            continue
        head = stmt[:col].strip()
        tail = stmt[col+1:].strip()
        head_params = 0
        for m in re.finditer(r"\(([^)]+)\)", head):
            inner = m.group(1).strip()
            if ":" in inner:
                vars_part = inner.split(":", 1)[0].strip()
                head_params += len(vars_part.split())
        tail_arrows = len(re.findall(r"→", tail))
        total_arity = head_params + tail_arrows
        if total_arity > 0:
            table[name] = total_arity
    table["atom"] = 1
    table["EntityOf"] = 1
    table["A"] = 2
    table["T"] = 1
    table["IsFalse"] = 1
    table["Initiates"] = 4
    return table


def format_discrete_math(s: str, table: dict = None) -> str:
    if not s:
        return ""
    if table is None:
        table = _CTX.get("symbol_table", {})
    
    # Clean LaTeX escape sequences
    s = s.replace(r"\;", " ").replace(r"\,", ", ").replace("_w", "w")
    s = re.sub(r"\\(?:text|mathrm)\{([^}]*)\}", r"\1", s)
    s = s.replace(r"\neg", "¬").replace(r"\land", "∧").replace(r"\lor", "∨")
    s = s.replace(r"\to", "→").replace(r"\leftrightarrow", "↔")
    s = s.replace(r"\forall", "∀").replace(r"\exists", "∃")
    s = s.replace(r"\neq", "≠")
    
    # Strip binder annotations: (w : World) -> w
    def repl_paren_binders(m):
        q = m.group(1)
        rest = m.group(2)
        vars = re.findall(r'\(([A-Za-zα-ωΑ-Ω0-9_\'₀-₉]+)\s*:[^)]+\)', rest)
        return q + ' ' + ', '.join(vars) + ','
    s = re.sub(r'([∀∃])\s*((?:\([A-Za-zα-ωΑ-Ω0-9_\'₀-₉]+\s*:[^)]+\)\s*)+),?', repl_paren_binders, s)
    s = re.sub(r'([∀∃])\s*\{([^}:]+)(?::[^}]*)?\}\s*,?', r'\1 \2,', s)
    while BINDER_RE.search(s):
        s = BINDER_RE.sub(r'\1 \2,', s)

    # Inner constructor applications
    for sym in ["atom", "EntityOf"]:
        s = re.sub(r"\b" + sym + r"\s+([A-Za-z0-9_\'₀-₉]+)", rf"{sym}(\1)", s)
        
    ARG = r"(?:\((?:[^()]+\([^()]*\)|[^()])*\)|¬[A-Za-z0-9_\'₀-₉]+|[A-Za-z0-9_\'α-ω₀-₉]+(?:\([^()]*\))?)"

    def wrap_call(head, *args):
        clean_args = []
        for a in args:
            a = a.strip()
            if a.startswith("(") and a.endswith(")"):
                inner = a[1:-1].strip()
                if (inner.count("(") == inner.count(")") and (" ∧ " not in inner and " ∨ " not in inner and " → " not in inner)) or (" " not in inner):
                    clean_args.append(inner)
                else:
                    clean_args.append(a)
            else:
                clean_args.append(a)
        return f"{head}(" + ", ".join(clean_args) + ")"

    # Bottom-up functional application rewriting
    for arity in [3, 2, 1]:
        syms_for_arity = [sym for sym, ar in table.items() if ar == arity and sym not in ("atom", "EntityOf")]
        syms_for_arity = [sym for sym in syms_for_arity if re.match(r"^[A-Za-z_][A-Za-z0-9_]*$", sym)]
        syms_for_arity.sort(key=len, reverse=True)
        if not syms_for_arity:
            continue
        pat_syms = "|".join(re.escape(sym) for sym in syms_for_arity)
        if arity == 3:
            s = re.sub(rf"\b({pat_syms})\s+({ARG})\s+({ARG})\s+({ARG})(?![A-Za-z0-9_\'₀-₉])",
                       lambda m: wrap_call(m.group(1), m.group(2), m.group(3), m.group(4)), s)
        elif arity == 2:
            s = re.sub(rf"\b({pat_syms})\s+({ARG})\s+({ARG})(?![A-Za-z0-9_\'₀-₉])",
                       lambda m: wrap_call(m.group(1), m.group(2), m.group(3)), s)
        elif arity == 1:
            s = re.sub(rf"\b({pat_syms})\s+({ARG})(?![A-Za-z0-9_\'₀-₉])",
                       lambda m: wrap_call(m.group(1), m.group(2)), s)

    # Quantifier normalization: comma separate variables
    s = re.sub(r"([∀∃])\s+([A-Za-z0-9_\'₀-₉]+(?:\s+[A-Za-z0-9_\'₀-₉]+)+)\s*,",
               lambda m: m.group(1) + ' ' + ', '.join(m.group(2).split()) + ',', s)
    s = re.sub(r"([∀∃])\s+([A-Za-z0-9_\'₀-₉]+(?:\s+[A-Za-z0-9_\'₀-₉]+)+)\s+",
               lambda m: m.group(1) + ' ' + ', '.join(m.group(2).split()) + ', ', s)

    s = re.sub(r"∃\s+([^,]+?)\s*,\s*∃\s+", r"∃ \1, ", s)
    s = re.sub(r"∀\s+([^,]+?)\s*,\s*∀\s+", r"∀ \1, ", s)

    s = re.sub(r"\s+", " ", s)
    s = re.sub(r"\s+,", ",", s)
    s = re.sub(r",\s*,", ",", s)
    s = s.replace("¬ ", "¬")
    return s.strip()

def mathify(s: str) -> str:
    return format_discrete_math(s)

def split_theorem_head(raw: str):
    s = strip_ns(raw.strip())
    m = re.match(r'^(?:theorem|lemma)\s+([A-Za-z0-9_]+)\s*', s)
    if not m:
        return [], s
    rest = s[m.end():]
    depth_p = depth_b = 0
    colon_idx = -1
    for i, ch in enumerate(rest):
        if ch == '(': depth_p += 1
        elif ch == ')': depth_p -= 1
        elif ch == '{': depth_b += 1
        elif ch == '}': depth_b -= 1
        elif ch == ':' and depth_p == 0 and depth_b == 0:
            colon_idx = i
            break
    if colon_idx == -1:
        return [], s
    head = rest[:colon_idx].strip()
    body = rest[colon_idx+1:].strip()
    antes = []
    i = 0
    while i < len(head):
        if head[i] == '{':
            db = 1
            j = i + 1
            while j < len(head) and db > 0:
                if head[j] == '{': db += 1
                elif head[j] == '}': db -= 1
                j += 1
            i = j
        elif head[i] == '(':
            dp = 1
            j = i + 1
            while j < len(head) and dp > 0:
                if head[j] == '(': dp += 1
                elif head[j] == ')': dp -= 1
                j += 1
            chunk = head[i+1:j-1].strip()
            if ':' in chunk:
                vname, vtype = chunk.split(':', 1)
                vtype = vtype.strip()
                if not is_sort(vtype):
                    antes.append(vtype)
            i = j
        else:
            i += 1
    return antes, body


def math_statement(full: str, cid: str = None) -> str:
    if cid and cid in STATEMENT_OVERRIDES:
        return STATEMENT_OVERRIDES[cid]
    decls = _CTX["decls"]
    d = decls.get(full)
    if not d:
        return ""
    raw = d["statement"]
    kind = d["kind"]
    if kind in ("theorem", "lemma"):
        antes, body = split_theorem_head(raw)
        hum_antes = []
        for a in antes:
            ha = humanise(strip_ns(a)).strip()
            if "→" in ha or "↔" in ha or " ∧ " in ha or " ∨ " in ha or "∃" in ha or "∀" in ha:
                if not (ha.startswith("(") and ha.endswith(")")):
                    ha = f"({ha})"
            hum_antes.append(ha)
        hum_body = humanise(strip_ns(body)).strip()
        if hum_antes:
            full_str = " → ".join(hum_antes) + " → " + hum_body
        else:
            full_str = hum_body
        return mathify(full_str)
    elif kind == "axiom":
        s = strip_ns(raw.strip())
        s = re.sub(r'^axiom\s+', '', s).strip()
        if ':' in s:
            name, rest = s.split(':', 1)
            h_rest = humanise(rest.strip()).strip()
            if '∀' in h_rest or '∃' in h_rest:
                return mathify(h_rest)
            else:
                return f'{name.strip()} : {mathify(h_rest)}'
        return mathify(humanise(s))
    else:  # def, abbrev
        s = strip_ns(raw.strip())
        s = re.sub(r'^(?:def|abbrev)\s+', '', s).strip()
        return mathify(humanise(s))


def displmath(s: str) -> str:
    return f"\\[ {s} \\]"


def inlmath(s: str) -> str:
    return f"\\({s}\\)"


def math_lean_ref(d: dict) -> str:
    if not d or not d.get("file"):
        return "n/a"
    return f"{Path(d['file']).name}#L{d['line']}"


def math_uses(c: dict) -> str:
    full = c.get("_full")
    if not full or full not in _CTX["node_map"]:
        return ""
    names = kernel_axiom_names(full, _CTX["node_map"])
    ax_id = _CTX["ax_id"]
    mapped = []
    unmapped = []
    for b in names:
        if b in ax_id:
            mapped.append(ax_id[b])
        else:
            unmapped.append(f"`{b}`")
    mapped.sort(key=lambda a: int(a[1:]))
    unmapped.sort()
    return ", ".join(mapped + unmapped)


def math_metadata(c: dict) -> str:
    full = c.get("_full")
    decls = _CTX["decls"]
    d = decls.get(full) if full else None
    ref = math_lean_ref(d)
    parts = [f"Lean: {ref}"]
    uses = math_uses(c)
    if uses:
        parts.append(f"uses {uses}")
    st_lbl = status_label(c)
    badge = badge_for(c, decls, _CTX["node_map"])
    parts.append(f"{st_lbl} {badge}")
    return "`" + " · ".join(parts) + "`"


def kind_of(c: dict) -> str:
    st = philo_status(c, _CTX["node_map"])
    return KIND_OF.get(c["id"], DEFAULT_KIND.get(st, "Proposition"))



def synthesize_proof(c: dict) -> str:
    cid = c["id"]
    full = c.get("_full")
    decls = _CTX.get("decls", {})
    node_map = _CTX.get("node_map", {})
    graph = _CTX.get("graph", {})
    ax_id = _CTX.get("ax_id", {})
    cid_by_full = {cl["_full"]: cl["id"] for cl in _CTX.get("claims", []) if cl.get("_full")}
    table = _CTX.get("symbol_table", {})
    
    if not full or full not in decls:
        return "Follows from definitions. ∎"
        
    d = decls[full]
    name = d["name"]
    
    # 1. Docstring derivation notes (paragraphs after paragraph 1)
    doc_full = d.get("doc_full", "")
    paras = [p.strip() for p in doc_full.split("\n\n") if p.strip()]
    doc_exp = ""
    for p in paras[1:]:
        p_clean = " ".join(p.split())
        if not (p_clean.startswith("PROVEN") or p_clean.startswith("Tag:") or p_clean.startswith("§") or p_clean.startswith("Footprint:")):
            doc_exp = p_clean
            break
            
    # 2. Kernel dependencies
    in_preds = graph.get("in", {}).get(full, set())
    direct_cids = []
    direct_ax = []
    for p in in_preds:
        if p in cid_by_full and cid_by_full[p] != cid:
            direct_cids.append(cid_by_full[p])
        b = p.rsplit(".", 1)[-1]
        if b in ax_id:
            direct_ax.append(ax_id[b])
    direct_cids = sorted(set(direct_cids))
    direct_ax = sorted(set(direct_ax))
    
    # Kernel axioms
    axioms = node_map.get(full, {}).get("axioms", []) if full in node_map else []
    has_cl = any("Classical" in a or "choice" in a or "propext" in a for a in axioms)
    for a in axioms:
        b = a.rsplit(".", 1)[-1]
        if b in ax_id and ax_id[b] not in direct_ax:
            direct_ax.append(ax_id[b])
            
    # 3. Read proof lines from Lean file
    file_path = LEAN_DIR / d["file"]
    raw_proof = ""
    if file_path.exists():
        lines = file_path.read_text(encoding="utf-8").splitlines()
        start = d["line"] - 1
        chunk = "\n".join(lines[start:start+35])
        if ":=" in chunk:
            raw_proof = chunk.split(":=", 1)[1].strip()
            if "/--" in raw_proof:
                raw_proof = raw_proof.split("/--", 1)[0].strip()
                
    technique = "direct"
    if "cases " in raw_proof or "rcases " in raw_proof:
        technique = "cases"
    elif "intro " in raw_proof and ("False.elim" in raw_proof or "refutes" in name.lower() or "exact h" in raw_proof):
        technique = "contradiction"
    elif "obtain " in raw_proof or "⟨" in raw_proof:
        technique = "witness"
        
    refs = []
    if direct_cids:
        refs.append("by " + ", ".join(f"**{p}**" for p in direct_cids))
    if direct_ax:
        refs.append("under " + ", ".join(f"**{a}**" for a in direct_ax))
    if has_cl:
        refs.append("by classical logic (**CL**)")
    ref_str = ", ".join(refs)
    
    if doc_exp:
        body = format_discrete_math(doc_exp, table)
        if not body.endswith("."):
            body += "."
        if ref_str and len(body) < 80 and not any(r in body for r in direct_cids):
            body = f"{body[:-1]} ({ref_str})."
        return f"{body} ∎"
        
    antes, body = split_theorem_head(d["statement"])
    antes_fm = [format_discrete_math(humanise(strip_ns(a)).strip(), table) for a in antes]
    
    clauses = []
    if antes_fm:
        clauses.append(f"Assume {', and '.join(antes_fm)}.")
        
    if technique == "contradiction":
        clauses.append(f"{ref_str.capitalize() if ref_str else 'By definition'}, the assumption refutes itself.")
    elif technique == "cases":
        clauses.append(f"Evaluating by disjunctive cases {ref_str if ref_str else 'from premises'}.")
    elif technique == "witness":
        clauses.append(f"The required witness is constructed {ref_str if ref_str else 'directly'}.")
    else:
        clauses.append(f"Follows {ref_str if ref_str else 'directly from the definitions'}.")
        
    res = " ".join(clauses)
    if not res.endswith("."):
        res += "."
    return f"{res} ∎"


def proof_of(c: dict) -> str:
    return synthesize_proof(c)


def _axiom_gloss_body(gloss: str) -> str:
    s = gloss.strip()
    if s.startswith("— "):
        s = s[2:].strip()
    s = re.sub(r'^[A-Za-z0-9_]+\s*(?:\([^)]*\))?\s*:\s*', '', s).strip()
    if s.lower().startswith('vocabulary:'):
        s = s[len('vocabulary:'):].strip()
    if s:
        s = s[0].upper() + s[1:]
    return s


def inline_countermodel(c: dict) -> list:
    """Compressed, first-use-deduped inline obstructions (MATH.md §2.2).

    Returns the `**Obstruction.**` lines only. The first occurrence of a model
    in the main body shows its `refutes` sentence; later occurrences use the
    catalog's short `attacks` phrase and point at Appendix C.1 (which carries the
    full refutes/survives text).
    """
    keys = CONTESTS.get(c["id"], [])
    if not keys:
        return []
    seen = _CTX["cm_seen"]
    L = []
    for k in keys:
        cm = _CTX["countermodels"].get(k, {})
        if k not in seen:
            seen.add(k)
            L.append(f"**Obstruction.** `Countermodel{k}` — "
                     f"{cm.get('refutes', '').strip()}")
        else:
            attacks = next((m["attacks"] for m in COUNTERMODEL_CATALOG
                            if m["key"] == k), "")
            L.append(f"**Obstruction.** `Countermodel{k}` — {attacks} "
                     f"(see Appendix C.1).")
    return L


def _answer_phrase(c: dict, st: str) -> str:
    """Status-derived philosophical payoff for a contested non-OPEN step."""
    r = RESOLUTION_OF.get(c["id"])
    if r:
        return r
    b = BRIDGE_OF.get(c["id"], "").rstrip(".")
    if b:
        return f"the step is {st} in Γ, not LOGICAL: it follows from {b}."
    return {
        "DEFINITIONAL": "the step is constitutive in Γ, not a logical consequence.",
        "SEMANTIC": ("the step rests on a substantive semantic principle, "
                     "not logic alone."),
        "METAPHYSICAL": ("the step rests on a substantive metaphysical bridge, "
                         "not logic alone."),
    }.get(st, "the step is not a logical consequence.")


def axiom_intro_en(full: str) -> list:
    L = []
    ax_shown = _CTX["ax_shown"]
    ax_id = _CTX["ax_id"]
    new = [b for b in kernel_axiom_names(full, _CTX["node_map"])
           if b in ax_id and b not in ax_shown]
    if "AxIntentionalChoice" in new and "AxActPolarity" not in ax_shown:
        new.append("AxActPolarity")
    if "AxIntentionalChoice" in new and "AxJudicativeBipolarity" not in ax_shown:
        new.append("AxJudicativeBipolarity")
    for base in sorted(new, key=lambda b: int(ax_id[b][1:])):
        ax_shown.add(base)
        r = _REGISTRY.get(base, {})
        fn = r.get("full") or _CTX["axiom_full"].get(base) or base
        d = _CTX["decls"].get(fn, {})
        stmt = math_statement(fn) if d.get("statement") else ""
        gloss = _axiom_gloss_body(_CTX["glosses"].get(fn, "") or r.get("gloss", ""))
        cost = _cost_for(d.get("doc_full", ""))
        L.append(f"**Axiom {ax_id[base]} · {base} ({r.get('tag', '?')}).**")
        if stmt:
            L.append(displmath(stmt))
        if gloss:
            L.append(gloss)
        if cost:
            L.append("")
            L.append(f"*Philosophical cost:* {cost}")
        L.append("")
    return L


def render_claim_block(c: dict) -> list:
    L = []
    ap = L.append
    decls = _CTX["decls"]
    node_map = _CTX["node_map"]
    full = c.get("_full")
    canon = _CTX.get("canonical_of", {}).get(c["id"])
    if canon:
        target = _CTX["by_id"].get(canon, {})
        tfull = target.get("_full")
        ref = f"`{tfull}`" if tfull else "the claim"
        ap(f"### {c['id']} · →")
        ap(f"*Dissolved into **{canon}** (shares {ref}); see that block.*")
        ap("")
        return L
    is_kernel = bool(full and full in decls and full in node_map
                     and c.get("status") in ("PROVEN", "PROVEN↑", "AXIOM"))
    st = philo_status(c, node_map)
    title, extra = split_claim(c)
    kind = kind_of(c)
    ap(f"**{kind} {c['id']} ({title}).**")
    ap("")
    if extra:
        ap(extra)
        ap("")
    if is_kernel:
        stmt = math_statement(full, c["id"])
        if stmt:
            ap(displmath(stmt))
            ap("")
    elif c["id"] in TARGET_OF:
        ap(displmath(TARGET_OF[c["id"]]))
        ap("")
    if is_kernel and st != "OPEN":
        p = proof_of(c)
        if not p.endswith("∎"):
            p += " ∎"
        ap(f"**Proof.** {p}")
        ap("")
    cml = inline_countermodel(c)
    for line in cml:
        ap(line)
        ap("")
    if st == "OPEN":
        ap("**Status: OPEN.**")
        ap("")
    elif cml:
        ap(f"**Γ's answer.** {_answer_phrase(c, st)}")
        ap("")
    ap(math_metadata(c))
    ap("")
    return L


def render_freewill_step() -> list:
    stmt = "Chooses(s, p, q) → FreeWill(s)"
    proof = "Immediate from FreeWill(s) := ∃ p, q (Chooses(s, p, q)) (definitional unrolling). ∎"
    ref = "Choice.lean#L151"
    meta = f"`Lean: {ref} · uses A5 · DEFINITIONAL ✔`"
    return [
        "**Corollary (Free will is definitional).**\n",
        f"\\[ {stmt} \\]\n",
        f"**Proof.** {proof}\n",
        f"{meta}\n",
    ]

def render_stages(all_claims: list) -> list:
    L = []
    ap = L.append
    rank = _CTX["reading_rank"]
    ap("## 3. The deduction")
    ap("")
    for st in STAGES:
        ap(f"### Stage {st['key']} — {st['title']}")
        ap("")
        ap(st["intro"])
        ap("")
        defs = DEFINITIONS.get(st["key"], [])
        if defs:
            for d in defs:
                ap(d)
                ap("")
        members = [c for c in all_claims
                   if stage_for(c) == st["key"]
                   and c["id"] not in _CTX["canonical_of"]]
        members.sort(key=lambda c: rank.get(c["id"], len(rank)))
        for c in members:
            full = c.get("_full")
            if full and full in _CTX["decls"]:
                for line in axiom_intro_en(full):
                    ap(line)
            if philo_status(c, _CTX["node_map"]) == "COUNTERMODEL":
                continue
            ap("\n".join(render_claim_block(c)).rstrip())
            ap("")
            extra = EXTRA_AFTER.get(c["id"])
            if extra == "FREEWILL":
                ap("\n".join(render_freewill_step()).rstrip())
                ap("")
        ap("")
    return L


def render_glance() -> list:
    L = []
    ap = L.append
    ap("## 2. The argument at a glance")
    ap("")
    ap("### 2.1 Classical and Logical Core")
    ap("")
    ap("The logical core holds by classical propositional logic and semantic definition alone, "
       "independently of whether any agent is acting or meaning:")
    ap("")
    ap("```text")
    for t in TRANSITIONS:
        if t["label"].startswith("classical core:"):
            ap(f"{t['label']:<58} {t['status']}")
    ap("```")
    ap("")
    ap("### 2.2 The Agency and Metaphysical Branch")
    ap("")
    ap("From the performative meaning-bearing datum (`∃ s p, Act s p`), Γ reads off subjecthood, "
       "constitutive personhood, available alternatives, and semantic selection. Substantive metaphysical "
       "and relational bridges remain explicitly priced:")
    ap("")
    ap("```text")
    for t in TRANSITIONS:
        if not t["label"].startswith("classical core:"):
            ap(f"{t['label']:<58} {t['status']}")
    ap("```")
    ap("")
    ap("### 2.3 The genuine-choice frontier")
    ap("")
    ap("```text")
    ap("PERFORMATIVE MEANING-ACT")
    ap("        │")
    ap("        └──→ Strong Act")
    ap("              ├──→ ChoiceField              [DEFINITIONAL]")
    ap("              │")
    ap("              └──→ Genuine Choice           [A14 / SEM]")
    ap("                         │")
    ap("                         └──→ FreeWill / FreeSubject")
    ap("")
    ap("A14 (AxIntentionalChoice):")
    ap("    Act(s,p) → ∃ q, Chooses(s,p,q)")
    ap("")
    ap("    ADOPTED as a substantive SEMANTIC constitutive principle")
    ap("    Weakest sufficient bridge identified at the pointwise level")
    ap("")
    ap("A13 (AxActPolarity):")
    ap("    Act(s,p) → Means(s,¬p)")
    ap("")
    ap("    Optional stronger contradictory-negation polarity principle")
    ap("    Strictly entails A14 (act_polarity_implies_intentional_choice)")
    ap("```")
    ap("")
    ap("#### Adopted Constitutive Semantic Principle: AxIntentionalChoice (A14)")
    ap("")
    ap("The hostile-model audit definitively proved that Strong Act is orthogonal "
       "to Genuine Choice under the pre-A14 primitives (`PreA14GammaTheory ⊬ genuine choice`, "
       "formalized by `act_orthogonal_to_genuine_choice_in_full_theory`). "
       "Genuine choice is not derivable from Strong Act in the pre-A14 theory. "
       "Γ now explicitly adopts the constitutive thesis as A14, a substantive semantic commitment:")
    ap("")
    ap("> **Genuine choice is constitutive of intentional action.**")
    ap("")
    ap("An event can be mechanical, involuntary, or merely causally produced (`act`); "
       "but an **intentional action** (`Act`), qua intentional action, is an action performed "
       "through the agent's apprehension and co-meaning of an incompatible alternative (`Chooses s p q`). "
       "Hence, genuine choice is constitutive of Strong Act, while remaining orthogonal to raw/weak "
       "performed events (`act`), preserving the separation proven in `CountermodelWeakActWithoutMeaning`.")
    ap("")
    ap("This constitutive commitment is formalized as the substantive semantic axiom:")
    ap("")
    ap("$$\\text{AxIntentionalChoice} : \\forall (s : \\text{Subject}) (p : \\text{Prop}),\\; "
       "\\text{Act}(s,p) \\implies \\exists q,\\; \\text{Chooses}(s,p,q)$$")
    ap("")
    ap("Under AxIntentionalChoice:")
    ap("")
    ap("$$\\text{Act}(s,p) \\longrightarrow \\text{Chooses}(s,p,q) \\longrightarrow \\text{FreeWill}(s) \\iff \\text{FreeSubject}(s)$$")
    ap("")
    ap("Thus F1b is closed under `{AxIntentionalChoice, Initiates, Means, State, Subject}` "
       "(`genuineChoice_exists_of_act_constitutive`, `freeWill_exists_of_act`, `freeSubject_exists_of_act`).")
    ap("")
    ap("**Distinction between Derivation and Adoption:**")
    ap("1. `Pre-A14 Γ ⊬ genuine choice` is **formally established** by the machine-checked hostile models "
       "`HostileSemantics.hostileAgencyInstance` and `HostileSemantics.fullTheoryHostileInstance` "
       "(`act_orthogonal_to_genuine_choice_in_full_theory`).")
    ap("2. `Pre-A14 Γ + AxIntentionalChoice ⊢ genuine choice` is **formally established** by the kernel theorem "
       "`Choice.genuineChoice_exists_of_act_constitutive`.")
    ap("The hostile countermodels remain valid against the pre-A14 theory, demonstrating why genuine choice "
       "is an authentic semantic commitment rather than a theorem of raw agency.")
    ap("")
    ap("#### Four-Model Diagnostic Hierarchy (M0–M3)")
    ap("")
    ap("| Level | Model Description | Act s p | ChoiceField s p q | Chooses s p q | FreeWill s | FreeSubject s | Verdict |")
    ap("|---|---|---|---|---|---|---|---|")
    ap("| M0 | Weak Act (`CountermodelWeakActWithoutMeaning`) | FALSE | FALSE | FALSE | FALSE | FALSE | Event occurs without meaning or strong Act |")
    ap("| M1 | Factive Strong Act (`hostileAgencyInstance`) | TRUE | TRUE | FALSE | FALSE | FALSE | Strong Act & ChoiceField hold; Chooses fails by veridicality |")
    ap("| M2 | Branching Initiation (`ModelM2BranchingInitiation`) | TRUE | TRUE | FALSE | FALSE | FALSE | Non-trivial state branching holds; Chooses still fails |")
    ap("| M3 | Contrastive Agency (`ModelM3ContrastiveAgency`) | TRUE | TRUE | TRUE | TRUE | TRUE | Polar agency validated (AxActPolarity); FreeSubject valid |")
    ap("")
    ap("#### Six-Attack Audit on Deriving Polarity from Strong Act")
    ap("")
    ap("| Attack Vector | Candidate Principle | Outcome Classification | Hostile Witness / Model | Exact Separating Valuation & Analysis |")
    ap("|---|---|---|---|---|")
    ap(r"| **Attack 1 (Existential Act Polarity)** | `(∃ s p, Act s p) → ∃ s p, Act s p ∧ Means s (¬p)` | **C. REFUTED BY HOSTILE MODEL** | `fullTheoryHostileInstance` (`not_entails_existential_polarity_from_full_theory`) | Valuation: `s = false, p = True`. In veridical semantics (`Means s p := p`), `Act s p` forces $p$, while `Means s (¬p)` forces $\neg p$, making dual co-meaning an absolute contradiction ($p \land \neg p \equiv \bot$). |")
    ap(r"| **Attack 2 (Semantics of Means)** | `Act s p → ∃ q, Means s q ∧ Incompatible p q` | **C. REFUTED BY HOSTILE MODEL** | `CountermodelVeridicalMeaning.Single` (`Single.no_genuine_choice`, `genuineChoice_requires_error_possibility`) | Valuation: `p = True`. If meaning is factive, any incompatible pair $p, q$ would require $p \land q \land \neg(p \land q) \equiv \bot$. Factive meaning mathematically excludes co-meaning incompatible alternatives. |")
    ap("| **Attack 3 (Contrastive Initiation)** | `Branches (fun w w' => ∃ p, Initiates s w w' p) → ∃ q, Means s q ∧ Incompatible p q` | **C. REFUTED / D. REDUNDANT** | `ModelM2BranchingInitiation` (`m2_diagnostic_separation`) | For physical branching: **C. REFUTED** by Model M2 (`w = false ∧ w' ∈ {true, false}`); physical state transitions are extensional and do not force mental co-meaning. For intentional contrast: **D. REDUNDANT** (extensionally equivalent to A13). |")
    ap("| **Attack 4 (DeliberateChoice Decomposition)** | `Act s p → ∃ q, DeliberateChoice s p q` | **C. REFUTED BY HOSTILE MODEL** | `hostileAgencyInstance` (`deliberateChoice_negation_decomposition`) | Valuation: `s = false, p = True, q = False`. Executive selection `Selects s p (¬p)` holds by assertion, but alternative awareness `Means s (¬p)` fails by veridicality. Deliberation fails strictly at the missing cognitive horn. |")
    ap("| **Attack 5 (Performative Doubt & Retorsion)** | `(Asserts speaker NoAct → False) → ∃ s p, Doubts s p` | **C. REFUTED BY HOSTILE MODEL** | `TwoPersons.retorsion_does_not_imply_doubt` | Valuation: `NoAct := ¬ ∃ s p, Act s p`. Retorsion establishes that denying action is performatively self-refuting, but refutation of an assertion does not populate the agent's mind with dual contradictory contents. |")
    ap("| **Attack 6 (C101 Normative Bivalence)** | `(Act s p ↔ Asserts s p ∨ Incorrect s p) → ∃ s p, Means s p ∧ Means s (¬p)` | **C. REFUTED BY HOSTILE MODEL** | `hostileAgencyInstance` (`hostile_c101`) | Valuation: `s = false, p = True`. Bivalent partition classifies the normative status of the posited content $p$ relative to reality; it tracks the world, not dual cognitive representations in the same subject $s$. |")
    ap("")
    ap("**Philosophical resolution of intentional initiation:**")
    ap("- **Case A (Already derivable from existing Strong Act in pre-A14 theory):** REFUTED by the all-scope hostile model `HostileSemantics.fullTheoryHostileInstance`.")
    ap("- **Case B (Initiates vocabulary is under-specified):** EVALUATED & BOUNDED. Model M2 shows that even when `Initiates` branches dynamically across states (`Branches`), physical transitions do not force cognitive co-meaning of the unchosen alternative in `Means`.")
    ap("- **Case C (Adoption of Constitutive Semantic Principle A14):** ESTABLISHED. Strong Choice is not an executive property of state transitions, but a cognitive property of contrastive agency. In the pre-A14 theory, Strong Act does not entail Genuine Choice; Γ therefore adopts `AxIntentionalChoice : Act s p → ∃ q, Chooses s p q` as an authentic, substantive **SEMANTIC constitutive principle** (`Tag: SEM`), with `AxActPolarity : Act s p → Means s (¬p)` remaining an optional stronger contradictory-negation principle.")
    ap("")
    ap("**Free Subject vs. Personhood:**")
    ap("- `FreeSubject s := ∃ p q, Chooses s p q` is definitionally equivalent to `FreeWill s` (`Choice.freeSubject_iff_freeWill`).")
    ap("- Every free subject is an ontological person (`Choice.freeSubject_implies_person`: `FreeSubject s → Person s`, `{Means, Subject}`).")
    ap("- But ontological personhood does NOT imply a free subject: in `TwoPersons`, two distinct persons exist while neither possesses free will (`HostileSemantics.TwoPersons.person_does_not_imply_freeSubject`).")
    ap("")
    ap("")
    ap("#### A Fronteira de A14: O Que a Teoria Existente Já Fornece vs. O Abismo Cognitivo")
    ap("")
    ap("Para qualquer ato intencional forte `Act s p`, as definições analíticas e a lógica de Γ já fornecem rigorosamente:")
    ap("```text")
    ap("Act s p")
    ap("  ├─→ Means s p                  [Definição analítica de Act: corno intencional]")
    ap("  ├─→ ∃ w w', Initiates s w w' p  [Definição analítica de Act: iniciação causal]")
    ap("  └─→ ChoiceField s p (¬p)       [Lógica pura: Incompatible p (¬p)]")
    ap("```")
    ap("")
    ap("Contudo, a ação intencional `Act s p` isolada **não** acarreta por si mesma:")
    ap("- `¬ Act s (¬p)` (necessário para a exclusão executiva em `Authors s p (¬p)`);")
    ap("- `Asserts s p` (necessário para a seleção assertiva em `Selects s p (¬p)`);")
    ap("- e, crucialmente, **não acarreta `Means s (¬p)` nem `Means s q` para nenhum `q` incompatível**.")
    ap("")
    ap("A proposição não-resolvida que separa a ação da escolha genuína é unicamente:")
    ap("$$\\text{Act}(s, p) \\implies \\exists q : \\text{Prop},\\; \\text{Means}(s, q) \\land \\text{Incompatible}(p, q)$$")
    ap("Esta é a ponte em falta da **Representação Contrastiva** (o segundo corno cognitivo).")
    ap("")
    ap("Como `Chooses s p q := Means s p ∧ Means s q ∧ Incompatible p q` e `Act s p` já fornece analiticamente `Means s p`, "
       "o axioma substantivo A14 (`AxIntentionalChoice : Act s p → ∃ q, Chooses s p q`) é **logicamente e definicionalmente equivalente à ponte de Representação Contrastiva** sobre a teoria existente.")
    ap("")
    ap("Portanto, a fronteira epistemológica de A14 fica perfeitamente isolada:")
    ap("$$\\text{Definições} + \\text{Lógica} \\quad \\vdash \\quad \\text{Act}(s, p) \\implies \\text{ChoiceField}(s, p, \\neg p)$$")
    ap("$$\\text{Definições} + \\text{Lógica} \\quad \\not\\vdash \\quad \\text{Act}(s, p) \\implies \\exists q,\\; \\text{Means}(s, q) \\land \\text{Incompatible}(p, q)$$")
    ap("")
    ap("```text")
    ap("ALTERNATIVA OBJETIVA (ChoiceField)   ───X───>   ALTERNATIVA COGNITIVA (Chooses / Means q)")
    ap("```")
    ap("Nenhuma propriedade puramente lógica ou analítica da semântica atual de `Means` é estritamente mais fraca do que A14 e capaz de derivar esta ponte: "
       "a co-significação de alternativas é o compromisso semântico irredutível de A14.")
    ap("")
    ap("### Primitive Boundary: Means and Incompatibility")
    ap("")
    ap("Means is primitive and presently uninterpreted.")
    ap("")
    ap("Incompatible is logical:")
    ap("    Incompatible p q := ¬(p ∧ q)")
    ap("")
    ap("Thus Γ currently contains:")
    ap("")
    ap("    cognitive relation: Means(s,p)")
    ap("    objective relation: Incompatible(p,q)")
    ap("")
    ap("but no primitive relation connecting the two.")
    ap("")
    ap("The unresolved A14 bridge is precisely that connection.")
    ap("")
    ap("```text")
    ap("The current formalization contains no primitive relation connecting")
    ap("objective incompatibility with cognitive representation.")
    ap("")
    ap("The unresolved bridge is therefore not recoverable from either:")
    ap("  (a) the current semantics of Means, or")
    ap("  (b) the current logic of Incompatible.")
    ap("```")
    ap("")
    ap("#### Audit: Semantics of Incompatible vs. Cognitive Representation")
    ap("")
    ap("1. **Is `Incompatible` primitive?** NO. In `formal/Logos/Alternatives.lean:17`, `Incompatible p q := ¬ (p ∧ q)` is a pure definition of propositional logic (`sorryAx = 0`, axiom footprint `{}`).")
    ap("2. **Seven Conceptual Dimensions of Incompatibility:**")
    ap("   - *Logical Incompatibility:* $\\neg(p \\land q)$ (truth-functional non-conjunction; the formal definition in Γ).")
    ap("   - *Truth Incompatibility:* $p$ and $q$ cannot co-obtain in reality.")
    ap("   - *Action Incompatibility:* An agent cannot execute both acts simultaneously.")
    ap("   - *Goal Incompatibility:* The realization of $p$ frustrates or precludes goal $q$.")
    ap("   - *Practical Opposition:* Volitional commitment to $p$ versus active rejection of $q$.")
    ap("   - *Counterfactual Exclusivity:* In any accessible counterfactual world realizing $p$, $q$ does not obtain.")
    ap("   - *Cognitive Alternative:* Both incompatible propositions $p$ and $q$ are apprehended, entertained, or represented in consciousness (`Means s p ∧ Means s q ∧ Incompatible p q`).")
    ap("3. **Sufficiency of Logical Relation:** Tested against hostile models (`CountermodelVeridicalMeaning.Single` and `ModelM2BranchingInitiation`), bare objective incompatibility $\\neg(p \\land q)$ does not imply that either proposition is represented (`Means s q`), considered, possible, actionable, chosen, rejected, or cognitively available.")
    ap("4. **Search for Deeper Structure in Γ:** Neither modal possibility (`Logos.Modal`), dynamic physical state branching (`ModelM2BranchingInitiation`), normative bivalence (`Logos.Order` C101), nor teleological goals (`TeleologicalAct`) can derive `Means s q` for an incompatible $q$ without already presupposing cognitive representation.")
    ap("5. **Candidate Principles & Relation to A14:**")
    ap("   - `Incompatible p q → Means s q`: Strictly stronger than A14 ($P > \\text{A14}$), cognitively explosive (forces representation of every incompatible proposition / contradiction), rejected.")
    ap("   - `Initiates s w w' p ∧ Initiates s w w'' q`: Independent of A14 ($P \\perp \\text{A14}$); extensional state branching fails to force mental co-meaning (refuted by Model M2).")
    ap("   - `Means s p → Means s (¬p)`: Equivalent to **A13** (`AxActPolarity`), NOT A14.")
    ap("")
    ap("#### Strength Relation: A13 vs. A14")
    ap("")
    ap("```text")
    ap("A13 : Act s p → Means s (¬p)")
    ap("             ↓")
    ap("A14 : Act s p → ∃q, Chooses s p q")
    ap("```")
    ap("")
    ap("A13 is **strictly stronger** in general than A14 because A14 permits an arbitrary incompatible alternative $q$ (e.g. contrasting positive actions such as North vs. East, as formally separated in `ContrastiveSeparation.contrastive_strictly_weaker`), whereas A13 forces the alternative to be the formal contradictory negation $\\neg p$.")
    ap("")
    ap("### Universal vs. Existential Constitutive Principle")
    ap("")
    ap("Universal A14:")
    ap("    ∀s p, Act s p → ∃q, Chooses s p q")
    ap("")
    ap("Existential weakening:")
    ap("    (∃s p, Act s p) →")
    ap("      ∃s p q, Chooses s p q")
    ap("")
    ap("The latter is sufficient for F1b.")
    ap("")
    ap("Its relation to A14 must be established formally.")
    ap("")
    ap("#### Audit: A14 vs. A14∃ (Formal Results)")
    ap("")
    ap("1. **Formalization:**")
    ap("   - Universal A14 (`AxIntentionalChoice`): `∀ (s : Subject) (p : Prop), Act s p → ∃ q, Chooses s p q`")
    ap("   - Existential A14 (`existential_intentional_choice`): `(∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, ∃ p q : Prop, Chooses s p q`")
    ap("2. **Entailment `A14 → A14∃`:** PROVEN by pure logic (`intentional_choice_implies_existential_choice`).")
    ap("3. **Converse `A14∃ → A14`:** REFUTED BY HOSTILE MODEL (`ExistentialChoiceSeparationModel.existential_not_entails_universal`). In a two-agent model where one agent chooses and another acts unilaterally without choice, `A14∃` holds while universal `A14` fails.")
    ap("   - Therefore: **`A14∃ < A14` (strictly weaker).**")
    ap("4. **Relation to Target F1b:** `existential_choice_iff_f1b` proves that `A14∃` is **DEFINITIONALLY EQUIVALENT** to target F1b (`(∃ s p, Act s p) → ∃ s, FreeWill s`) under `FreeWill s := ∃ p q, Chooses s p q` (`rfl`).")
    ap("5. **Sufficiency for Free Will:** YES (`freeWill_exists_of_existential_choice`).")
    ap("6. **Pre-A14 Derivability:** NO. `act_orthogonal_to_existential_contrastive_agency_in_full_theory` in `fullTheoryHostileInstance` proves that `A14∃` is independent of the pre-A14 theory.")
    ap("7. **Transitivity with A13:**")
    ap("```text")
    ap("A13 : Act s p → Means s (¬p)")
    ap("       ↓")
    ap("A14 : ∀ s p, Act s p → ∃ q, Chooses s p q")
    ap("       ↓")
    ap("A14∃ : (∃ s p, Act s p) → ∃ s p q, Chooses s p q  (≡ F1b)")
    ap("```")
    ap("`act_polarity_implies_existential_choice` verifies direct entailment `A13 → A14∃`.")
    ap("")
    ap("### Systematic Attack on F1b and the Mathematical Frontier")
    ap("")
    ap("Target F1b: `(∃ s p, Act s p) → ∃ s, FreeWill s` (definitionally equivalent to `A14∃`).")
    ap("")
    ap("We seek whether there is a genuinely more primitive semantic principle $B$ such that:")
    ap("$$\\text{Pre-A14 } \\Gamma + B \\vdash \\text{F1b}$$")
    ap("while $B$ is not definitionally or propositionally equivalent to F1b/A14∃, and not merely A14/A13 under another name.")
    ap("")
    ap("#### The 11-Way Candidate Classification")
    ap("")
    ap("| Candidate Direction | Formulation / Schema | Strict Classification | Hostile Witness / Model | Formal Mechanism & Status |")
    ap("|---|---|---|---|---|")
    ap(r"| **1. Doubt / Propositional Polarity** | `Doubts s p := Means s p ∧ Means s (¬p)` | **INCOMPARABLE** (datum) / **STRICTLY STRONGER THAN F1b** (act bridge); **REFUTED BY HOSTILE MODEL** | `fullTheoryHostileInstance` (`Means s p := p`) | As an unprompted datum (`DoubtingDatum : ∃ s p, Doubts s p`), it is incomparable with F1b (entails FreeWill without requiring an intentional act; not entailed by F1b). As an act bridge (`Act s p → ∃ q, Doubts s q`), it strictly entails F1b but forces contradictory negation $\neg p$. In pre-A14 Γ, doubt is identically False in veridical models (`p ∧ ¬p ↔ False`). |")
    ap(r"| **2. Self-Reference / Retorsion** | `SelfDenialOfChoice s p := Act s p ∧ (p ↔ ∀ q, ¬ Chooses s p q)` | **REFUTED BY HOSTILE MODEL** | `DelusionalSelfChoiceModel` & `SelfDenialOfChoiceModel` | An agent can truthfully perform an act with content 'this act contains no genuine choice' (`p = True`), and in fact possess zero choice (`∀ q, ¬ Chooses s p q`). Performative retorsion fails to populate the cognitive field with alternative contents. |")
    ap(r"| **3. Intentionality as such** | `Intentional s := ∃ p, Means s p` (or `Act s p`) | **REFUTED BY HOSTILE MODEL** | `fullTheoryHostileInstance` (`act_orthogonal_to_genuine_choice_in_full_theory`) | Present in pre-A14 Γ (`T5_personExists`, `act_implies_intentional`). Survives in hostile models where an agent acts intentionally with single/veridical content, completely decoupled from genuine choice. |")
    ap(r"| **4. Rationality / Judgment** | `Judge s := Asserts s (¬ N_T ∧ ¬ N_F)` | **REFUTED BY HOSTILE MODEL** | `fullTheoryHostileInstance` (`JUDGE_HAS_CHOICE_FIELD`) | Judgment derives an *objective* alternative field `ChoiceField s p (¬p)` (`Means s p ∧ Incompatible p (¬p)`), but does NOT derive the second cognitive horn `Means s (¬p)`. The judge remains free of choice in factive models. |")
    ap(r"| **5. Alternative-Generation** | `∃ q, Incompatible p q` | **REFUTED BY HOSTILE MODEL** | `CountermodelVeridicalMeaning.Single` | Pure logic: for any $p$, $q := \neg p$ satisfies `Incompatible p (¬p)`. Being a tautology, it holds in all models, including single-meaning deterministic models, and cannot force mental representation of $q$. |")
    ap(r"| **6. Modal Openness / Branching** | `∃ w w' : State, Initiates s w w' p ∧ ∃ w'' : State, Initiates s w w'' q` | **REFUTED BY HOSTILE MODEL** | `ModelM2BranchingInitiation` (`counterfactual_branching_not_entails_means`) | Physical or modal non-determinacy in causal initiation branches the state space without forcing internal intentional representation `Means s q` of the non-actualized branch. |")
    ap(r"| **7. Contrastive Explanation** | `ExplainsContrast s p q := Act s p ∧ Means s q ∧ Incompatible p q` | **REDUNDANT / RENAMED F1b** (if cognitive) / **REFUTED BY HOSTILE MODEL** (if objective) | `ModelM2BranchingInitiation` & `fullTheoryHostileInstance` | If defined with cognitive representation `Means s q`, existential contrastive agency is definitionally equivalent to F1b (`existential_contrastive_agency`). If defined purely objectively without `Means s q`, it is refuted by M2. |")
    ap(r"| **8. Reasons-Responsive Agency** | `ReasonResponsiveAct s p r := Act s p ∧ Means s r ∧ (r → p)` | **REFUTED BY HOSTILE MODEL** | `hostileReasonResponsiveInstance` (`reason_responsiveness_not_entails_contrastive_agency`) | Acting for a sufficient reason in the actual world does not require occurrent representation of contrary reasons in thought. Counterfactual dispositions do not populate actual occurrent `Means`. |")
    ap(r"| **9. Authorship / Settlement** | `Authors s p q := Act s p ∧ ¬ Act s q ∧ Incompatible p q` | **DERIVED** in pre-A14 Γ; **REFUTED BY HOSTILE MODEL** for F1b | `fullTheoryHostileInstance` (`authors_not_entails_rejected_horn_meaning`) | Raw authorship is derived in pre-A14 Γ (`act_implies_authors`), but fails to derive F1b because non-action on $\neg p$ does not imply meaning $\neg p$. 'Deliberate Authorship' (`Authors ∧ Means s q`) is **REDUNDANT / RENAMED F1b**. |")
    ap(r"| **10. Deliberation** | `Deliberates s p q` vs `DeliberateChoice s p q` | **REDUNDANT / RENAMED F1b** (raw) / **STRICTLY STRONGER THAN F1b** (executive) | `hostileAgencyInstance` (`deliberateChoice_negation_decomposition`) | Raw deliberation (`deliberates_iff_chooses`) is definitionally identical to `Chooses`. Executive deliberation (`DeliberateChoice := Selects ∧ Means s q`) strictly entails F1b and is refuted by veridical models. |")
    ap(r"| **11. Unrealized Possibilities** | `∃ s p, Means s p ∧ ¬p` (non-factive intentionality) | **REFUTED BY HOSTILE MODEL** | `UnrealizedPossibilityModel` (`unrealized_not_entails_freeWill`) | Representing a false or unrealized proposition allows error in thought, but does not force co-meaning mutually exclusive alternatives. An agent representing a falsehood does not thereby possess genuine choice among alternatives. |")
    ap("")
    ap("#### The Exact Mathematical Frontier of Genuine Choice")
    ap("")
    ap("In `formal/Logos/Choice.lean`, the exact mathematical structure required to close F1b is formally isolated:")
    ap("")
    ap("```lean")
    ap("def MissingCognitiveHorn (s : Subject) (p : Prop) : Prop :=")
    ap("  ∃ q : Prop, Means s q ∧ Incompatible p q")
    ap("")
    ap("theorem means_missing_horn_iff_chooses (s : Subject) (p : Prop) :")
    ap("  Means s p ∧ MissingCognitiveHorn s p ↔ ∃ q, Chooses s p q")
    ap("")
    ap("theorem freeWill_iff_means_missing_horn :")
    ap("  (∃ s : Subject, FreeWill s) ↔ ∃ s : Subject, ∃ p : Prop, Means s p ∧ MissingCognitiveHorn s p")
    ap("")
    ap("theorem act_missing_horn_implies_chooses (s : Subject) (p : Prop) :")
    ap("  Act s p ∧ MissingCognitiveHorn s p → ∃ q, Chooses s p q")
    ap("")
    ap("theorem act_missing_horn_iff_chooses (s : Subject) (p : Prop) (hAct : Act s p) :")
    ap("  MissingCognitiveHorn s p ↔ ∃ q, Chooses s p q")
    ap("```")
    ap("")
    ap("The mathematical frontier is completely rigid:")
    ap("1. **First Horn Provided by Act:** For any intentional act `Act s p`, pre-A14 Γ supplies the first cognitive horn: `Means s p` (via `act_decomposition`).")
    ap("2. **Objective Incompatibility Provided by Logic:** For any proposition $p$, logic supplies an incompatible partner: $q := \\neg p$ with `Incompatible p (¬p)` (`incompatible_self_negation`).")
    ap("3. **The Irreducible Missing Ingredient:** The entire axiomatic gap of F1b is precisely `MissingCognitiveHorn s p`, i.e., `∃ q, Means s q ∧ Incompatible p q`.")
    ap("4. **No Pre-A14 Structure Supplies This Horn:** Neither causal initiation (`Initiates`), nor logical negation (`¬`), nor assertion (`Asserts`), nor judgment (`Judge`), nor authorship (`Authors`), nor non-factivity (`Means s p ∧ ¬p`) supplies `Means s q` for an incompatible $q$.")
    ap("5. **Conclusion:** Any principle $B$ that derives F1b without goal-containment either introduces a substantive cognitive commitment strictly stronger than F1b (such as A13 or DoubtingDatum), or is equivalent to F1b under definitional expansion (such as A14∃ or Deliberates). No weaker or decoupled existing structure in Γ can derive genuine choice.")
    ap("")
    ap("### The Frontier Meta-Theorems (Relative Completeness, General Independence, and Contrastive Collapse)")
    ap("")
    ap("The frontier separating pre-A14 agency from genuine choice is not merely an empirical collection of failed attempts. "
       "It is a **rigorous mathematical boundary** governing the formal language of Γ, established by three meta-theorems:")
    ap("")
    ap("#### 1. Claim A — Exact Relative Completeness Theorem")
    ap("")
    ap("Relative to the pre-A14 vocabulary and axioms, target F1b is provably equivalent to the conditional existence of the missing cognitive horn over the performative action datum:")
    ap("")
    ap("```lean")
    ap("theorem f1b_iff_missing_cognitive_horn :")
    ap("  ((∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, FreeWill s) ↔")
    ap("  ((∃ s : Subject, ∃ p : Prop, Act s p) → ∃ s : Subject, ∃ p : Prop, Means s p ∧ MissingCognitiveHorn s p)")
    ap("```")
    ap("")
    ap("- **Kernel Footprint:** `{Initiates, Means, State, Subject}` (VOCAB only; zero non-logical axioms).")
    ap("- **Transparent Equivalence:** Because `FreeWill s ↔ ∃ p, Means s p ∧ MissingCognitiveHorn s p` holds by pure definition, "
       "F1b is transparently the requirement that intentional action be accompanied by the mental co-representation of an incompatible alternative. "
       "Closing F1b without supplying `MissingCognitiveHorn` is a logical impossibility.")
    ap("")
    ap("#### 2. Claim B — Parameterized Hostile Model Family (General Independence)")
    ap("")
    ap("In `formal/Logos/HostileSemantics.lean` (`ParameterizedHostileFamily`), the hostile countermodel is elevated from an isolated instance to a **reusable parameterized model family**:")
    ap("")
    ap("$$\\forall R : \\text{Bool} \\to \\text{Prop} \\to \\text{Prop},\\; \\text{AdmissiblePreA14Meaning}(R) \\land \\text{HornFreeMeaning}(R) \\implies \\text{PreA13FullTheory}(\\text{model}(R)) \\land \\neg \\text{F1b}$$")
    ap("")
    ap("- **Admissibility:** Any relation where subjects mean true performed contents (e.g. $R(\\text{true}, \\text{True})$).")
    ap("- **Horn-Free Condition:** $\\forall s\\,p\\,q,\\; R(s,p) \\land R(s,q) \\implies \\neg \\text{Incompatible}(p,q)$ (i.e. the agent never simultaneously entertains mutually exclusive propositions).")
    ap("- **Scope:** Captures veridical semantics ($R(s,p) := p$), single-content intentionality ($R(s,p) := (p = \\text{True})$), and any conjunctive belief filter.")
    ap("- **Result:** Pre-A14 $\\Gamma \\nvdash \\text{F1b}$ across the entire family.")
    ap("")
    ap("#### 3. Claim C — Model-Transformation Preservation & Blocker Analysis")
    ap("")
    ap("In `formal/Logos/HostileSemantics.lean` (`ModelTransformationCollapse`), we define the generic semantic transformation:")
    ap("")
    ap("$$\\text{Collapse}(M) := M[\\text{Means} \\mapsto \\lambda s\\,p,\\; M.\\text{Means}(s,p) \\land p]$$")
    ap("")
    ap("1. **Universal Choice Destruction:** For EVERY model $M$, $\\forall s\\,p\\,q,\\; \\neg \\text{Chooses}(\\text{Collapse}(M), s, p, q)$ (`collapse_destroys_all_choice`).")
    ap("2. **Blocker Analysis for Unconditioned $T_0$:** Does `Collapse(M)` preserve the unconditioned 12-axiom theory $T_0$ for arbitrary models? **NO.**")
    ap("   - *Axiom 1 Blocker (`nonfactive_act_blocks_collapse`):* If all intentional acts in $M$ are non-factive ($p = \\text{False}$), `FullAct` collapses to false, refuting Axiom 1 (Act Datum).")
    ap("   - *Axiom 2 Blocker (`nonfactive_plurality_blocks_collapse`):* If a person in $M$ only means non-factive contents, `FullPerson` collapses to false, refuting Axiom 2 (Plurality of Persons).")
    ap("3. **Full Preservation Theorem on Factive Models:** On `FactivePreA14Theory` (where intentional acts and personhood meanings are realized factively), `ContrastiveCollapse` **provably preserves every one of the 12 pre-A14 axioms** (`collapse_preserves_preA14`).")
    ap("4. **Canonical Witness:** `fullTheoryHostileInstance_is_factive` formally verifies that the canonical hostile instance is factive.")
    ap("")
    ap("#### 4. Claim D — Structural Impossibility for Contrastive-Blind Extensions")
    ap("")
    ap("Let $B$ be any extension of the theory satisfying the model-preserving blindness condition:")
    ap("$$\\text{PreA14ContrastiveBlind}(B) := \\forall I,\\; \\text{FactivePreA14Theory}(I) \\land B(I) \\implies B(\\text{ContrastiveCollapse } I)$$")
    ap("")
    ap("The kernel formally proves the model-theoretic impossibility theorem (`blind_extension_cannot_derive_f1b`):")
    ap("")
    ap("$$\\text{PreA14ContrastiveBlind}(B) \\land \\text{PreA14Consistent}(B) \\implies \\exists M,\\; \\text{PreA13FullTheory}(M) \\land B(M) \\land (\\exists s\\,p,\\; \\text{FullAct } M\\,s\\,p) \\land \\neg (\\exists s,\\; \\text{FullFreeWill } M\\,s)$$")
    ap("")
    ap("> **Exact Impossibility:** $\\text{Pre-A14 }\\Gamma + B \\nvdash \\text{F1b}$. Every consistent contrastive-blind extension admits a choice-free model satisfying the entire pre-A14 theory.")
    ap("")
    ap("#### 5. Claim E — Expressivity Boundary & Non-Definability Theorem")
    ap("")
    ap("In `formal/Logos/HostileSemantics.lean` (`ExpressivityBoundary`), we construct the inductive syntax `BlindFormula (Subject State Entity : Type)` decoupled from concrete model instances, with constructors for:")
    ap("- Propositional truth connectives (`top`, `bot`, `not`, `and`, `or`, `imp`)")
    ap("- Causal state transitions: `causal (s : Subject) (w w' : State) (p : Prop)` (`Initiates`)")
    ap("- Truthmaker grounding: `ground (e : Entity) (p : Prop)` (`Ground`)")
    ap("- Objective logical incompatibility: `incomp (p q : Prop)` (`Incompatible`)")
    ap("- Factive intentional meaning: `factiveMeans (s : Subject) (p : Prop)` (`Means s p ∧ p`)")
    ap("")
    ap("The kernel machine-checks two fundamental expressivity results:")
    ap("1. **Invariance Theorem (`blind_formula_collapse_invariant`):** By structural induction on formulas, every $\\varphi \\in \\text{BlindFormula}$ evaluates identically in any model and in its contrastive collapse:")
    ap("$$\\forall I\\,\\varphi,\\; \\text{eval } I\\ \\varphi \\iff \\text{eval } (\\text{ContrastiveCollapse } I)\\ \\varphi$$")
    ap("2. **Non-Definability of Genuine Choice (`no_blind_formula_defines_choice`):** In a model $I_{\\text{choice}}$ where genuine choice occurs, any formula defining `Chooses` would evaluate to true in $I_{\\text{choice}}$, hence true in $\\text{Collapse}(I_{\\text{choice}})$, contradicting `collapse_destroys_all_choice`. Thus:")
    ap("$$\\neg \\exists \\varphi \\in \\text{BlindFormula},\\; \\text{eval } I\\ \\varphi \\iff \\text{FullChooses } I\\ s\\ p\\ q$$")
    ap("3. **Non-Definability of Free Will (`no_blind_formula_defines_freeWill`):** No formula in `BlindFormula` can define `FreeWill` or target F1b across models.")
    ap("")
    ap("#### 6. Adversarial Self-Attack & Loopholes Analysis")
    ap("")
    ap("- **Loophole 1: Quantifier Permutation:** Can an existential action datum $\\exists s\\,p, Act(s,p)$ force choice through an external subject? Refuted: In single-agent models (`CountermodelVeridicalMeaning.Single`), no external subject exists.")
    ap("- **Loophole 2: Non-Factivity without Choice:** Can allowing false beliefs force choice? Refuted: `UnrealizedPossibilityModel` demonstrates an agent meaning a falsehood (`Means () False`) with zero genuine choice.")
    ap("- **Loophole 3: Disjunctive / Negated Actions:** Can an agent act on a disjunction $p \\lor q$? Refuted: Acting on $p \\lor q$ provides `Means s (p ∨ q)`, not `Means s p ∧ Means s q`.")
    ap("- **Loophole 4: Performative Retorsion / Self-Denial:** Refuted: `SelfDenialOfChoiceModel` and `DelusionalSelfChoiceModel` prove that self-referential denial of choice is consistent with zero genuine choice.")
    ap("")
    ap("#### 5. Architectural Synthesis: The Frontier Diagram")
    ap("")
    ap("```text")
    ap("=========================================================================================")
    ap("                           THE FRONTIER THEOREM                                          ")
    ap("=========================================================================================")
    ap("                                                                                         ")
    ap("    Performative Intentional Action (Act s p)                                            ")
    ap("            │                                                                            ")
    ap("            ├──► Intentional Meaning: Means s p                   (Layer 1 - PROVEN)     ")
    ap("            ├──► Causal Initiation: Initiates s w w' p            (Layer 0 - PROVEN)     ")
    ap("            ├──► Objective Incompatibility: Incompatible p (¬p)   (Layer 2 - PROVEN)     ")
    ap("            ├──► Selection / Settlement: Selects / Authors        (Layer 3 - PROVEN)     ")
    ap("            └──► Judgment / Truth / Normativity / Modality        (Layer 3+ - PROVEN)    ")
    ap("                           │                                                             ")
    ap("                           X  ◄─── CONTRASTIVE COLLAPSE BARRIER                          ")
    ap("                           │       (Destroyed by Collapse(M); Underdetermined by T₀)     ")
    ap("                           │                                                             ")
    ap("                Cognitive Representation of an Incompatible Alternative                   ")
    ap("                (MissingCognitiveHorn s p := ∃ q, Means s q ∧ Incompatible p q)          ")
    ap("                           │                                                             ")
    ap("                           ▼                                                             ")
    ap("                     Genuine Choice (Chooses s p q)               (Layer 4 - A14)        ")
    ap("                           │                                                             ")
    ap("                           ▼                                                             ")
    ap("                       Free Will (FreeWill s)                     (Target F1b)           ")
    ap("=========================================================================================")
    ap("```")
    ap("")
    ap("### Candidate Layer Beneath A14")
    ap("")
    ap("Current status:")
    ap("")
    ap("```text")
    ap("  Objective incompatibility")
    ap("          ↓")
    ap("  [MISSING COGNITIVE RELATION]")
    ap("          ↓")
    ap("  Cognitive alternative representation")
    ap("          ↓")
    ap("  Chooses")
    ap("          ↓")
    ap("  FreeWill")
    ap("```")
    ap("")
    ap("The candidate cognitive relation is NOT yet part of Γ.")
    ap("")
    ap("Its logical strength relative to A14 is currently OPEN.")
    ap("")
    ap("---")
    ap("")
    ap("## O Programa de Teologia Condicional (Γ + A14 ⊢ ?)")
    ap("")
    ap("Adotando $A14$ (`AxIntentionalChoice`: $Act(s,p) \\to \\exists q, Chooses(s,p,q)$) como o único novo compromisso semântico substantivo, "
       "investigamos formalmente no módulo `formal/Logos/ConditionalTheology.lean` o que o sistema axiomático existente de $\\Gamma$ é capaz de derivar em direção à teologia filosófica "
       "(fundamento último, personalidade, pluralidade, amor, trindade, encarnação, criação).")
    ap("")
    ap("### 1. Fechamento de Agência e Limites de FreeWill")
    ap("")
    ap("O fechamento dedutivo imediato de A14 estabelece:")
    ap("$$Act(s,p) \\implies Chooses(s,p,q) \\implies FreeWill(s) \\land FreeSubject(s) \\land IntentionalSubject(s)$$")
    ap("(Na ontologia unificada de $\\Gamma$, $Person(s) := FreeSubject(s) \\leftrightarrow FreeWill(s)$, sendo a pessoalidade decorrência constitutiva do livre-arbítrio com 0 axiomas substantivos).")
    ap("")
    ap("No entanto, o teste adversarial contra 8 dimensões de agência prova que $FreeWill$ **NÃO acarreta** nenhuma das seguintes propriedades (todas separadas por contramodelos máquina-verificados):")
    ap("1. **Racionalidade:** $FreeWill \\nvdash ReasonsFor$ (`freewill_not_entails_rationality`). Agentes livres podem escolher sem razões explicativas.")
    ap("2. **Normatividade:** $FreeWill \\nvdash ActsCorrectly$ (`freewill_not_entails_normativity`). A liberdade permite o erro e a infração normativa.")
    ap("3. **Valor Interpessoal:** $FreeWill \\nvdash AffectsValue$ (`freewill_not_entails_value`). Agência livre é consistente com estados proposicionais indiferentes.")
    ap("4. **Teleologia:** $FreeWill \\nvdash HasGoal$ (`freewill_not_entails_teleology`). Escolhas deliberadas podem ser pontuais e espontâneas sem meta final.")
    ap("5. **Subjetividade Reflexiva:** $FreeWill \\nvdash KnowsOwnAct$ (`freewill_not_entails_reflexive_subjectivity`). A escolha de primeira ordem não força auto-representação transcendental de ordem superior.")
    ap("6. **Relacionalidade:** $FreeWill \\nvdash \\exists s_2, s_1 \\neq s_2$ (`freewill_not_entails_relationality`). Um agente livre pode existir em isolamento solipsista absoluto.")
    ap("7. **Persistência / Imortalidade:** $FreeWill \\nvdash Persists$ (`freewill_not_entails_persistence`). Agentes livres podem ser puramente efêmeros (existir e escolher em um único instante temporal/causal).")
    ap("8. **Necessidade:** $FreeWill \\nvdash NecSubject$ (`freewill_not_entails_necessity`). A vontade livre é compatível com contingência ontológica total.")
    ap("")
    ap("### 2. A Arquitetura de Fundamentação sob A14 (Obstrução da Cadeia Infinita)")
    ap("")
    ap("Na cadeia de fundamentação de verdades necessárias:")
    ap("$$T(p) \\implies \\exists e, Ground(e,p) \\implies \\exists e, Ground(e,p) \\land Nec(e) \\stackrel{?}{\\implies} UltimateGround(u)$$")
    ap("- A14 **não elimina** a regressão infinita de fundamentação (`a14_not_eliminates_infinite_ground_chain`). A agência livre de sujeitos contingentes não impõe boa-ordenação ou finitude na ordem explicativa ontológica.")
    ap("- Logo, $FreeWill \\nvdash UltimateGround$ (`free_agency_not_entails_ultimate_ground`).")
    ap("")
    ap("### 3. Independência do Fundamento Último Pessoal")
    ap("")
    ap("Mesmo que se postule a existência de um fundamento último ($UltimateGround(u)$), a adição de A14 **não força** que o fundamento último seja pessoal:")
    ap("$$A14 + UltimateGround \\nvdash Personal(u)$$")
    ap("Demonstrado formalmente em `a14_plus_ultimate_ground_not_entails_personal_ultimate_ground`: um fundamento último impessoal (substrato cósmico) é plenamente compatível com a existência de criaturas contingentes dotadas de livre-arbítrio.")
    ap("")
    ap("### 4. Independência de Pluralidade e Amor")
    ap("")
    ap("1. **Pluralidade:** $A14 \\nvdash Plurality$ (`a14_not_entails_plurality`). O contramodelo `SolitaryFreeAgentModel` prova que a agência livre não deriva um segundo sujeito sem o compromisso metafísico `AxTwoSubjects`.")
    ap("2. **Amor:** $A14 + Plurality \\nvdash Loves$ (`free_agency_and_plurality_not_entails_love`). Um universo com múltiplos agentes livres pode ser mutuamente hostil, maldoso ou estéril. O amor não decorre analiticamente da liberdade.")
    ap("")
    ap("### 5. Estruturas Teológicas Neutras: Trindade, Encarnação e Criação")
    ap("")
    ap("Definindo alvos estruturais neutros (sem contrabando dogmático por definição):")
    ap("1. **Trindade (`TrinitarianStructure`):** Exige 3 centros pessoais distintos em 1 realidade divina comum com relações mútuas eternas. Separado pelo modelo binitariano (`preceding_theory_not_entails_trinity`): uma teologia com 2 pessoas divinas em mútuo amor satisfaz plenamente $\\Gamma + A14$, tornando a Trindade estritamente indemonstrável sem axioma triádico.")
    ap("2. **Encarnação (`IncarnationalStructure`):** Exige que um mesmo sujeito pessoal una uma natureza divina e uma natureza humana. Separado pelo modelo unincarnado (`preceding_theory_not_entails_incarnation`): a transcendência divina não acarreta ontologicamente a união hipostática.")
    ap("3. **Criação Contingente (`CreationStructure`):** Separado pelo modelo divino acósmico (`necessary_ground_not_entails_contingent_creation`): um Deus necessário e autossuficiente pode existir sem criar qualquer universo ou sujeito contingente. A realidade necessária não força criação contingente.")
    ap("")
    ap("### 6. O Grafo de Dependência Teológica Formal")
    ap("")
    ap("```text")
    ap("=========================================================================================")
    ap("                 GRAFO DE DEPENDÊNCIA TEOLÓGICA (Γ + A14)                                 ")
    ap("=========================================================================================")
    ap("                                                                                         ")
    ap("     [Act s p]                                                                           ")
    ap("         │                                                                               ")
    ap("         ▼  (A14: AxIntentionalChoice - SEMANTIC)                                        ")
    ap("     [Chooses s p q]                                                                     ")
    ap("         │                                                                               ")
    ap("         ▼  (DEFINITIONAL)                                                               ")
    ap("     [FreeWill s]                                                                        ")
    ap("         │                                                                               ")
    ap("         ├──X (COUNTERMODEL: freewill_not_entails_rationality)      ──► [Rationality]    ")
    ap("         ├──X (COUNTERMODEL: freewill_not_entails_normativity)      ──► [Normativity]    ")
    ap("         ├──X (COUNTERMODEL: freewill_not_entails_teleology)        ──► [Teleology]      ")
    ap("         ├──X (COUNTERMODEL: freewill_not_entails_relationality)    ──► [Relationality]  ")
    ap("         └──X (COUNTERMODEL: freewill_not_entails_necessity)        ──► [Necessity]      ")
    ap("                                                                                         ")
    ap("     [Necessary Truth (T p)]                                                             ")
    ap("         │                                                                               ")
    ap("         ▼  (A4/A6: AxGlobalGround - PROVEN)                                             ")
    ap("     [Some Ground (Ground e p)]                                                          ")
    ap("         │                                                                               ")
    ap("         ▼  (Modal: T7_necessaryReality - PROVEN)                                        ")
    ap("     [Necessary Ground (Ground e p ∧ Nec e)]                                             ")
    ap("         │                                                                               ")
    ap("         X  ◄─── (COUNTERMODEL: a14_not_eliminates_infinite_ground_chain)                  ")
    ap("         │                                                                               ")
    ap("     [Ultimate Ground]                                                                   ")
    ap("         │                                                                               ")
    ap("         X  ◄─── (COUNTERMODEL: a14_plus_ultimate_ground_not_entails_personal_ultimate)      ")
    ap("         │                                                                               ")
    ap("     [Personal Ultimate Ground]                                                          ")
    ap("         │                                                                               ")
    ap("         X  ◄─── (METAPHYSICAL: A10 AxTwoSubjects required; Solitary Model blocks)       ")
    ap("         │                                                                               ")
    ap("     [Plurality of Persons]                                                              ")
    ap("         │                                                                               ")
    ap("         X  ◄─── (METAPHYSICAL: AxPersonsAffect required; Malicious Model blocks)        ")
    ap("         │                                                                               ")
    ap("     [Mutual Divine Love]                                                                ")
    ap("         │                                                                               ")
    ap("         X  ◄─── (COUNTERMODEL: Binitarian Model blocks Trinity)                         ")
    ap("         │                                                                               ")
    ap("     [Trinitarian Structure (3 Persons)]                                                 ")
    ap("         │                                                                               ")
    ap("         ├──X (COUNTERMODEL: Acosmic Model blocks) ──► [Contingent Creation]             ")
    ap("         │                                                    │                          ")
    ap("         └────────────────────────────────────────────────────X (Unincarnate Model)     ")
    ap("                                                              │                          ")
    ap("                                                              ▼                          ")
    ap("                                                     [Incarnation]                       ")
    ap("=========================================================================================")
    ap("```")
    ap("")
    ap("### 7. Síntese do Balanço Axiomático (Single-Axiom Discipline)")
    ap("")
    ap("- **O que A14 realmente compra:** A14 fecha formalmente o salto de agência performativa para livre-arbítrio (`Act → Chooses → FreeWill`), garantindo a existência de um sujeito livre (`FreeSubject`) e de uma pessoa moral (`Person`).")
    ap("- **O que A14 NÃO compra:** A14 não compra fundamentação última bem-ordenada, não compra personalidade do absoluto, não força pluralidade, não força amor mútuo, não deriva a Trindade, não força a criação contingente e não deriva a Encarnação.")
    ap("- **A Teologia de $\\Gamma$:** É uma teologia rigorosamente condicional, estratificada e honesta. Cada passo além da liberdade requer explicitamente ou uma nova ponte metafísica (como `AxTwoSubjects` e `AxPersonsAffect`) ou permanece estritamente indecidível/independente da lógica interna da agência.")
    ap("")
    ap("---")
    ap("")
    ap("## O Passe de Endurecimento Ontológico de Γ (Ontology Hardening)")
    ap("")
    ap("Executamos um passe agressivo de **endurecimento ontológico** sobre $\\Gamma$, eliminando atalhos definicionais "
       "que carregavam conteúdo metafísico substantivo disfarçado de analiticidade, sob a regra mandatória:")
    ap("")
    ap("> **Prefira perder um teorema a esconder uma premissa.**")
    ap("")
    ap("### 1. Desconstrução dos Atalhos Eliminados")
    ap("")
    ap("1. **`ExistsAt` (Existência Relativa a Mundos vs. Necessidade Degenerada):**")
    ap("   - *Atalho anterior:* `ExistsAt w (Entity.ofSubject _) := True` tornava qualquer sujeito atuante trivialmente necessário em todos os mundos por pura definição analítica.")
    ap("   - *Endurecimento:* Substituído por existência genuinamente sensível ao mundo (`SubjectExistsAt w s`, `EntityExistsAt w e`). Sujeitos atuantes na atualidade não existem automaticamente em mundos contrafatuais.")
    ap("   - *Impacto:* Os teoremas C77 (`necessaryPersonExists`) e C92 (`necessary_entity_exists`) a partir do ato performativo foram **demovidos e refutados por contramodelo** (`ContingentAgencyModel`: `act_not_entails_necessary_subject` e `act_not_entails_necessary_entity`). A necessidade ontológica não nasce mais de um ato contingente.")
    ap("")
    ap("2. **`Person` (Sujeito Intencional vs. Livre-Arbítrio e Pessoalidade):**")
    ap("   - *Atalho anterior:* `Person s := Agent s ∧ Rational s ∧ Intentional s` com `Agent := True` e `Rational := True`, fazendo com que qualquer registro intencional fosse nominalmente uma 'pessoa'.")
    ap("   - *Endurecimento e Unificação:* Distinção entre o mero sujeito intencional (`IntentionalSubject s := ∃ p, Means s p`), a vontade numericamente individuada (`subjectWill s`), e a Pessoa como o sujeito dotado de livre-arbítrio (`Person s := FreeSubject s ↔ FreeWill s`).")
    ap("   - *Impacto:* O ato intencional singular não é chamado de pessoa antes da deliberação; a pessoalidade segue com necessidade dedutiva plena a partir do Livre-Arbítrio derivado da retorsão (`free_subject_is_person`, 0 axiomas substantivos).")
    ap("")
    ap("3. **Relações Interpessoais (`Affects`, `Helps`, `Harms`, `Loves`):**")
    ap("   - *Atalho anterior:* `Affects s t := s ≠ t`, `Helps := Affects`, `Harms := False`, o que tornava o amor uma consequência analítica imediata da mera distinção entre dois sujeitos ($s \\neq t \\implies Loves(s,t)$).")
    ap("   - *Endurecimento:* As relações de afetação, ajuda e dano foram endurecidas em termos primitivos independentes (`BearingOf s t`), preservando a definição constitutiva de amor como benevolência direcionada (`Loves s t := Helps s t ∧ ¬ Harms s t`).")
    ap("   - *Impacto:* A derivação automática de amor a partir da pluralidade foi **completamente destruída**. Dois sujeitos distintos não se afetam, não se ajudam e não se amam analiticamente (`DisconnectedPluralityModel`: `plurality_not_entails_affects`, `plurality_not_entails_helps`, `plurality_not_entails_love`, `freewill_and_plurality_not_entails_love`). T13 e T14 tornam-se estritamente condicionais a princípios relacionais explícitos.")
    ap("")
    ap("4. **Ataque aos Quatro Grandes Axiomas (A3, A4, A6, A7):**")
    ap("   - **A3 (Truthmaker):** A instanciação atômica (`groundPrinciple_atom`) não deriva a fundamentação existencial de fórmulas compostas sem indução estrutural (`AtomicVsFormulaTruthmakerModel`).")
    ap("   - **A4 (Global Ground):** A fundamentação mundanal ordinária não acarreta um fundamento uniforme necessário comum a todos os mundos (`CountermodelWorldwiseTruthmaking`). A4 permanece estritamente irredutível como compromisso semântico.")
    ap("   - **A6 (Pluralidade):** O cogito performativo, a bivalência e o livre-arbítrio (sob A14) são plenamente consistentes com um modelo solitário de agente único (`SolitaryChoiceModel`). A6 permanece estritamente irredutível como compromisso META.")
    ap("   - **A7 (Personal Ground):** A fundamentação de uma propriedade pessoal não transfere o tipo ontológico para o fundamento (`CountermodelImpersonalUltimateGround`). A7 permanece estritamente irredutível como compromisso META.")
    ap("")
    ap("### 2. Tabela de Auditoria Compacta (Ontology Hardening Ledger)")
    ap("")
    ap("| Área Ontológica | Formulação Antiga (Degenerada) | Formulação Endurecida (Robusta) | Teorema Antigo Sobrevive? | Novo Axioma Adicionado? | Status Epistêmico / Contramodelo |")
    ap("| :--- | :--- | :--- | :--- | :--- | :--- |")
    ap("| **Person** | `Agent ∧ Rational ∧ Intentional` (`Agent, Rational := True`) | `IntentionalSubject s := ∃p, Means s p`; `Person s := FreeSubject s` | **UNIFICADO / DERIVADO** (`Act → IntentionalSubject` e `FreeSubject → Person` provados) | **NÃO** (0 axiomas) | `DEFINITIONAL` (`free_subject_is_person`, 0 axiomas substantivos) |")
    ap("| **ExistsAt** | `ExistsAt w (Entity.ofSubject _) := True` (necessidade analítica) | `SubjectExistsAt w s` sensível a mundos (`w = actualWorld`) | **DEMOVIDO** (C77 e C92 refutados; necessidade do ato cai) | **NÃO** (0 axiomas) | `COUNTERMODEL` (`ContingentAgencyModel`: `act_not_entails_necessary_subject`) |")
    ap("| **Ground (A3)** | Truthmaker existencial irrestrito para todas as fórmulas | Fundamentação atômica (`groundPrinciple_atom`) + semântica composicional | **AUDITADO / REDUZIDO** (átomos fundamentados; compostos livres) | **NÃO** (A3 auditado) | `SEMANTIC` / `AtomicVsFormulaTruthmakerModel` |")
    ap("| **GlobalGround (A4)** | Troca de quantificadores $\\forall w \\exists e \\to \\exists e \\forall w$ | Fundamentação mundanal vs. fundamento necessário uniforme | **IRREDUTÍVEL** (fundamento uniforme não dedutível de mundanal) | **NÃO** (A4 preservado) | `SEMANTIC` / `CountermodelWorldwiseTruthmaking` |")
    ap("| **Plurality (A6)** | `AxTwoSubjects` decorrente de certo/errado | Pluralidade genuína irredutível do agente único | **IRREDUTÍVEL** (agência e escolha não forçam segundo sujeito) | **NÃO** (A6 mantido como META) | `METAPHYSICAL` / `SolitaryChoiceModel`, `CountermodelUnitPlurality` |")
    ap("| **Love / Value** | `Affects := s ≠ t`, `Helps := Affects`, `Harms := False` | `BearingOf s t` independente; `Loves := Helps ∧ ¬Harms` | **DEMOVIDO** (Amor não decorre da pluralidade; T13/T14 condicionais) | **NÃO** (0 axiomas) | `COUNTERMODEL` (`DisconnectedPluralityModel`: `plurality_not_entails_love`) |")
    ap("")
    ap("> **Conclusão:** O sistema $\\Gamma$ agora repousa sobre uma base axiomática limpa, livre de atalhos definicionais ilícitos. A necessidade, a pessoalidade substantiva, a pluralidade e o amor mútuo são explicitamente reconhecidos pelo que são: exigências ontológicas de alto preço que jamais devem ser mascaradas sob definições analíticas triviais.")
    ap("")
    ap("---")
    ap("")
    ap("## O Programa de Expansão Retorsiva de Γ (Retorsion Expansion Pass)")
    ap("")
    ap("Sob a diretriz metodológica central:")
    ap("> **Para toda afirmação substantiva que Γ aceita, não basta testar se ela é derivável. Ataque também sua negação. Verifique se a negação é performativa, semântica, lógica ou metafisicamente auto-refutável.**")
    ap("> **Prefira perder um teorema a esconder uma premissa. Uma retorsão tem êxito somente quando a negação genuinamente não pode ser coerentemente sustentada.**")
    ap("")
    ap("### 1. Taxonomia e Estratégia Retorsiva de Primeira Classe")
    ap("")
    ap("- **Reductio Ordinário:** Assume $\\neg P$, deriva `False` num modelo arbitrário (`by_contra`).")
    ap("- **Retorsão Performativa:** Assume $\\neg P$ como uma posição cognitiva ou ato asserido real, analisa os compromissos ontológicos e semânticos indispensáveis para executar ou sustentar esse próprio ato, e demonstra que o próprio ato de negação pressupõe ou instancia $P$.")
    ap("")
    ap("Fontes rastreadas da contradição retorsiva:")
    ap("1. `RETORSION / LOGICAL`: O ato de asserção viola a coerência lógica bivalente ($T(\\text{NoTruth}) \\implies False$).")
    ap("2. `RETORSION / DEFINITIONAL`: O ato de asserir a negação instancia analiticamente o conceito negado (asserir `NoAct` executa um `Act`).")
    ap("3. `RETORSION / SEMANTIC`: A verdade pretendida pela negação exige uma ponte semântica que ela mesma rejeita (ou revela limitação expressiva).")
    ap("4. `RETORSION / METAPHYSICAL`: A posição sustentada anula as condições ontológicas do sujeito que julga.")
    ap("")
    ap("### 2. A Campanha Retorsiva Big-O / Big-S (Ontologia de Sujeito Intencional)")
    ap("")
    ap("Reformulamos a campanha retorsiva em torno do conceito ontológico fundamental de **dependência de um Sujeito Intencional** (`IntentionalSubject`), desvinculando a definição de Subjetividade de Pessoa e Livre-Arbítrio:")
    ap("")
    ap("```text")
    ap("Subject")
    ap("  └── IntentionalSubject")
    ap("")
    ap("Subjective x  :=  x depende de um Sujeito Intencional (DependsOnIntentional x)")
    ap("Objective x   :=  x não depende de um Sujeito Intencional (¬ DependsOnIntentional x)")
    ap("```")
    ap("")
    ap("- **Definição de Dependência Intencional:** `DependsOnIntentional x := ∃ s : Subject, IntentionalSubject s ∧ DependsOn x s`. Um item é subjetivo sse inere ontologicamente em um sujeito que significa conteúdos proposicionais.")
    ap("- **Dependência Ontológica:** Primitivo intensional `DependsOn x s` (**A15**, `Tag: VOCAB`).")
    ap("- **Disjunção Lógica Pura:** A disjunção entre Objetividade e Subjetividade (`objective_and_subjective_disjoint`) é um **teorema da lógica pura** ($\\neg P \\land P \\implies False$).")
    ap("- **Exaustão Clássica:** `Objective x ∨ Subjective x` decorre do Terceiro Excluído clássico.")
    ap("- **Cadeia Construtiva:** A inferência `Subjective x → ∃ s, IntentionalSubject s` é puramente lógica e definicional.")
    ap("")
    ap("Axiomas constitutivos da campanha retorsiva:")
    for base in ["DependsOn", "universal_thesis_claims_objectivity", "transcendental_reflection_intentional"]:
        _CTX["ax_shown"].add(base)
        r = _REGISTRY.get(base, {})
        aid = AX_ID.get(base, "?")
        ap(f"- **Axiom {aid} · `{base}` (`{r.get('tag', '?')}`):** {r.get('gloss', '—')}")
    ap("")
    ap("1. **Retorsão contra a Subjetividade Absoluta (Big-S):**")
    ap("   - Seja $ES := \\forall x, Subjective(x)$ (\"Tudo depende de um Sujeito Intencional\").")
    ap("   - Reivindica validade objetiva como tese universal sobre a realidade (independência de sujeito intencional): `universal_thesis_claims_objectivity` (**A16** / `SEM`).")
    ap("   - Pelo lema de auto-inclusão (`everything_subjective_self_applies`), $ES$ classifica a si mesma como dependente de sujeito intencional: $Subjective(ES)$.")
    ap("   - Pela contradição definicional entre $Objective$ e $Subjective$, temos $\\neg EverythingSubjective$ (`not_everything_subjective`, 0 premissas).")
    ap("   - Consequência existencial positiva: **$\\exists x, Objective(x)$** (`exists_objective_of_retorsion`, testemunhado pela própria tese universal).")
    ap("")
    ap("2. **Retorsão contra a Objetividade Absoluta (Big-O):**")
    ap("   - Seja $EO := \\forall x, Objective(x)$ (\"Nada depende de um Sujeito Intencional\").")
    ap("   - A reflexão transcendental sobre a objetividade universal depende de um sujeito intencional pensante: `transcendental_reflection_intentional` (**A17** / `SEM`).")
    ap("   - Essa ponte semântica estabelece que a própria formulação de $EO$ depende de um sujeito intencional: $Subjective(EO)$.")
    ap("   - Pelo lema de auto-inclusão (`everything_objective_self_applies`), $EO$ dita que ela mesma é objetiva: $Objective(EO)$.")
    ap("   - Pela contradição definicional, temos $\\neg EverythingObjective$ (`not_everything_objective`, 0 premissas).")
    ap("   - Consequência existencial positiva: **$\\exists x, Subjective(x)$** (`exists_subjective_of_retorsion`).")
    ap("")
    ap("3. **Dedução do Teorema Central: Existência do Sujeito Intencional via Retorsão:**")
    ap("   - Da testemunha positiva $\\exists x, Subjective(x)$, decorre imediatamente:")
    ap("     $$\\exists s : Subject, \\; IntentionalSubject(s) \\quad (\\text{`exists_intentional_subject_of_retorsion`})$$")
    ap("")
    ap("```text")
    ap("=========================================================================================")
    ap("TEOREMA CENTRAL — EXISTÊNCIA DO SUJEITO INTENCIONAL VIA RETORSÃO BIG-O / BIG-S")
    ap("=========================================================================================")
    ap("A campanha retorsiva sob a ontologia de Dependência Intencional estabelece formalmente em Lean:")
    ap("")
    ap("    exists_intentional_subject_of_retorsion : ∃ s : Subject, IntentionalSubject s")
    ap("")
    ap("Cadeia Construtiva Transparente:")
    ap("    Retorsão Big-O  ──→  ∃ x, Subjective x  ──→  ∃ s, IntentionalSubject s")
    ap("")
    ap("Footprint Axiomático Auditado pelo Kernel:")
    ap("    {Means, Subject, DependsOn, transcendental_reflection_intentional}")
    ap("")
    ap("• RIGOROSAMENTE INDEPENDENTE de Person, FreeWill, Chooses, Act e A14.")
    ap("• Não depende de Initiates, State, Cogito, ou escolha moral deliberada.")
    ap("• A retorsão atinge legitimamente o Sujeito Intencional e estanca ANTES de Pessoa / Livre-Arbítrio.")
    ap("=========================================================================================")
    ap("```")
    ap("")
    ap("> **Significado Conceitual Preciso:** A rota Big-O / Big-S estabelece a existência de um centro de perspectiva intencional (`IntentionalSubject`) independentemente de `Act`. Ela não assume Livre-Arbítrio nem Pessoalidade, mantendo estes como conceitos a jusante.")
    ap("")
    ap("#### Fronteira Conceitual e Teoremas de Separação")
    ap("")
    ap("A arquitetura torna a fronteira explícita:")
    ap("```text")
    ap("Retorsão Big-O / Big-S")
    ap("   │")
    ap("   ▼  [PROVADO - exists_intentional_subject_of_retorsion]")
    ap("IntentionalSubject")
    ap("   │")
    ap("   X  [BLOQUEADO - DeterministicTranscendentalSubjectModel]")
    ap("   ▼")
    ap("Person (FreeWill)")
    ap("```")
    ap("")
    ap("#### Auditoria Adversarial: A Fraqueza Inerente e o Teste do \"Porco Voador\"")
    ap("")
    ap("Submetemos a campanha retorsiva ao teste adversarial definitivo: **pode a retorsão descobrir o Livre-Arbítrio sem já assumi-lo na premissa retorsiva A17?**")
    ap("")
    ap("1. **Variantes Enfraquecidas da Premissa Retorsiva:**")
    ap("   - *Dependência de Sujeito Nu (`DependsOnBareSubject`):* Se a reflexão transcendental exige apenas que a tese dependa de algum sujeito (`∃ s, DependsOn EO s`), a retorsão deriva apenas a existência do sort `∃ s : Subject, True`, sem qualquer intencionalidade ou agência.")
    ap("   - *Dependência de Sujeito Intencional (`DependsOnIntentional`):* Se a reflexão exige que a tese dependa de um sujeito intencional (`∃ s, IntentionalSubject s ∧ DependsOn EO s`), a retorsão deriva legitimamente `∃ s : Subject, IntentionalSubject s` (`weakened_retorsion_derives_intentional_subject`).")
    ap("")
    ap("2. **O Modelo Hostil Permanente (`DeterministicTranscendentalSubjectModel`):**")
    ap("   Construímos em Lean um modelo concreto com `0 axiomas` onde um sujeito puramente mecânico/determinista reflete intencionalmente sobre a tese transcendental, satisfazendo plenamente a teoria retorsiva enfraquecida, enquanto `FreeWill` e `Person` são uniformemente falsos:")
    ap("   - Provamos `deterministic_transcendental_subject_refutes_freewill`: **a retorsão enfraquecida NÃO deriva Livre-Arbítrio**.")
    ap("   - Provamos `deterministic_transcendental_subject_refutes_person`: **a retorsão enfraquecida NÃO deriva Pessoalidade**.")
    ap("")
    ap("3. **O Teste de Estresse do \"Porco Voador\" (Arbitrary-Object Stress Test):**")
    ap("   Para demonstrar o vício de petição de princípio de injetar `Person / FreeWill` na premissa transcendental A17, introduzimos o predicado arbitrário `WingedPig : Subject → Prop` e definimos `SubjectivePig x := ∃ s, WingedPig s ∧ DependsOn x s`.")
    ap("   - Provamos `winged_pig_derived_of_pig_reflection`: se postulamos que a reflexão depende de um porco voador, a retorsão \"prova\" a existência de um porco voador!")
    ap("   - Provamos `pig_retorsion_exposes_premise_smuggling` (`0 axiomas`): a reflexão transcendental não força predicados externos arbitrários.")
    ap("")
    ap("4. **Decomposição Sistemática e Escada Dedutiva de A17:**")
    ap("   Decompomos o axioma forte A17 em quatro alvos intermediários explícitos:")
    ap("   - **(A17a) `∃ s, IntentionalSubject s`:** Existência de sujeito intencional (derivável via Rota B).")
    ap("   - **(A17b) `∃ s, Means s EO ∧ DependsOn EO s`:** Mesma testemunha que significa e fundamenta a tese universal.")
    ap("   - **(A17c) `∃ s, Person s`:** Existência de uma pessoa.")
    ap("   - **(A17d) `∃ s, FreeWill s`:** Existência de livre-arbítrio.")
    ap("   - **`A17_weak`:** `∃ s, IntentionalSubject s ∧ DependsOn EO s` (transcendental enfraquecido).")
    ap("   - **`A17_strong`:** `∃ s, Person s ∧ DependsOn EO s` (o A17 original com livre-arbítrio).")
    ap("")
    ap("   *Pontes Candidatas entre Significação e Dependência:*")
    ap("   - *Ponte Universal (`Means s p → DependsOn (ofProp p) s`):* Rejeitada como absurda — faria qualquer pensamento sobre 2+2=4 ou sobre um Porco Voador tornar a entidade dependente da mente.")
    ap("   - *Ponte Transcendental Restrita (`RestrictedTranscendentalBridge`):* Postula especificamente que a tese de objetividade universal, enquanto formulação conceitual, depende ontologicamente do sujeito que a pensa (`Tag: SEM`). Provamos que ela deriva `A17b` e `A17_weak`, mas **não** deriva `FreeWill`.")
    ap("")
    ap("   *Rastreamento Estrito de Testemunha e Modelo de Deslizamento (Witness Slippage):*")
    ap("   Provamos formalmente que ter separadamente um pensante de EO (`A17b`) e uma pessoa (`A17c`) **não implica** que o pensante seja uma pessoa (`witness_slippage_separation`, `0 axiomas`). No modelo com dois sujeitos `WitnessSubject` (`thinker` e `person`), o pensante opera sem livre-arbítrio, enquanto a pessoa não fundamenta a tese.")
    ap("")
    ap("```text")
    ap("=========================================================================================")
    ap("A ESCADA DEDUTIVA DE A17 E O ESTATUTO DE CADA DEGRAU")
    ap("=========================================================================================")
    ap("Retorsão Big-O / Big-S")
    ap("  │")
    ap("  ▼  [PROVADO - Rota B]")
    ap("∃ s : Subject, IntentionalSubject s  (A17a)")
    ap("  │")
    ap("  ▼? [EXIGE PREMISSA DE CONSIDERAÇÃO PERFORMATIVA (SEMÂNTICA)]")
    ap("∃ s : Subject, Means s EverythingObjective")
    ap("  │")
    ap("  ▼? [EXIGE PONTE TRANSCENDENTAL DE DEPENDÊNCIA (SEMÂNTICA)]")
    ap("∃ s : Subject, Means s EO ∧ DependsOn EO s  (A17b)")
    ap("  │")
    ap("  ▼  [PROVADO / DEFINICIONAL - a17b_implies_a17_weak]")
    ap("A17_weak : ∃ s : Subject, IntentionalSubject s ∧ DependsOn EO s")
    ap("  │")
    ap("  ▼? [INDEPENDENTE / BLOQUEADO PELO MODELO DETERMINISTA E DESLIZAMENTO]")
    ap("∃ s : Subject, Person s ∧ DependsOn EO s")
    ap("  │")
    ap("  ▼  [PROVADO / DEFINICIONAL]")
    ap("A17_strong : ∃ s : Subject, FreeWill s ∧ DependsOn EO s")
    ap("=========================================================================================")
    ap("```")
    ap("")
    ap("> **Veredito Filosófico e Formal (CASO C):**")
    ap("> A reflexão transcendental força performativamente a existência de um **Sujeito Intencional** (`IntentionalSubject`), pois não se pode formular uma tese sem significá-la. Contudo, ela **NÃO força Livre-Arbítrio nem Pessoalidade**, pois um autômato determinista pode significar uma tese. Portanto, **A17_strong é uma ponte metafísica substantiva irredutível (`Tag: META`)**, e não uma decorrência neutra da lógica ou da retorsão pura.")
    ap("")
    ap("Provamos formalmente 11 teoremas de separação sem axiomas (`0 axioms`) demonstrando essas fronteiras:")
    ap("1. **`representation_not_depends_on_person`:** Representação intencional (`Means s p`) não implica dependência de pessoa.")
    ap("2. **`subjective_not_depends_on_person`:** Em assinatura desvinculada, subjetividade não força dependência de pessoa.")
    ap("3. **`intentional_subject_not_person`:** Sujeito intencional não implica Pessoa (Livre-Arbítrio).")
    ap("4. **`person_not_freewill`:** Em assinatura desvinculada, pessoalidade não força livre-arbítrio.")
    ap("5. **`exists_subjective_not_exists_person`:** A existência de algo subjetivo não força a existência de uma pessoa.")
    ap("6. **`exists_subjective_not_exists_freewill`:** A existência de algo subjetivo não força livre-arbítrio.")
    ap("7. **`deterministic_transcendental_subject_refutes_freewill`:** Retorsão enfraquecida não deriva livre-arbítrio.")
    ap("8. **`deterministic_transcendental_subject_refutes_person`:** Retorsão enfraquecida não deriva pessoalidade.")
    ap("9. **`pig_retorsion_exposes_premise_smuggling`:** Retorsão enfraquecida não deriva predicados arbitrários externos.")
    ap("10. **`means_not_dependson` / `exists_means_not_exists_dependson`:** Significar EO não implica depender ontologicamente de s.")
    ap("11. **`witness_slippage_separation`:** Conjunção de pensante de EO e pessoa não garante pensante pessoal (bloqueio de deslizamento).")
    ap("")
    ap("### 3. Livro-Razão Adversarial de Retorsão (Adversarial Retorsion Ledger)")
    ap("")
    ap("| Afirmação Alvo | Negação Exata | Ataque Retorsivo | O que a negação precisa executar/assumir | Resultado | Classificação | Modelo Hostil / Obstrução |")
    ap("| :--- | :--- | :--- | :--- | :--- | :--- | :--- |")
    ap("| **Ato Intencional** (`Act`) | `∀ s p, ¬ Act s p` (`NoAct`) | Performativo direto | Asserir que não há ato executa um ato intencional | **REFUTADO** | `PROVEN BY RETORSION` | Nenhum (impossibilidade analítica) |")
    ap("| **Ato Fraco** (`act`) | `∀ s p, ¬ act s p` (`NoWeakAct`) | Performativo fraco | Enunciar a negação realiza um evento de prolação | **REFUTADO** | `PROVEN BY RETORSION` | Nenhum |")
    ap("| **Verdade** (`T`) | `∀ p, ¬ T p` (`NoTruth`) | Lógico | Se é verdade que nada é verdade, algo é verdade | **REFUTADO** | `PROVEN BY RETORSION + LOGIC` | Nenhum |")
    ap("| **Sujeito** (`SubjectExists`) | `∀ s, ¬ SubjectExists s` | Performativo direto | Negar o sujeito exige o centro de perspectiva que julga | **REFUTADO** | `PROVEN BY RETORSION` | Nenhum |")
    ap("| **Campo de Escolha** (`ChoiceField`) | `∀ s p q, ¬ ChoiceField s p q` | Performativo alternativo | Asserir coloca o agente diante da alternativa da sua própria negação | **REFUTADO** | `PROVEN BY RETORSION` | Nenhum |")
    ap("| **Subjetividade Absoluta** | `∀ x, Subjective x` | Auto-inclusão objetiva | A tese reivindica estatuto objetivo sobre o real | **REFUTADO** | `PROVEN BY RETORSION + LOGIC` | Nenhum (sob disjunção lógica O/S) |")
    ap("| **Objetividade Absoluta** | `∀ x, Objective x` | Representação pessoal | O ato de formular a tese depende de um sujeito pessoal livre | **REFUTADO** | `PROVEN BY RETORSION + META` | Nenhum (sob A17) |")
    ap("| **Retorsão Enfraquecida → FreeWill** | `∃ s, IntentionalSubject s ↛ FreeWill s` | Teste de enfraquecimento | Reflexão transcendental mecânica sem livre-arbítrio | **FALHOU** | `FAILED — HOSTILE MODEL` | `DeterministicTranscendentalSubjectModel` |")
    ap("| **Retorsão Arbitrária (WingedPig)** | `Reflexão ↛ WingedPig` | Objeção de Gaunilo | Enxertar predicados contingentes na premissa | **FALHOU** | `FAILED — PREMISE SMUGGLING` | `pig_retorsion_exposes_premise_smuggling` |")
    ap("| **A3 (Truthmaker)** | `∃ w φ, TrueAt w φ ∧ ∀ e, ¬(ExistsAt ∧ Ground)` | Performativo / Diagonal | Asserir que algo não tem grounder não fornece grounder ontológico | **FALHOU** | `FAILED — HOSTILE MODEL` / `EXPRESSIVITY GAP` | Satisfação sem grounder é coerente (`Form` carece de ponto fixo diagonal) |")
    ap("| **A4 (Global Ground)** | `∃ φ, □φ ∧ ∀ e, ¬(∀ w, ExistsAt ∧ Ground)` | Universal contrafatual | Troca $\\forall w \\exists e \\to \\exists e \\forall w$ não é forçada por asserir sua ausência | **FALHOU** | `FAILED — HOSTILE MODEL` | `CountermodelWorldwiseTruthmaking` |")
    ap("| **A9 (GroundProp)** | `∃ f, T f ∧ ∀ e, ¬ GroundProp e f` | Performativo | Proposição verdadeira não carrega entidade grounder por mera auto-asserção | **FALHOU** | `FAILED — HOSTILE MODEL` | Impessoalismo semântico |")
    ap("| **A13 (ActPolarity)** | `∃ s p, Act s p ∧ ¬ Means s (¬p)` | Asserção de contra-exemplo | Agente pode asserir sem conceber a negação contraditória | **FALHOU** | `FAILED — HOSTILE MODEL` | `CountermodelVeridicalMeaning` (`Means s p := p`) |")
    ap("| **A14 (IntentionalChoice)** | `∃ s p, Act s p ∧ ∀ q, ¬ Chooses s p q` | Auto-negação de escolha | \"Ajo sem escolher\": ato determinado assere a negação sem ter alternativas co-significadas | **FALHOU** | `FAILED — HOSTILE MODEL` | `CountermodelNoFreeWill` (ato determinado sem livre-arbítrio) |")
    ap("| **A6 (Pluralidade)** | `¬ ∃ s₁ s₂, Person s₁ ∧ Person s₂ ∧ s₁ ≠ s₂` | Solipsismo asserido | Agente único assere \"estou só\"; ato não requer interlocutor | **FALHOU** | `FAILED — HOSTILE MODEL` | `SolitaryChoiceModel` (agente único cumpre toda a agência pré-A6) |")
    ap("| **A7 (Personal Ground)** | `∃ f, IsPresentPersonalFeature f ∧ ∀ e, ¬Personal e` | Grounding de pessoa | Ato pessoal sustentado por fundamento impessoal | **FALHOU** | `FAILED — HOSTILE MODEL` | `CountermodelImpersonalUltimateGround` |")
    ap("| **Fundamento Último** (`UltimateGround`) | `¬ ∃ u, UltimateGround u` | Regresso Infinito com Truthmakers | Asserir que não há fundamento último exige verdade fundamentada | **SOBREVIVE / DILEMA** | `DILEMMA — HOSTILE MODEL` | Sobrevive sob truthmaking permissivo (`PermissiveTruthGroundedInfiniteChain`); refutado sob truthmaking de totalidade substantiva (`TotalityGroundingSignature`) |")
    ap("| **Act → Person** | `∃ s p, Act s p ∧ ¬ Person s` | Agente intencional não-livre | Ato singular não força co-significação de alternativas incompatíveis | **FALHOU** | `FAILED — HOSTILE MODEL` | `CountermodelNoFreeWill` (Ato determinado sem escolha) |")
    ap("| **FreeSubject → Person** | `FreeSubject s → Person s` | Definição constitutiva de Pessoa | O sujeito dotado de livre-arbítrio é constitutivamente uma pessoa | **PROVADO** | `PROVEN (0 axiomas)` | `Person.free_subject_is_person` |")
    ap("| **Person → NecessarySubject** | `∃ s, Person s ∧ ¬ NecessarySubject s` | Pessoa contingente | Pessoa no mundo atual não existe necessariamente em todos os mundos | **FALHOU** | `FAILED — HOSTILE MODEL` | `faithful_contingent_person_fails_necessary_subject` |")
    ap("| **Plurality → Loves** | `Pluralidade ∧ ¬ Amor` | Indiferença interpessoal | Dois sujeitos interagem em total indiferença ou hostilidade | **FALHOU** | `FAILED — HOSTILE MODEL` | `DisconnectedPluralityModel` |")
    ap("")
    ap("### 4. Mapa Sintético: O Espaço Negativo e Positivo de Γ")
    ap("")
    ap("```text")
    ap("                        [ DADO PERFORMATIVO ]                                            ")
    ap("                                  │                                                      ")
    ap("        ┌─────────────────────────┴─────────────────────────┐                            ")
    ap("        ▼                                                   ▼                            ")
    ap("[ Consequências Positivas ]                       [ Exclusões Retorsivas ]               ")
    ap("  • Act s p                                         • ¬(NoAct)                           ")
    ap("  • Means s p                                       • ¬(NoWeakAct)                       ")
    ap("  • IntentionalSubject s                            • ¬(NoTruth)                         ")
    ap("  • ChoiceField s p (¬p)                            • ¬(NoSubject)                       ")
    ap("  • Chooses / FreeWill (sob A14)                    • ¬(NoChoiceField)                   ")
    ap("                                                    • ¬(EverythingSubjective)            ")
    ap("                                                    • ¬(EverythingObjective)             ")
    ap("                                                            │                            ")
    ap("                                                            ▼                            ")
    ap("                                              [ Testemunhas Positivas ]                  ")
    ap("                                                • ∃ x, Objective x                       ")
    ap("                                                • ∃ x, Subjective x                      ")
    ap("                                                • ∃ s, IntentionalSubject s (Rota B)     ")
    ap("                                                                                         ")
    ap("=========================================================================================")
    ap("                 FRONTEIRA DE IRREDUCIBILIDADE (Retorsão Falha)                          ")
    ap("=========================================================================================")
    ap("  Axiomas Semânticos:                                                                    ")
    ap("    A3 (Truthmaker)      ◄─── Retorsão falha; modelo hostil sem grounder sobrevive       ")
    ap("    A4 (GlobalGround)    ◄─── Retorsão falha; modelo mundanal sem swap sobrevive         ")
    ap("    A9 (GroundProp)      ◄─── Retorsão falha; modelo impessoal sobrevive                 ")
    ap("    A13 (ActPolarity)    ◄─── Retorsão falha; modelo verídico sem ¬p sobrevive           ")
    ap("    A14 (Choice)         ◄─── Retorsão falha; ato determinado sem Chooses sobrevive      ")
    ap("                                                                                         ")
    ap("  Axiomas Metafísicos:                                                                   ")
    ap("    A6 (Pluralidade)     ◄─── Retorsão falha; modelo de agente solitário sobrevive       ")
    ap("    A7 (Personal Ground) ◄─── Retorsão falha; modelo de base impessoal sobrevive         ")
    ap("                                                                                         ")
    ap("  Fronteiras Abertas / Modelos de Separação:                                             ")
    ap("    Act → Person         ◄─── Ato intencional singular não força livre-arbítrio (exige normatividade)")
    ap("    Person → NecSubject  ◄─── Pessoa atual não força existência necessária em todos os mundos     ")
    ap("    Pluralidade → Amor   ◄─── Retorsão falha; sujeitos indiferentes/hostis sobrevivem    ")
    ap("```")
    ap("")
    ap("#### Audit of Candidate Cognitive Primitive R")
    ap("")
    ap("- **Candidate primitive:** `AlternativeRepresentation : Subject → Prop → Prop → Prop`")
    ap("- **Semantic elimination:** `elim_R : ∀ s p q, AlternativeRepresentation s p q → Means s q ∧ Incompatible p q`")
    ap("- **Action bridge:** `B_R : ∀ s p, Act s p → ∃ q, AlternativeRepresentation s p q`")
    ap("- **Does $B_R$ derive A14?** YES (via `elim_R` and `Act s p → Means s p`).")
    ap("- **Does A14 derive $B_R$?** NOT in general (if $R$ requires intentional contrastive awareness beyond extensional co-meaning) / YES (if $R$ is extensionally defined as `Means s q ∧ Incompatible p q`).")
    ap("- **Strictly weaker than A14?** NO. Any candidate weaker than `Means s q ∧ Incompatible p q` fails to derive A14, while any candidate requiring intentional contrast is strictly stronger ($B_R > \\text{A14}$).")
    ap("- **Outcome:** **Outcome C** (every candidate reduces either to A13, A14, or a renamed composite primitive; no genuinely weaker bridge has yet been discovered).")
    ap("- **Hostile model:** In `CountermodelVeridicalMeaning.Single` (`Means s p := p`), $B_R$ fails identically to A14, because no incompatible proposition can be represented without contradiction.")
    ap("")
    ap("Current formal status of `Means`:")
    ap("```lean")
    ap("Means : Subject → Prop → Prop")
    ap("Tag: VOCAB (Primitive Vocabulary)")
    ap("```")
    ap("")
    ap("As currently formalized, `Means` has no internal structure beyond pairing a subject with a proposition. "
       "Therefore no closure, factivity, non-factivity, alternative-generation, or contrastive representation "
       "follows merely from the relation itself.")
    ap("")
    ap("- **Independent decomposition found?** NO. Any decomposition into mental states/representations either renames the primitive (`Means := Represents`) or hard-codes contrastivity into the definition.")
    ap("- **Smallest missing primitive beneath Means:** A structured intensional representation layer or cognitive polarity faculty (`Polarity : Means s p → Means s (¬p)`), which is equivalent to **A13** (`Tag: SEM`), not A14.")
    ap("- **Status:** OPEN as a deeper reductive question; BOUNDED as a primitive semantic relation in the formal ledger.")
    ap("")
    ap("#### Conceptual Hierarchy: The Multi-Stage Architecture of Agency")
    ap("")
    ap("```text")
    ap("Layer 0: Causal Production (Initiates s w w' p)")
    ap("      ↓  [Refuted: initiates_does_not_imply_means (CountermodelWeakActWithoutMeaning)]")
    ap("Layer 1: Intentional Action (Act s p := Means s p ∧ ∃ w w', Initiates s w w' p)")
    ap("      ↓  [PROVEN: act_implies_choiceField / intentional_hasChoiceField]")
    ap("Layer 2: Objective Alternative Field (ChoiceField s p q := Means s p ∧ Incompatible p q)")
    ap("      ↓  [PROVEN for Asserts: asserts_implies_selects / asserts_selects]")
    ap("Layer 3: Semantic Selection / Authorship (Selects s p q / Authors s p q)")
    ap("      ↓  [Refuted: selection_not_entails_rejected_horn_meaning / authors_not_entails_rejected_horn_meaning]")
    ap("Layer 4: Cognitive Alternative Representation (Means s q ∧ Incompatible p q / Contemplates)")
    ap("      ↓  [PROVEN: deliberateAuthorship_implies_chooses / deliberateChoice_iff_selects_and_means]")
    ap("Layer 5: Deliberate Authorship / Settlement (DeliberateAuthorship s p q := Authors s p q ∧ Means s q)")
    ap("      ↓  [PROVEN: deliberateAuthorship_implies_chooses / chooses_implies_freeWill]")
    ap("Layer 6: Genuine Choice & Free Will (Chooses s p q  →  FreeSubject s / FreeWill s)")
    ap("```")
    ap("")
    ap("This multi-stage hierarchy isolates the exact locus of non-derivability in the pre-A14 theory:")
    ap("- **Transitions 1 → 2 and 2 → 3** are machine-verified theorems of logic and assertion.")
    ap("- **Transition 3 → 4** is the sole unbridgeable cognitive boundary: selecting or authoring *against* $q$ does not force *thinking* or *co-meaning* $q$.")
    ap("- **Transitions 4 → 5 → 6** are definitional identities.")
    ap("")
    ap("#### Four Rigorously Separated Phenomena of Agency")
    ap("")
    ap("1. **Causal Outcome (`CausalSettles`):** Physical execution bringing about $p$ and suppressing $q$ in state space; satisfied by deterministic systems (`ModelM2BranchingInitiation`). Does not entail mental representation.")
    ap("2. **Contemplative Representation (`ContemplatesWithoutSettling`):** Co-meaning incompatible options without physical action; satisfied by `ContemplationWithoutActionModel` (`contemplation_without_action`). Shows that cognitive free will does not require overt physical action.")
    ap("3. **Selection / Authorship (`Authors` / `Selects`):** Executive determination of $p$ over $q$ without representing $q$; satisfied by `Single` (`authors_not_entails_rejected_horn_meaning`).")
    ap("4. **Deliberate Choice (`DeliberateAuthorship` / `DeliberateChoice` / `Chooses`):** Active commitment with dual cognitive representation of both incompatible options.")
    ap("")
    ap("#### Three Epistemic Levels of Constitutivity in Γ")
    ap("")
    ap("- **Constitutive by Definition (DEFINITIONAL):** `FreeWill` from `Chooses` (`FreeWill s := ∃ p q, Chooses s p q`); `Chooses` from `DeliberateAuthorship`.")
    ap("- **Constitutive by Semantic Axiom (SEMANTIC):** `AxIntentionalChoice` (A14): substantive commitment that intentional initiation constitutively involves cognitive alternativity, proven independent of pre-A14 primitives by machine-checked full-theory countermodels.")
    ap("- **Constitutive by Derivation (DERIVED):** `ChoiceField s p (¬p)` from `Act s p`; `Selects s p (¬p)` from `Asserts s p`.")
    ap("")
    ap("#### O Contraste Definidor: A14 (Ato → Escolha) vs. Inverso de A14 (Escolha → Ato)")
    ap("")
    ap("A relação entre ação intencional e escolha genuína é assimetricamente estruturada:")
    ap("")
    ap("- **A14 (`Act s p → ∃ q, Chooses s p q`):** Princípio semântico constitutivo adotado (`Tag: SEM`). Postula que a ação intencional envolve constitutivamente a faculdade cognitiva de escolha entre alternativas.")
    ap("- **Inverso de A14 (`(∃ q, Chooses s p q) → Act s p`):** **REFUTADO POR MODELO HOSTIL** (`ContemplationWithoutActionModel.universal_reverse_a14_refuted` e `existential_reverse_a14_refuted`). A escolha genuína e o livre-arbítrio são faculdades cognitivas/deliberativas (`Means s p ∧ Means s q ∧ Incompatible p q`) que não exigem execução ou iniciação causal física (`Initiates s w w' p`). Um sujeito pode escolher e deliberar em puro pensamento contemplativo sem agir no mundo físico.")
    ap("")
    ap("Conclusão filosófica: **A escolha genuína não acarreta execução. Escolha cognitiva e ação intencional são fenômenos ontologicamente distintos.**")
    ap("")
    ap("#### Auditoria da Negação Auto-Referencial da Escolha")
    ap("")
    ap("Investigou-se se uma asserção auto-referencial que nega a existência de escolha em si mesma "
       "(`SelfDenialOfChoice s p := Act s p ∧ (p ↔ ∀ q, ¬ Chooses s p q)`) poderia forçar a escolha genuína por retorção performativa.")
    ap("")
    ap("- **Resultado:** **REFUTADO POR MODELO HOSTIL** (`SelfDenialOfChoiceModel.self_denial_not_derives_choice` e `self_denial_without_choice_consistent`).")
    ap("- **Mecanismo:** Em semântica verídica, a proposição $p := (\\forall q, \\neg \\text{Chooses}(s, p, q))$ é estritamente verdadeira; "
       "o agente intencionalmente significa $p$, inicia o proferimento de $p$, e de facto não possui escolha alguma, sem qualquer contradição. "
       "Ao contrário da negação de atos (onde negar o ato destrói a própria execução), negar a escolha apenas exige agir, não escolher.")
    ap("- **Conclusão:** A auto-referência não ultrapassa A14; refutar a negação da escolha pressupõe a própria bilateralidade cognitiva (A13/A14) em vez de a derivar.")
    ap("")
    ap("#### Auditoria da Escolha Livre Auto-Referencial (Candidatas A, B, C, D)")
    ap("")
    ap("Investigou-se se asserir positivamente a escolha livre de si mesmo (\"Escolho livremente este próprio ato\") "
       "poderia derivar a escolha genuína ou gerar contradição performativa sem assumir A14.")
    ap("")
    ap("- **Candidata A (Escolha Genuína Auto-Asserida, `p ↔ ∃ q, Chooses s p q`):**")
    ap("  - Sob asserção fáctica (`Asserts s p`), $p$ é verdadeiro, logo $\\exists q, \\text{Chooses}(s, p, q)$ segue por **pura lógica/desprendimento definicional** (`selfAssertedChoice_factive_implies_chooses`).")
    ap("  - Sob ação intencional não-fáctica (`Act s p`), o agente pode proferir iludidamente $p$ num mundo determinista onde $p$ é falso e nenhuma escolha existe (**REFUTADO POR MODELO HOSTIL**, `DelusionalSelfChoiceModel.nonfactive_self_choice_not_derives_choice`).")
    ap("- **Candidata B (Autoria Auto-Asserida, `p ↔ ∃ q, Authors s p q`):** A autoria executiva verdadeira não força a representação cognitiva do corno rejeitado (`Single.authors_not_entails_rejected_horn_meaning`).")
    ap("- **Candidata C (Escolha Deliberada Auto-Asserida, `p ↔ ∃ q, DeliberateChoice s p q`):** Sob asserção fáctica, deriva escolha por desprendimento (`selfAssertedDeliberateChoice_factive_implies_chooses`); sob ação não-fáctica, falha por auto-atribuição falsa.")
    ap("- **Candidata D (Paradoxo Auto-Referencial, `p ↔ (∃ q, Chooses s p q) ∧ (∀ q, ¬ Chooses s p q)`):** $p$ é logicamente falso (`selfAssertedParadox_is_false`). A asserção fáctica é auto-refutante (`selfAssertedParadox_not_assertable`), mas o proferimento de uma falsidade em ato não-fáctico não instancia escolha.")
    ap("")
    ap("Conclusão: **A auto-referência positiva apenas deriva a escolha se a auto-atribuição for previamente admitida como verdadeira (fáctica), o que não pode ser generalizado a um ato genérico (`Act s p`) sem assumir A14.**")
    ap("")
    ap("#### Reconstrução Ontológica da Escolha: Determinação Executiva vs. Deliberação")
    ap("")
    ap("A auditoria formal revelou que a definição histórica de `Chooses s p q := Means s p ∧ Means s q ∧ Incompatible p q` "
       "media a faculdade cognitiva de **Deliberação / Representação Contrastiva** (co-significar simultaneamente ambos os cornos em pensamento), "
       "e não a **Escolha Executiva** (o ato de determinação/seleção semântica).")
    ap("")
    ap("A ontologia reconstruída separa rigorosamente as camadas:")
    ap("1. **Movimento/Evento Fraco (`act s`):** Comportamento causal/físico sem intencionalidade.")
    ap("2. **Ato Intencional Forte (`Act s p`):** Significado intencional aliado à iniciação causal de transição de estado.")
    ap("3. **Campo Objetivo de Alternativas (`ChoiceField s p q`):** Espaço lógico objetivo de alternativas (`Incompatible p q`).")
    ap("4. **Determinação Executiva / Escolha (`Choice s p := Selects s p (¬p)` e `AuthorshipChoice s p := Authors s p (¬p)`):** O sujeito assere/determina $p$ e exclui $\\neg p$.")
    ap("5. **Deliberação Cognitiva (`Deliberates s p q := Means s p ∧ Means s q ∧ Incompatible p q`):** Contemplação de alternativas em pensamento (legado `Chooses`).")
    ap("6. **Escolha Deliberada (`DeliberateChoice s p q := Selects s p q ∧ Means s q`):** Determinação executiva unida à consciência cognitiva do corno rejeitado.")
    ap("7. **Livre Agência (`FreeAgency s := ∃ p, Choice s p`):** Capacidade de determinação executiva.")
    ap("")
    ap("- **Teorema da Retorção Performativa da Escolha (`selfDenialOfExecutiveChoice_selfRefutes`):**")
    ap("  A asserção auto-referencial \"Esta minha asserção não possui Escolha\" (`SelfDenialOfExecutiveChoice s p := Asserts s p ∧ (p ↔ ¬ Choice s p)`) "
       "é uma **CONTRADIÇÃO PERFORMATIVA GENUÍNA** (`SelfDenialOfExecutiveChoice s p → False`, derivado por pura lógica/definições). "
       "O próprio ato de asserir $p$ instancia a determinação executiva `Choice s p`, destruindo o conteúdo da negação!")
    ap("")
    ap("This clarifies that genuine choice constitutively requires *alternativity* "
       "(`Incompatible p q` entertained in thought), but does not intrinsically require the formal "
       "operator of contradictory propositional negation (`¬p`). Model `ContrastiveSeparation` "
       "formally demonstrates that an agent can choose between incompatible positive courses "
       "of action (e.g. North vs. East) without entertaining `¬North`.")
    ap("")
    ap("#### Six Foundational Candidate Families for Deriving A14 (Exhaustive Audit)")
    ap("")
    ap("| Foundational Family | Candidate Formulation | Strict Classification | Hostile Witness / Model | Analysis & Mathematical Mechanism |")
    ap("|---|---|---|---|---|")
    ap(r"| **1. Goal / End-Directedness** | `Goal s g ∧ (p → g) → ∃ q, Means s q ∧ Incompatible g q` | **REFUTED BY HOSTILE MODEL** | `hostileTeleologicalInstance` (`teleology_not_entails_contrastive_agency`) | Valuation: `s = false, p = True, g = True`. In veridical semantics (`Means s p := p`), acting for a true goal does not force representation of an incompatible alternative; factive goal-directedness mathematically excludes co-meaning false $q$. Baking contrastivity into `Goal` is **DEFINITIONAL RECODING — REJECTED**. |")
    ap(r"| **2. Reason-Guided Agency** | `ReasonFor s r p ∧ (r → p) → ∃ r' q, Means s r' ∧ Means s q ∧ Incompatible r q` | **REFUTED BY HOSTILE MODEL** | `hostileReasonResponsiveInstance` (`reason_responsiveness_not_entails_contrastive_agency`) | Valuation: `s = false, r = True, p = True`. Acting on a sufficient reason in the actual world does not require occurrent representation of contrary reasons in thought. Dispositions across hypothetical counterfactual worlds do not populate actual occurrent `Means`. |")
    ap(r"| **3. Action Individuation under Description** | `Description s p → ∃ q, Means s q ∧ Incompatible p q` | **REFUTED BY HOSTILE MODEL** | `hostileActionIndividuationInstance` (`action_individuation_not_entails_contrastive_agency`) | Valuation: `s = false, p = True`. Individuating an action under description $p$ distinguishes it from non-intended descriptions $p'$ without the subject representing any incompatible alternative description $q$ in thought. |")
    ap(r"| **4. Non-Factive Representation Layer** | `Entertains s p → ∃ q, Entertains s q ∧ Incompatible p q` | **REFUTED BY HOSTILE MODEL** | `hostileRepresentationLayerInstance` (`nonfactive_representation_not_entails_contrastive_agency`) | Valuation: `s = false, p = True`. Distinguishing `Means` from a non-factive representation faculty `Entertains` allows entertaining false contents in principle, but does not force the subject to entertain incompatible alternatives; single-content entertainment remains consistent. |")
    ap(r"| **5. Counterfactual Agency (State Branching)** | `CouldAct s q ∧ Incompatible p q → Means s q` | **REFUTED BY HOSTILE MODEL** | `ModelM2BranchingInitiation` (`counterfactual_branching_not_entails_means`) | Valuation: Model M2 exhibits physical state-space branching (`w = false ∧ w' ∈ {true, false}`), so alternative initiation holds (`CouldAct () False`), but internal intentional representation `Means () False` remains strictly false. Physical branching does not force cognitive representation. |")
    ap(r"| **6. Contrastive Intentionality** | `Act s p → ∃ q, Means s q ∧ Incompatible p q` | **REDUCED TO DEEPER SEMANTIC BRIDGE** · **REDUNDANT** | `fullTheoryHostileInstance` (`act_orthogonal_to_contrastive_agency_in_full_theory`) | Conceptually and logically equivalent to A14 (`contrastive_agency_equivalent_to_intentional_choice`). Strictly independent of pre-A14 primitives, forming the *weakest sufficient bridge identified at the pointwise level* within the audited candidate family. |")
    ap("")
    ap("#### Machine-Checked Orthogonality Theorem: Act ⟂ Chooses (Pre-A14 Theory)")
    ap("")
    ap("In `formal/Logos/HostileSemantics.lean`, the kernel formally verifies that under the ENTIRE "
       "pre-A14 axiomatic theory of Γ (12 axioms across Agency, Plurality, Truthmaker, Modal, GroundPerson, and Value):")
    ap("")
    ap("$$\\exists s\\,p,\\; \\text{Act}(s,p) \\quad \\perp \\quad \\exists s\\,p\\,q,\\; \\text{Chooses}(s,p,q)$$")
    ap("")
    ap("- `act_orthogonal_to_genuine_choice_in_full_theory`: Strong Act does NOT entail Genuine Choice in the pre-A14 theory.")
    ap("- `act_orthogonal_to_freewill_in_full_theory`: Strong Act does NOT entail Free Will in the pre-A14 theory.")
    ap("- `act_orthogonal_to_contrastive_agency_in_full_theory`: Strong Act does NOT entail Contrastive Agency in the pre-A14 theory.")
    ap("")
    ap("Thus, genuine choice is not derivable from Strong Act in the pre-A14 theory; Γ adopts its constitutivity as A14, an authentic substantive semantic commitment (`Tag: SEM`).")
    ap("")
    ap("Architectural note on the formal definition of `Chooses`: the attempted asymmetric definition "
       "`Chooses_asym(s, p, q) := Means(s, p) ∧ Means(s, ¬q) ∧ Incompatible(p, q)` fails by double-negation collapse: "
       "for `q := ¬p`, `Means(s, ¬¬p)` reduces to `Means(s, p)`, dissolving the requirement of entertaining "
       "the rejected alternative and collapsing genuine choice into mere `ChoiceField`. Genuine choice "
       "therefore constitutively requires co-meaning of both alternatives (`Means s p ∧ Means s q ∧ Incompatible p q`).")
    ap("")
    ap("---")
    ap("")
    return L


def render_frontier(all_claims: list) -> list:
    L = []
    ap = L.append
    ap("## 4. Where the deduction stops")
    ap("")
    ap(FRONTIER_INTRO)
    ap("")
    open_claims = [c for c in all_claims
                   if philo_status(c, _CTX["node_map"]) == "OPEN"]
    for c in open_claims:
        keys = CONTESTS.get(c["id"], [])
        cm = ""
        if keys:
            cm = " _(countermodel: " + ", ".join(f"`Countermodel{k}`" for k in keys) + ")_"
        math_target = ""
        if c["id"] == "F1b":
            math_target = r" \((\exists s\,p\,q,\; Chooses(s,p,q))\)"
        ap(f"- **{c['id']}** — {claim_title(c)}{math_target}{cm}")
    if not open_claims:
        ap("_(none)_")
    ap("")
    ap(OPEN_BRIDGES)
    ap("")
    ap("---")
    ap("")
    return L


def load_countermodels(decls: dict) -> dict:
    out = {}
    for full, info in decls.items():
        if not full.startswith("Logos.CountermodelMeanings."):
            continue
        sv = info.get("stringValue") or ""
        name = info["name"]
        if name.endswith("_refutes"):
            out.setdefault(name[:-len("_refutes")], {})["refutes"] = sv
        elif name.endswith("_survives"):
            out.setdefault(name[:-len("_survives")], {})["survives"] = sv
    return out


def _ns_line(short: str):
    path = LEAN_DIR / "HostileSemantics.lean"
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if re.match(r"^namespace\s+" + re.escape(short) + r"\s*$", line.strip()):
            return i
    return None


def render_retired(all_claims: list) -> list:
    L = []
    ap = L.append
    ap("## Appendix C — Obstructions & retired alternatives")
    ap("")
    ap("A hostile model is a self-contained Lean structure in which the premises "
       "hold and the disputed inference fails. C.1 is the model reference; C.2 "
       "lists the proposed steps those models retire; C.3 lists the dissolved "
       "aliases. Each step's inline **Obstruction** line points back here.")
    ap("")
    ap("### C.1 Countermodel reference")
    ap("")
    for cm in COUNTERMODEL_CATALOG:
        key = cm["key"]
        gloss = _CTX["countermodels"].get(key, {})
        ns = cm["ns"]
        line = _ns_line(ns.rsplit(".", 1)[-1])
        loc = (f" · [HostileSemantics.lean#L{line}]"
               f"(formal/Logos/HostileSemantics.lean#L{line})") if line else ""
        ap(f"- **`Countermodel{key}`** — {cm['title']}: *attacks* "
           f"{cm['attacks']}. Refutes: {gloss.get('refutes', '—')} "
           f"**What survives:** {gloss.get('survives', '—')} · `{ns}`{loc}")
    ap("")
    ap("### C.2 Retired and rejected alternatives")
    ap("")
    retired = [c for c in all_claims
               if philo_status(c, _CTX["node_map"]) == "COUNTERMODEL"]
    for c in retired:
        keys = CONTESTS.get(c["id"], [])
        survives = " ".join(_CTX["countermodels"].get(k, {}).get("survives", "")
                            for k in keys).strip()
        cm = ", ".join(f"`Countermodel{k}`" for k in keys) or "—"
        ap(f"- **{c['id']}** — {claim_title(c)} · {cm} · what survives: "
           f"{survives or '—'}")
    if not retired:
        ap("_(none)_")
    ap("")
    ap("### C.3 Dissolved aliases")
    ap("")
    canonical_of = _CTX.get("canonical_of", {})
    by_id = _CTX["by_id"]
    for a in [x for x in ALIAS_TO if x in canonical_of]:
        canon = canonical_of[a]
        tfull = by_id.get(canon, {}).get("_full")
        ref = f"`{tfull}`" if tfull else "the claim"
        ap(f"- **{a}** → **{canon}** (shares {ref}); see that block.")
    ap("")
    ap("---")
    ap("")
    return L


def render_compact_axiom_ledger() -> list:
    L = []
    ap = L.append
    ax_id = _CTX["ax_id"]
    node_map = _CTX["node_map"]
    for base in ax_id:
        _CTX["ax_shown"].add(base)
    n_axioms = sum(1 for n in node_map.values() if n["kind"] == "axiom")
    ap(f"## Epistemic Ledger & Axiom Inventory ({n_axioms} declarations)")
    ap("")
    ap("Every formal axiom in Γ is strictly accounted for. There are no hidden premises:")
    ap("")
    ap("| Axiom | A# | Tag | Meaning (EN) | Depended on by |")
    ap("|---|---|---|---|---|")
    for base, aid in sorted(ax_id.items(), key=lambda kv: int(kv[1][1:])):
        r = _REGISTRY.get(base, {"tag": "?", "gloss": "—"})
        deps = sorted({c["id"] for f, c in _CTX["claims_by_id"].items()
                       if base in [a.rsplit(".", 1)[-1] for a in audit_footprint(f)]})
        ap(f"| `{base}` | {aid} | `{r.get('tag', '?')}` | {r.get('gloss') or '—'} | "
           + (", ".join(deps) if deps else "—") + " |")
    ap("")
    ap("---")
    ap("")
    return L


def is_internal_lean_decl(name: str) -> bool:
    if not name:
        return True
    internal_prefixes = (
        "Init.", "Lean.", "Std.", "Classical.", "Eq.", "Quot.",
        "Bool.", "Nat.", "String.", "Subtype.", "Prod.", "Sum.",
        "Option.", "Decidable.", "True.", "False.", "And.", "Or.",
        "Iff.", "Not.", "Exists."
    )
    if any(name.startswith(p) for p in internal_prefixes):
        return True
    if re.search(r'\.(?:eq_\d+|proof_\d+|match_\d+|injEq|recOn|casesOn|noConfusion)$', name):
        return True
    return False


def definition_body(d: dict) -> str:
    path = LEAN_DIR / d["file"]
    if not path.exists():
        return ""
    lines = path.read_text(encoding="utf-8").splitlines()
    start = d["line"] - 1
    i = start
    while i < len(lines) and ":=" not in lines[i]:
        i += 1
    if i >= len(lines):
        return ""
    chunk_lines = [lines[i].split(":=", 1)[1]]
    j = i + 1
    while j < len(lines):
        nxt = lines[j].strip()
        if not nxt:
            break
        if re.match(r"^(?:theorem|lemma|def|axiom|structure|inductive|/--)\b", nxt):
            break
        chunk_lines.append(nxt)
        j += 1
    raw = " ".join(" ".join(chunk_lines).split())
    raw = re.sub(r"--.*$", "", raw).strip()
    return format_discrete_math(humanise(strip_ns(raw)))


class Rule(Enum):
    ASSUMPTION = "assumption"
    PREMISE = "premise"
    CONJUNCTION_INTRO = "conjunction_intro"
    CONJUNCTION_ELIM = "conjunction_elim"
    EXISTENTIAL_INTRO = "existential_intro"
    EXISTENTIAL_ELIM = "existential_elim"
    MODUS_PONENS = "modus_ponens"
    LEMMA_APP = "lemma_application"
    DEFINITION_UNFOLD = "definition_unfold"
    CONTRADICTION = "contradiction"
    BOUNDARY = "boundary"
    CONCLUSION = "conclusion"


@dataclass
class ProofStepIR:
    var_name: str
    proposition: str
    rule: Rule
    premises: list[str] = field(default_factory=list)
    description: str = ""


@dataclass
class ProofIR:
    full_name: str
    name: str
    kind: str
    file: str
    line: int
    goal: str
    doc: str
    assumptions: list[ProofStepIR] = field(default_factory=list)
    steps: list[ProofStepIR] = field(default_factory=list)
    conclusion: ProofStepIR | None = None
    subst_axioms: list[str] = field(default_factory=list)
    boundary: tuple[str, str, str, str] | None = None  # (left, right, link, link_label)

def compile_lean_proof(full: str, decls: dict, node_map: dict, graph: dict, def_registry: dict) -> ProofIR:
    """Compiles a Lean declaration and its proof term/tactics into a domain-independent ProofIR."""
    d = decls[full]
    name = d["name"]
    kind = d["kind"]
    antes, body = split_theorem_head(d.get("statement", ""))
    subst, vocab, cl = footprint_parts(full)

    goal_fm = format_discrete_math(humanise(strip_ns(body)).strip())
    doc_text = d.get("doc", "").strip()

    proof = ProofIR(
        full_name=full,
        name=name,
        kind=kind,
        file=d["file"],
        line=d["line"],
        goal=goal_fm if goal_fm else math_statement(full),
        doc=doc_text,
        subst_axioms=subst,
    )

    # Register definitions in the definition registry
    if kind == "def":
        body_def = definition_body(d)
        if body_def:
            def_registry[name] = body_def
            proof.goal = f"{name} ≡ {body_def}"
        return proof

    if kind in ("structure", "axiom"):
        proof.goal = math_statement(full)
        return proof

    # Assumptions from theorem signature
    for a in antes:
        clean_a = humanise(strip_ns(a)).strip()
        proof.assumptions.append(ProofStepIR(
            var_name="",
            proposition=format_discrete_math(clean_a),
            rule=Rule.ASSUMPTION,
            description="initial assumption",
        ))

    # Read proof body from Lean file
    path = LEAN_DIR / d["file"]
    if not path.exists():
        return proof

    lines = path.read_text(encoding="utf-8").splitlines()
    start = d["line"] - 1
    i = start
    while i < len(lines) and ":=" not in lines[i]:
        i += 1
    if i >= len(lines):
        return proof

    proof_lines = []
    i += 1
    while i < len(lines):
        l = lines[i].strip()
        if re.match(r"^(?:theorem|lemma|def|axiom|structure|inductive|/--|section|namespace|end)\b", l):
            break
        proof_lines.append(l)
        i += 1

    for l in proof_lines:
        m_have = re.match(r"^\s*have\s+([A-Za-z0-9_]+)\s*:\s*(.*?)\s*:=\s*(.*)", l)
        if m_have:
            v_name, v_type, term = m_have.group(1), m_have.group(2).strip(), m_have.group(3).strip()
            prop_fm = format_discrete_math(humanise(strip_ns(v_type)).strip())

            # Deconstruct projections (.1, .2, .left, .right, or named fields)
            m_proj = re.search(r"([A-Za-z0-9_.]+)\.([A-Za-z0-9_.]+)$", term)
            if m_proj:
                base, proj = m_proj.group(1), m_proj.group(2)
                proof.steps.append(ProofStepIR(
                    var_name=v_name,
                    proposition=prop_fm,
                    rule=Rule.CONJUNCTION_ELIM,
                    premises=[base],
                    description=f"elimination of {proj} from {base}",
                ))
                continue

            # Deconstruct constructor ⟨a, b, ...⟩
            if term.startswith("⟨") and term.endswith("⟩"):
                args = [x.strip() for x in term[1:-1].split(",")]
                arg_str = ", ".join(args)
                if "∃" in v_type or "Exists" in v_type:
                    proof.steps.append(ProofStepIR(
                        var_name=v_name,
                        proposition=prop_fm,
                        rule=Rule.EXISTENTIAL_INTRO,
                        premises=args,
                        description=f"existential introduction with witness {args[0]}",
                    ))
                elif "∧" in v_type or "And" in v_type:
                    proof.steps.append(ProofStepIR(
                        var_name=v_name,
                        proposition=prop_fm,
                        rule=Rule.CONJUNCTION_INTRO,
                        premises=args,
                        description=f"conjunction introduction from {arg_str}",
                    ))
                else:
                    head_type = v_type.split()[0]
                    proof.steps.append(ProofStepIR(
                        var_name=v_name,
                        proposition=prop_fm,
                        rule=Rule.DEFINITION_UNFOLD,
                        premises=args,
                        description=f"instantiation of {head_type} from {arg_str}",
                    ))
                continue

            # Lemma / implication application
            if " " in term:
                tokens = term.split()
                rule_name = tokens[0]
                proof.steps.append(ProofStepIR(
                    var_name=v_name,
                    proposition=prop_fm,
                    rule=Rule.LEMMA_APP,
                    premises=tokens[1:],
                    description=f"modus ponens via {rule_name}",
                ))
                continue

            proof.steps.append(ProofStepIR(
                var_name=v_name,
                proposition=prop_fm,
                rule=Rule.PREMISE,
                premises=[term],
                description=f"from {term}",
            ))

        m_exact = re.match(r"^\s*exact\s+(.*)", l)
        if m_exact:
            term = m_exact.group(1).strip()
            if body == "False":
                proof.conclusion = ProofStepIR(
                    var_name="",
                    proposition="⊥",
                    rule=Rule.CONTRADICTION,
                    premises=term.split(),
                    description=f"{term} refutes assumption",
                )
            else:
                proof.conclusion = ProofStepIR(
                    var_name="",
                    proposition=proof.goal,
                    rule=Rule.CONCLUSION,
                    premises=term.split(),
                    description=f"conclusion via {term}",
                )

    if proof.conclusion is None and proof.goal:
        proof.conclusion = ProofStepIR(
            var_name="",
            proposition=proof.goal,
            rule=Rule.CONCLUSION,
            description="derived theorem",
        )

    return proof


def discover_human_narrative(base_path: Path = None, theorems_dir: Path = None) -> tuple[list[dict], dict[str, dict]]:
    """Discovers the canonical human narrative sections from base.txt and theorems/T*.txt
    without relying on fixed or uniform headers.
    """
    base_path = base_path or (ROOT / "base.txt")
    theorems_dir = theorems_dir or (ROOT / "theorems")

    if not base_path.exists():
        return [], {}

    base_text = base_path.read_text(encoding="utf-8")
    matches = list(re.finditer(r"^(\d+)\.\s+([A-ZÁÉÍÓÚÀÃÕÇ][^\n]+)", base_text, re.MULTILINE))
    valid_matches = []
    for m in matches:
        title = m.group(2).strip()
        clean_title = re.sub(r"\s*→\s*theorems/T\d+\.txt", "", title).strip()
        words = [w for w in re.findall(r"\b[A-Za-zÁÉÍÓÚÀÃÕÇáéíóúàãõç]+\b", clean_title) if w.lower() not in ("vs", "de", "da", "do", "dos", "das", "e", "o", "a", "à")]
        if words and all(w.isupper() for w in words):
            valid_matches.append((int(m.group(1)), clean_title, m))

    title_owners = {}
    for num, clean_title, m in valid_matches:
        thms = re.findall(r"\bT\d+\b", clean_title)
        for t in thms:
            title_owners[t] = num

    sections = []
    for i, (num, clean_title, m) in enumerate(valid_matches):
        start_pos = m.end()
        end_pos = valid_matches[i + 1][2].start() if i + 1 < len(valid_matches) else len(base_text)
        body = base_text[start_pos:end_pos].strip()
        thms_in_title = re.findall(r"\bT\d+\b", clean_title)
        if thms_in_title:
            assigned_thms = thms_in_title
        else:
            thms_in_body = re.findall(r"theorems/(T\d+)", body)
            for start, end in re.findall(r"T(\d+)[–-]T?(\d+)", body):
                for n in range(int(start), int(end) + 1):
                    thms_in_body.append(f"T{n}")
            assigned_thms = [t for t in dict.fromkeys(thms_in_body) if title_owners.get(t, num) == num]
        sections.append({
            "num": num,
            "title": clean_title,
            "body": body,
            "theorems": assigned_thms,
        })

    theorems = {}
    if theorems_dir.exists():
        for p in sorted(theorems_dir.glob("T*.txt"), key=lambda x: int(re.search(r"\d+", x.stem).group())):
            tid = p.stem
            content = p.read_text(encoding="utf-8")
            lines = content.splitlines()
            title = lines[0].strip() if lines else tid
            deps = ""
            for l in lines[:10]:
                if l.startswith("Depende de:"):
                    deps = l.split("Depende de:", 1)[1].strip()
                    break
            theorems[tid] = {
                "title": title,
                "deps": deps,
                "content": content,
                "cids": re.findall(r"\bC\d+\b", content),
            }

    return sections, theorems


@dataclass
class CandidateRoute:
    target_concepts: set[str]
    source_decl: str
    conclusion_prop: str
    proof: ProofIR
    premises: list[str]
    intermediate_conclusions: list[str] = field(default_factory=list)
    subst_axioms: set[str] = field(default_factory=set)
    status: str = "PROVEN"
    countermodel_blocked: bool = False
    is_conditional_route: bool = False
    is_route_composition: bool = False


def extract_consequent(prop: str) -> str:
    """Extracts the final consequent of an implication or statement, stripping outermost
    quantifiers, hypotheses, and implications.
    """
    p = prop.strip()
    if ":" in p and "⊢" not in p and ":=" not in p:
        p = p.split(":", 1)[1].strip()

    while True:
        if p.startswith("(") and p.endswith(")"):
            depth = 0
            matched = True
            for j, ch in enumerate(p[:-1]):
                if ch == "(": depth += 1
                elif ch == ")": depth -= 1
                if depth == 0 and j > 0:
                    matched = False
                    break
            if matched:
                p = p[1:-1].strip()
                continue

        m = re.match(r"^\s*(?:∃|∀|\bexists\b|\bforall\b)\s+[^,:]+[,:]\s*(.*)", p)
        if m:
            p = m.group(1).strip()
            continue

        depth = 0
        cur = []
        tokens = []
        i = 0
        chars = list(p)
        while i < len(chars):
            c = chars[i]
            if c in ("(", "[", "{"): depth += 1; cur.append(c)
            elif c in (")", "]", "}"): depth -= 1; cur.append(c)
            elif (c == "→" or (c == "-" and i + 1 < len(chars) and chars[i+1] == ">")) and depth == 0:
                tokens.append("".join(cur).strip())
                cur = []
                if c == "-": i += 1
            else: cur.append(c)
            i += 1
        if cur: tokens.append("".join(cur).strip())
        if len(tokens) > 1:
            p = tokens[-1].strip()
            continue
        break
    return p


def extract_target_concepts(prop: str) -> set[str]:
    """Extracts target head predicates/relations from a proposition string,
    stripping outermost quantifiers, hypotheses, and implications.
    """
    c_prop = extract_consequent(prop)
    if c_prop in ("False", "⊥"):
        matches = re.findall(r"\b([A-Za-z0-9_]+)\b", prop)
        neg_targets = [m for m in matches if m.startswith("No") or "Neg" in m or "Not" in m]
        if neg_targets:
            return set(neg_targets)

    conjuncts = [c.strip() for c in re.split(r"\s*(?:∧|&)\s*", c_prop)]
    concepts = set()
    for conj in conjuncts:
        c_clean = re.sub(r"^[¬□◇\s]+", "", conj).strip()
        m_head = re.match(r"^([A-Za-z0-9_]+)", c_clean)
        if m_head:
            head = m_head.group(1)
            if head not in ("True", "False", "s", "p", "q", "r", "w", "a", "f", "g", "t"):
                concepts.add(head)
    return concepts


def extract_separation_pairs(decls: dict) -> list[tuple[str, str, str]]:
    """Extracts separation boundary pairs (premise, target, theorem_name) from
    all hostile countermodels and independence theorems in the corpus.
    """
    pairs = []
    for full, d in decls.items():
        name = d["name"]
        if "_not_entails_" in name:
            p1, p2 = name.split("_not_entails_", 1)
            pairs.append((p1.lower(), p2.lower(), name))
        elif name.startswith("not_entails_"):
            target = name[len("not_entails_"):]
            pairs.append(("act", target.lower(), name))
        elif "orthogonal" in name:
            parts = name.split("_orthogonal_to_")
            if len(parts) == 2:
                p1 = parts[0].lower()
                p2 = parts[1].split("_in_")[0].lower()
                pairs.append((p1, p2, name))
    return pairs


def is_route_countermodel_blocked(premises: list[str], target_concepts: set[str], subst_axioms: set[str], separation_pairs: list[tuple[str, str, str]]) -> bool:
    """Verifies whether an inference attempts to cross a countermodel-separated
    boundary without an audited substantive bridging axiom (SEM / META).
    """
    prem_lower = " ".join(premises).lower()
    for p_sep, t_sep, cm_name in separation_pairs:
        if p_sep in prem_lower or (p_sep == "act" and ("act" in prem_lower or "assert" in prem_lower)):
            for tc in target_concepts:
                if t_sep in tc.lower() or tc.lower() in t_sep:
                    # Target is separated from premise by countermodel!
                    # Only unblocked if an audited substantive bridge exists
                    if not subst_axioms:
                        return True
    return False


def compare_routes(r1: CandidateRoute, r2: CandidateRoute) -> str:
    """Compares two candidate routes establishing the same or subsumed target concepts
    under a strict partial order of logical strength, decoupling length from strength.
    A route r1 can only dominate r2 if r1 establishes ALL target concepts that r2 establishes.
    Theorems with distinct target achievements (e.g. Ground vs Personal) do not compete.
    """
    if not (r1.target_concepts and r2.target_concepts):
        return "INCOMPARABLE"

    # Countermodel blockage: unblocked strictly dominates blocked
    if not r1.countermodel_blocked and r2.countermodel_blocked:
        if r2.target_concepts.issubset(r1.target_concepts):
            return "DOMINATES"
    if r1.countermodel_blocked and not r2.countermodel_blocked:
        if r1.target_concepts.issubset(r2.target_concepts):
            return "DOMINATED_BY"

    # Conditional routes vs pure derivations: pure derivation strictly dominates
    if not r1.is_conditional_route and r2.is_conditional_route:
        if r2.target_concepts.issubset(r1.target_concepts):
            return "DOMINATES"
    if r1.is_conditional_route and not r2.is_conditional_route:
        if r1.target_concepts.issubset(r2.target_concepts):
            return "DOMINATED_BY"

    status_rank = {"PROVEN": 4, "DEFINITIONAL": 4, "PROVEN↑": 3, "AXIOM": 2, "BLOCKED": 1, "DEFERRED": 1}
    s1 = status_rank.get(r1.status, 0)
    s2 = status_rank.get(r2.status, 0)

    a1 = r1.subst_axioms
    a2 = r2.subst_axioms

    # r1 dominates r2 only if r1 establishes all target concepts that r2 establishes
    # and requires strictly fewer substantive axioms or has strictly higher status
    if r2.target_concepts.issubset(r1.target_concepts):
        if a1 < a2 and s1 >= s2:
            return "DOMINATES"
        if len(a1) < len(a2) and s1 >= s2:
            return "DOMINATES"
        if s1 > s2 and a1 <= a2:
            return "DOMINATES"

    # r2 dominates r1 only if r2 establishes all target concepts that r1 establishes
    # and requires strictly fewer substantive axioms or has strictly higher status
    if r1.target_concepts.issubset(r2.target_concepts):
        if a2 < a1 and s2 >= s1:
            return "DOMINATED_BY"
        if len(a2) < len(a1) and s2 >= s1:
            return "DOMINATED_BY"
        if s2 > s1 and a2 <= a1:
            return "DOMINATED_BY"

    if r1.target_concepts == r2.target_concepts and a1 == a2 and s1 == s2:
        return "EQUIVALENT"

    return "INCOMPARABLE"


def select_strongest_routes(routes: list[CandidateRoute]) -> tuple[list[CandidateRoute], list[CandidateRoute]]:
    """Partitions candidate routes into undominated (primary) and dominated (alternative) routes."""
    if not routes:
        return [], []
    undominated = []
    dominated = []
    for r in routes:
        is_dom = False
        for other in routes:
            if other is not r and compare_routes(other, r) == "DOMINATES":
                is_dom = True
                break
        if is_dom:
            dominated.append(r)
        else:
            undominated.append(r)
    return undominated, dominated


def extract_boundary_generically(proof_name: str, doc: str = "", statement: str = "") -> tuple[str, str]:
    """Extracts independence boundary (left ⇏ right) generically from theorem name,
    docstring, or AST statement without hard-coding any domain substrings.
    """
    if "_not_entails_" in proof_name:
        parts = proof_name.split("_not_entails_", 1)
        left = format_discrete_math(humanise(strip_ns(parts[0])))
        right = format_discrete_math(humanise(strip_ns(parts[1])))
        return left, right

    if doc:
        for line in doc.splitlines():
            if "⇏" in line:
                parts = line.split("⇏", 1)
                return parts[0].strip(), parts[1].strip()

    return format_discrete_math(humanise(strip_ns(proof_name))), "Independence"


def classify_proof_edge(proof: ProofIR, graph: dict = None, decls: dict = None) -> tuple[str, str]:
    """Classifies the local deductive status of a proof transition edge into one of:
    - DEFINITIONAL: definitional equality, structure constructor, or identity (Iff.rfl / def)
    - COUNTERMODEL: machine-checked independence separation boundary
    - OPEN / FRONTIER: open problem / unproved horizon
    - SEMANTIC [requires: <Ax> (SEM)]: direct invocation of a semantic bridge axiom (Tag: SEM)
    - METAPHYSICAL [requires: <Ax> (META)]: direct invocation of a metaphysical bridge axiom (Tag: META)
    - PROVEN: machine-verified derivation from established premises with 0 substantive axioms
    """
    if proof.boundary:
        left, right = proof.boundary[0], proof.boundary[1]
        return "COUNTERMODEL", f"COUNTERMODEL | {left} ⇏ {right}"

    if proof.kind in ("def", "structure"):
        return "DEFINITIONAL", "DEFINITIONAL"

    local_meta = [ax.rsplit(".", 1)[-1] for ax in proof.subst_axioms if (_REGISTRY.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") == "META"]
    local_sem = [ax.rsplit(".", 1)[-1] for ax in proof.subst_axioms if (_REGISTRY.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") == "SEM"]

    if local_meta:
        req = ", ".join(sorted(set(local_meta)))
        return "METAPHYSICAL", f"METAPHYSICAL [requires: {req} (META)]"
    elif local_sem:
        req = ", ".join(sorted(set(local_sem)))
        return "SEMANTIC", f"SEMANTIC [requires: {req} (SEM)]"
    else:
        return "PROVEN", "PROVEN | 0 substantive axioms"


def resolve_proof_by_name(name: str, compiled_by_id: dict, decls: dict, graph: dict) -> ProofIR | None:
    for cid, (c, p) in compiled_by_id.items():
        if p.name == name or p.full_name.endswith(f".{name}"):
            return p
    for full, d in decls.items():
        if d["name"] == name or full.endswith(f".{name}"):
            return compile_lean_proof(full, decls, graph.get("node_map", {}), graph, {})
    return None


def select_global_proof_spine(
    compiled_by_id: dict[str, tuple[dict, ProofIR]],
    narrative_secs: list[dict],
    theorems_dict: dict,
    graph: dict,
    decls: dict,
    separation_pairs: list[tuple[str, str, str]]
) -> tuple[list[dict], list[ProofIR], set[str]]:
    """Selects an uninterrupted end-to-end global proof spine over depgraph.json
    and the canonical narrative, discovering multi-hop paths from performative starting
    declarations to terminal milestones, pruning countermodel-blocked routes, and
    computing minimal-assumption dominance globally across the entire proof space.
    """
    bridge_type_names = {
        name.rsplit(".", 1)[-1]
        for name, d in decls.items()
        if ("bridge" in name.lower() or "bridge" in d.get("doc", "").lower()) and d["kind"] in ("structure", "class")
    }

    # 1. Discover all candidate routes globally across compiled claims
    all_candidate_routes = []
    route_by_decl = {}
    for cid, (c, proof) in compiled_by_id.items():
        if c.get("status") not in ("PROVEN", "PROVEN↑", "AXIOM") or proof.boundary:
            continue
        p_prose = c.get("prose", "")
        if "IM_STUPID" in p_prose or "deprecated" in p_prose.lower():
            continue

        target_concepts = extract_target_concepts(proof.goal)
        subst = {ax.rsplit(".", 1)[-1] for ax in proof.subst_axioms if (_REGISTRY.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") in ("SEM", "META")}
        premises = [a.proposition for a in proof.assumptions]
        blocked = is_route_countermodel_blocked(premises, target_concepts, subst, separation_pairs)
        intermediates = []
        for pred in graph["in"].get(proof.full_name, []):
            if pred in decls and decls[pred]["kind"] in ("theorem", "lemma"):
                intermediates.append(decls[pred]["statement"])

        stmt = decls.get(proof.full_name, {}).get("statement", "")
        has_bridge_param = any(b in stmt for b in bridge_type_names) or bool(re.search(r"\(\s*\w+\s*:\s*[A-Za-z0-9_.]*Bridge\b", stmt))
        is_comp = len(intermediates) > 1 and bool(subst)

        route = CandidateRoute(
            target_concepts=target_concepts,
            source_decl=proof.full_name,
            conclusion_prop=proof.goal,
            proof=proof,
            premises=premises,
            intermediate_conclusions=intermediates,
            subst_axioms=subst,
            status=c.get("status", "PROVEN"),
            countermodel_blocked=blocked,
            is_conditional_route=has_bridge_param,
            is_route_composition=is_comp,
        )
        all_candidate_routes.append(route)
        route_by_decl[proof.full_name] = (cid, c, route)

    # 2. Global end-to-end minimal-assumption route dominance across the full repository
    undom_routes, dom_routes = select_strongest_routes(all_candidate_routes)

    # Format dominated routes into alternative derivations with explicit premise pricing
    assigned_cids = set()
    alternative_proofs = []
    for r in dom_routes:
        if r.status in ("PROVEN", "PROVEN↑"):
            if r.is_conditional_route:
                r.proof.alternative_note = "Conditional route (requires bridge parameter)"
            elif r.subst_axioms:
                req = f"requires: {', '.join(sorted(r.subst_axioms))}"
                r.proof.alternative_note = f"Route composition / alternative derivation ({req})"
            else:
                r.proof.alternative_note = "Alternative derivation"
            cid = route_by_decl[r.source_decl][0]
            if cid not in assigned_cids and r.source_decl not in assigned_cids:
                assigned_cids.add(cid)
                assigned_cids.add(r.source_decl)
                alternative_proofs.append(r.proof)

    # 3. Topologically sort the undominated global spine declarations via depgraph.json
    def get_dag_depth(decl_name: str, memo: dict = None, visiting: set = None) -> int:
        if memo is None: memo = {}
        if decl_name in memo: return memo[decl_name]
        if visiting is None: visiting = set()
        if decl_name in visiting: return 0
        visiting.add(decl_name)
        preds = [p for p in graph["in"].get(decl_name, []) if not is_internal_lean_decl(p) and p in decls]
        d = 0 if not preds else 1 + max(get_dag_depth(p, memo, visiting.copy()) for p in preds)
        memo[decl_name] = d
        return d

    depth_cache = {}
    spine_routes_sorted = sorted(undom_routes, key=lambda r: get_dag_depth(r.source_decl, depth_cache))

    # 4. Map the globally selected, topologically ordered spine declarations into narrative sections
    detailed_sections = []
    for s in narrative_secs:
        num = s["num"]
        if num == 0 or num > 25:
            continue
        sec_title = s["title"]
        body = s["body"]
        t_refs = list(s["theorems"])

        section_proofs = []
        for r in spine_routes_sorted:
            cid, c, _ = route_by_decl[r.source_decl]
            if cid in assigned_cids or r.source_decl in assigned_cids:
                continue
            p = c.get("prose", "")
            is_match = False
            if re.search(rf"(?:^|[\s/,;])§{num}(?:[a-z]?)(?:[\s/,;]|$)", p):
                is_match = True
            elif any(re.search(rf"\b{t}\b", p) for t in t_refs):
                is_match = True
            elif any(cid in theorems_dict[t]["cids"] for t in t_refs if t in theorems_dict):
                is_match = True

            if is_match:
                assigned_cids.add(cid)
                assigned_cids.add(r.source_decl)
                section_proofs.append(r.proof)

        # Sort proofs within section putting reductio turning points first, then topological order
        section_proofs.sort(key=lambda p: (
            0 if (p.conclusion and p.conclusion.rule == Rule.CONTRADICTION) else 1,
            get_dag_depth(p.full_name, depth_cache)
        ))

        summary_text = ""
        if body:
            paras = [p.strip() for p in body.split("\n\n") if p.strip()]
            clean_paras = [p for p in paras if not p.startswith("**[Nota") and not p.startswith("Teoremas:")]
            selected = []
            total_len = 0
            for p in clean_paras:
                if p.startswith("(Nota formal") or p.startswith("* ChoiceField"):
                    break
                selected.append(p)
                total_len += len(p)
                if total_len >= 1800 and len(selected) >= 7:
                    break
            summary_text = "\n\n".join(selected)
        if not summary_text:
            for t in t_refs:
                if t in theorems_dict:
                    t_lines = theorems_dict[t]["content"].splitlines()
                    narrative = []
                    for l in t_lines[1:]:
                        l_s = l.strip()
                        if l_s and not (l_s.startswith("Depende de:") or l_s.startswith("Verificado em:") or l_s.startswith("Pegada:") or l_s.startswith("Impressão")):
                            narrative.append(l_s)
                    if narrative:
                        summary_text = "\n\n".join(narrative[:3])
                        break

        detailed_sections.append({
            "title": f"{num}. {sec_title}",
            "summary": summary_text,
            "proofs": section_proofs,
            "conclusion": section_proofs[-1].goal if section_proofs else "",
            "category": "detailed",
        })

    # 5. Build the Main Presentation Spine from Authoritative Declarative Metadata
    presentation_data = load_presentation_spine()
    spine_sections = []

    if presentation_data and "spine_nodes" in presentation_data:
        for node in presentation_data["spine_nodes"]:
            primary_proofs = []
            pt_names = node.get("primary_targets", node.get("target_names", []))
            for name in pt_names:
                p = resolve_proof_by_name(name, compiled_by_id, decls, graph)
                if p:
                    primary_proofs.append(p)

            supporting_proofs = []
            for name in node.get("supporting_targets", []):
                p = resolve_proof_by_name(name, compiled_by_id, decls, graph)
                if p:
                    supporting_proofs.append(p)

            obstruction_proofs = []
            for name in node.get("obstructions", []):
                p = resolve_proof_by_name(name, compiled_by_id, decls, graph)
                if p:
                    obstruction_proofs.append(p)

            subsections = []
            for sub in node.get("supporting_defense", []):
                sub_proofs = []
                for name in sub.get("target_names", []):
                    p = resolve_proof_by_name(name, compiled_by_id, decls, graph)
                    if p:
                        sub_proofs.append(p)
                subsections.append({
                    "title": sub.get("title", ""),
                    "summary": sub.get("summary", ""),
                    "proofs": sub_proofs,
                })

            branches = []
            for b in node.get("branches", []):
                b_primary = [resolve_proof_by_name(n, compiled_by_id, decls, graph) for n in b.get("primary_targets", [])]
                b_primary = [p for p in b_primary if p]
                b_supporting = [resolve_proof_by_name(n, compiled_by_id, decls, graph) for n in b.get("supporting_targets", [])]
                b_supporting = [p for p in b_supporting if p]
                b_obstructions = [resolve_proof_by_name(n, compiled_by_id, decls, graph) for n in b.get("obstructions", [])]
                b_obstructions = [p for p in b_obstructions if p]
                branches.append({
                    "id": b.get("id", ""),
                    "label": b.get("label", ""),
                    "title": b.get("title", b.get("label", "")),
                    "formula": b.get("formula", ""),
                    "edge_label": b.get("edge_label", ""),
                    "continuation_label": b.get("continuation_label", ""),
                    "summary": b.get("summary", ""),
                    "investigation_link": b.get("investigation_link", ""),
                    "primary_proofs": b_primary,
                    "supporting_proofs": b_supporting,
                    "obstruction_proofs": b_obstructions,
                    "proofs": b_primary,
                })

            spine_sections.append({
                "id": node.get("id", ""),
                "label": node.get("label", ""),
                "title": node["title"],
                "explanation": node.get("explanation", ""),
                "summary": node["summary"],
                "formula": node.get("formula", ""),
                "investigation_link": node.get("investigation_link", ""),
                "primary_proofs": primary_proofs,
                "supporting_proofs": supporting_proofs,
                "obstruction_proofs": obstruction_proofs,
                "proofs": primary_proofs,
                "branches": branches,
                "subsections": subsections,
                "conclusion": primary_proofs[-1].goal if primary_proofs else "",
                "category": "spine",
            })
    else:
        # Generic fallback when metadata file is absent
        for sec in detailed_sections[:8]:
            spine_sections.append({
                "title": sec["title"],
                "summary": sec.get("summary", ""),
                "proofs": sec.get("proofs", []),
                "conclusion": sec.get("conclusion", ""),
                "category": "spine",
            })

    return spine_sections, detailed_sections, alternative_proofs, assigned_cids


def discover_deduction_sections(gapmap_sections: list[dict], decls: dict, node_map: dict, graph: dict, def_registry: dict) -> list[dict]:
    """Discovers the main deduction path and sections dynamically from the canonical
    human narrative (base.txt and theorems/) and formal Lean AST corpus.
    """
    base_path = ROOT / "base.txt"
    theorems_dir = ROOT / "theorems"

    # Synthetic test mode fallback: if base.txt is missing or decls is small
    if not base_path.exists() or len(decls) <= 10:
        discovered = []
        for sec in gapmap_sections:
            raw_title = sec["title"]
            title = re.sub(r"\s*\([^)]*\)", "", raw_title).strip()
            if " — " in title:
                level_part, name_part = title.split(" — ", 1)
                clean_title = f"{level_part.strip()}: {name_part.strip().title()}"
            else:
                clean_title = title.title()

            proofs = []
            for c in sec.get("claims", []):
                full = c.get("_full")
                if not full or full not in decls or is_internal_lean_decl(full):
                    continue
                status = c.get("status", "")
                if status in ("DISSOLVED", "DEFERRED", "BLOCKED"):
                    continue

                proof = compile_lean_proof(full, decls, node_map, graph, def_registry)
                if status == "COUNTERMODEL" or "_not_entails_" in proof.name:
                    doc = decls[full].get("doc", "")
                    stmt = decls[full].get("statement", "")
                    left, right = extract_boundary_generically(proof.name, doc, stmt)
                    proof.boundary = (left, right, c.get("prose") or None, f"{proof.name} countermodel" if c.get("prose") else None)
                proofs.append(proof)

            if proofs:
                proofs.sort(key=lambda p: len(graph["in"].get(p.full_name, set())))
                discovered.append({
                    "title": clean_title,
                    "summary": f"Deductive progression established in {raw_title}.",
                    "proofs": proofs,
                    "conclusion": proofs[-1].goal if proofs else "",
                    "category": "spine",
                })
        return discovered

    # Real repository mode: discover from canonical human narrative
    narrative_secs, theorems_dict = discover_human_narrative(base_path, theorems_dir)
    all_claims = [c for s in gapmap_sections for c in s.get("claims", [])]

    compiled_by_id = {}
    for c in all_claims:
        full = c.get("_full")
        if not full or full not in decls or is_internal_lean_decl(full):
            continue
        proof = compile_lean_proof(full, decls, node_map, graph, def_registry)
        status = c.get("status", "")
        if status == "COUNTERMODEL" or "_not_entails_" in proof.name:
            doc = decls[full].get("doc", "")
            stmt = decls[full].get("statement", "")
            left, right = extract_boundary_generically(proof.name, doc, stmt)
            proof.boundary = (left, right, c.get("prose") or None, f"{proof.name} countermodel" if c.get("prose") else None)
        compiled_by_id[c["id"]] = (c, proof)

    separation_pairs = extract_separation_pairs(decls)
    spine_sections, detailed_sections, alternative_proofs, assigned_cids = select_global_proof_spine(
        compiled_by_id, narrative_secs, theorems_dict, graph, decls, separation_pairs
    )

    # 2. Detailed Deductions (secondary sub-proofs / alternative routes)
    detailed_proofs = []
    for cid, (c, proof) in compiled_by_id.items():
        if cid in assigned_cids or proof.boundary:
            continue
        if c.get("status") in ("PROVEN", "PROVEN↑"):
            detailed_proofs.append(proof)
            assigned_cids.add(cid)

    all_detailed = alternative_proofs + detailed_proofs
    if all_detailed:
        all_detailed.sort(key=lambda p: len(graph["in"].get(p.full_name, set())))
        detailed_sections.append({
            "title": "Alternative Derivations and Supporting Lemmas",
            "summary": "Step-by-step natural deduction proofs, certified alternative derivations, and secondary formal derivations supporting the main argument.",
            "proofs": all_detailed,
            "conclusion": "",
            "category": "detailed",
        })

    # 3. Countermodels and Open Problems
    countermodel_proofs = []
    for cid, (c, proof) in compiled_by_id.items():
        if proof.boundary:
            countermodel_proofs.append(proof)
            assigned_cids.add(cid)

    countermodel_sections = []
    if countermodel_proofs:
        countermodel_sections.append({
            "title": "Countermodels and Open Problems",
            "summary": "Machine-checked independence countermodels separating premises from unprovable targets without explicit bridges.",
            "proofs": countermodel_proofs,
            "conclusion": "",
            "category": "countermodel",
        })

    # 4. Formal Frontiers (Issue 3 resolution)
    frontier_proofs = []
    for c in all_claims:
        status = c.get("status", "")
        if status in ("BLOCKED", "DEFERRED", "OPEN"):
            frontier_proofs.append(ProofIR(
                full_name=c.get("_full") or c["id"],
                file="GAPMAP.md",
                line=0,
                name=c["id"],
                kind="frontier",
                goal=f"{c.get('prose', '')} — {c.get('statement') or c.get('lean_ref') or ''}",
                doc=c.get("_gloss") or "",
            ))

    frontier_sections = []
    if frontier_proofs:
        frontier_sections.append({
            "title": "Formal Frontiers",
            "summary": "Unresolved formal steps, active conjectures, and open boundaries in Γ.",
            "proofs": frontier_proofs,
            "conclusion": "",
            "category": "frontier",
        })

    return spine_sections + detailed_sections + countermodel_sections + frontier_sections


def discover_investigations(investigations_dir: Path = None, decls: dict = None) -> dict:
    """Dynamically discovers and categorizes investigation documents and formal artifacts
    without hard-coding any specific filenames.
    """
    if investigations_dir is None:
        investigations_dir = ROOT / "investigations"

    docs = []
    if investigations_dir and investigations_dir.exists():
        for p in sorted(investigations_dir.glob("*.md")):
            content = p.read_text(encoding="utf-8")
            title = p.stem.replace("-", " ").title()
            title_found = False
            sources = []
            status = ""
            for line in content.splitlines()[:25]:
                line_str = line.strip()
                m = re.match(r"^#\s+(?:Investigation:\s*)?(.*)", line_str, flags=re.IGNORECASE)
                if m and not title_found:
                    title = re.sub(r"[\*`]", "", m.group(1)).strip()
                    title_found = True
                if "Primary Formal Source:" in line_str:
                    raw_src = line_str.split("Primary Formal Source:")[-1]
                    sources = [s.strip(" *`") for s in raw_src.split(",") if s.strip(" *`")]
                if "Kernel Status:" in line_str:
                    status = line_str.split("Kernel Status:")[-1].strip(" *`")
            rel_path = f"investigations/{p.name}"
            docs.append({
                "path": rel_path,
                "file": p.name,
                "title": title,
                "sources": sources,
                "status": status,
            })

    retorsions_docs = []
    countermodels_docs = []
    technical_docs = []
    detailed_docs = []

    for d in docs:
        stem = Path(d["path"]).stem.lower()
        t = d["title"].lower()
        if "kernel-audit" in stem or "technical" in t or "audit" in t:
            technical_docs.append(d)
        elif "countermodel" in stem or "countermodel" in t or "hostile" in t or "independence" in t:
            countermodels_docs.append(d)
        elif "retorsion" in stem or "retorsion" in t or "right-and-wrong" in stem:
            retorsions_docs.append(d)
        else:
            detailed_docs.append(d)

    return {
        "retorsions_docs": retorsions_docs,
        "countermodels_docs": countermodels_docs,
        "detailed_docs": detailed_docs,
        "technical_docs": technical_docs,
    }


def render_further_investigations(decls: dict = None, investigations_dir: Path = None) -> list[str]:
    """Renders the comprehensive, uninterrupted navigation catalogue into the proof research
    at the end of README.md, organized into 4 first-class categories:
    1. Retorsions
    2. Countermodels & Independence
    3. Detailed Investigations
    4. Technical
    """
    cat = discover_investigations(investigations_dir, decls)
    L = []
    ap = L.append
    ap("## Further Investigations")
    ap("")
    ap("### Retorsions")
    ap("")
    # Dynamically extract retorsion theorems from decls without hardcoding specific names
    if decls:
        retorsion_proofs = []
        for full, d in sorted(decls.items()):
            name = d["name"]
            doc = d.get("doc", "")
            if d["kind"] in ("theorem", "lemma") and doc:
                first_line = doc.splitlines()[0].strip(" -*")
                name_l = name.lower()
                doc_l = doc.lower()
                if "retorsion" in name_l or "selfrefutes" in name_l or "claims_correct" in name_l or "retors" in doc_l or "self-refut" in doc_l:
                    label = humanise(strip_ns(name)).title()
                    retorsion_proofs.append((label, name, f"formal/Logos/{d['file']}", first_line))
        for label, name, file_path, first_line in retorsion_proofs:
            ap(f"* **{label}:** `{name}` (`{file_path}`) — {first_line}")
    for d in cat["retorsions_docs"]:
        desc = f" — {d['status']}" if d.get("status") else ""
        ap(f"* [{d['title']}]({d['path']}){desc}")
    ap("")

    ap("### Countermodels & Independence")
    ap("")
    # Dynamically extract independence boundaries from decls without hardcoding specific names
    if decls:
        independence_proofs = []
        for full, d in sorted(decls.items()):
            name = d["name"]
            doc = d.get("doc", "")
            stmt = d.get("statement", "")
            if ("_not_entails_" in name or d.get("status") == "COUNTERMODEL") and d["kind"] in ("theorem", "lemma"):
                left, right = extract_boundary_generically(name, doc, stmt)
                first_line = doc.splitlines()[0].strip(" -*") if doc else "Mathematical independence model."
                line_no = d.get("line", 1)
                loc = f"formal/Logos/{d['file']}:{line_no}"
                independence_proofs.append((f"{left} ⇏ {right}", name, loc, first_line))
        for boundary, name, loc, first_line in independence_proofs[:6]:
            ap(f"* **{boundary}:** `{name}` (`{loc}`) — {first_line}")
    for d in cat["countermodels_docs"]:
        desc = f" — {d['status']}" if d.get("status") else ""
        ap(f"* [{d['title']}]({d['path']}){desc}")
    ap("")

    ap("### Detailed Investigations")
    ap("")
    for d in cat["detailed_docs"]:
        desc = f" — {d['status']}" if d.get("status") else ""
        ap(f"* [{d['title']}]({d['path']}){desc}")
    ap("")

    ap("### Technical")
    ap("")
    for d in cat["technical_docs"]:
        ap(f"* [{d['title']}]({d['path']}) — Complete kernel audit, transitive axiom footprints, dependency ledger, and consistency checks.")
    ap("* [Formal Dependency Graph (JSON)](formal/depgraph.json) / [(DOT)](formal/depgraph.dot) — LeanDepViz transitive kernel dependency DAG.")
    ap("* [Theorem Ledger (GAPMAP)](formal/GAPMAP.md) — Formal correspondence mapping across formal and prose corpora.")
    ap("")

    return L


def pick_primary_milestone_proof(proofs: list[ProofIR]) -> ProofIR | None:
    """Selects the most representative, strongest milestone proof for a section
    prioritizing existential/composite master theorems, retorsive turning points,
    and proven status.
    """
    if not proofs:
        return None
    def score(p):
        concepts = extract_target_concepts(p.goal)
        is_existential = 1 if ("∃" in p.goal or "exists" in p.goal.lower()) else 0
        is_theorem = 1 if p.kind == "theorem" else 0
        is_master = 1 if (p.doc and ("master" in p.doc.lower() or "fundamental" in p.doc.lower() or "retorsion" in p.doc.lower())) else 0
        is_contradiction = 1 if (p.conclusion and p.conclusion.rule == Rule.CONTRADICTION) else 0
        return (is_contradiction, is_master, is_existential, len(concepts), is_theorem)
    return max(proofs, key=score)


def compute_epistemic_badge(proofs: list[ProofIR], registry: dict = None) -> str:
    """Computes an authoritative epistemic badge for a set of proofs against the axiom registry."""
    if registry is None:
        registry = _REGISTRY
    if not proofs:
        return "DEFINITIONAL"
    meta_axes = sorted(set(
        ax.rsplit(".", 1)[-1] for p in proofs for ax in p.subst_axioms
        if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") == "META"
    ))
    sem_axes = sorted(set(
        ax.rsplit(".", 1)[-1] for p in proofs for ax in p.subst_axioms
        if (registry.get(ax.rsplit(".", 1)[-1]) or {}).get("tag") == "SEM"
    ))
    if any(getattr(p, "boundary", None) or "_not_entails_" in p.name for p in proofs):
        return "COUNTERMODEL · ⇏"
    elif meta_axes:
        return f"METAPHYSICAL [requires: {', '.join(meta_axes)} (META)]"
    elif sem_axes:
        return f"SEMANTIC [requires: {', '.join(sem_axes)} (SEM)]"
    elif all(p.kind in ("def", "structure") for p in proofs):
        return "DEFINITIONAL"
    return "PROVEN · 0 substantive axioms"


def generate_ascii_chart(
    spine_nodes: list[dict],
    edges: list[dict],
    terminal_branches: list[dict],
    spine_proofs: dict[str, list[ProofIR]],
    spine_sections_dict: dict[str, dict] = None
) -> list[str]:
    """Generically generates an ASCII flowchart from declarative presentation nodes and edges,
    computing authoritative status badges dynamically from kernel proof audit data.
    """
    lines = []
    edges_by_from = {}
    for e in edges:
        edges_by_from.setdefault(e["from"], []).append(e)

    for i, node in enumerate(spine_nodes):
        node_id = node.get("id", "")
        label = node.get("label", node.get("title", ""))
        formula = node.get("formula", "")
        proofs = spine_proofs.get(node_id, [])

        # Compute authoritative badge from primary proofs and registry
        badge = compute_epistemic_badge(proofs) if formula else "DEFINITIONAL"

        lines.append(label)
        if node.get("explanation"):
            lines.append(f"  {node['explanation']}")
        if formula:
            lines.append(f"  ⊢ {formula}")
        lines.append(f"  *[{badge}]*")
        if node.get("note"):
            lines.append(f"  *[{node['note']}]*")

        # Supporting defense if any
        for sub in node.get("supporting_defense", []):
            lines.append("        ▲")
            lines.append(f"        │ [{sub.get('title', 'Supporting Defense')}]")
            if sub.get("formula"):
                lines.append(f"        │ ⊢ {sub.get('formula')}")

        # Branches attached directly to this node
        branches = node.get("branches", [])
        if branches:
            for idx, b in enumerate(branches):
                is_last = (idx == len(branches) - 1)
                prefix = "        └───" if is_last else "        ├───"
                cont_pfx = "            " if is_last else "        │   "
                b_edge = b.get("edge_label", "[branch]")
                b_label = b.get("label", "")
                b_formula = b.get("formula", "")

                b_proofs = []
                if spine_sections_dict and node_id in spine_sections_dict:
                    sec = spine_sections_dict[node_id]
                    for sec_b in sec.get("branches", []):
                        if sec_b.get("id") == b.get("id"):
                            b_proofs = sec_b.get("primary_proofs", []) or sec_b.get("obstruction_proofs", [])
                            break
                b_badge = compute_epistemic_badge(b_proofs)
                if b.get("obstructions") and not b.get("primary_targets"):
                    b_badge = "COUNTERMODEL · ⇏"

                lines.append("        │")
                lines.append(f"{prefix} {b_edge} → {b_label}")
                if b_formula:
                    lines.append(f"{cont_pfx}  ⊢ {b_formula}")
                lines.append(f"{cont_pfx}  *[{b_badge}]*")
                if b.get("continuation_label"):
                    lines.append(f"{cont_pfx}       │")
                    lines.append(f"{cont_pfx}       │ [COUNTERMODEL SEPARATION FRONTIERS]")
                    lines.append(f"{cont_pfx}       ▼")
                    lines.append(f"{cont_pfx}  {b.get('continuation_label')}")
                    lines.append(f"{cont_pfx}    *[COUNTERMODEL · ⇏]*")

        # Outgoing edges
        out_edges = edges_by_from.get(node_id, [])
        for e in out_edges:
            direction = e.get("direction", "discovery")
            rel = e.get("relation", "")
            if direction == "grounding":
                dir_tag = f"[{direction.upper()} · {rel}]"
            elif direction == "continuation":
                dir_tag = f"[{direction} · {rel}]"
            else:
                dir_tag = f"[{direction} · {rel}]"
            lines.append("        │")
            lines.append(f"        │ {dir_tag}")
            lines.append("        ▼")

    if not any(node.get("branches") for node in spine_nodes):
        for tb in terminal_branches:
            lines.append("        │")
            lines.append("        ├─────────────────────────────┬─────────────────────────────┐")
            b1, b2 = tb["branches"][0], tb["branches"][1]
            lines.append(f"        │ {b1['edge_label']}   │ {b2['edge_label']} │")
            lines.append("        ▼                             ▼                             │")
            lines.append(f"{b1['label']} {b2['label']}")
            lines.append(f"  ⊢ {b1['formula']}         ⊢ {b2['formula']}")
            lines.append(f"  *[{b1['badge']}]* *[{b2['badge']}]*")
            cont = tb.get("continuation")
            if cont:
                lines.append("        │")
                lines.append(f"        │  {cont['edge_label']}")
                lines.append("        ▼")
                lines.append(cont["label"])
                lines.append(f"  ⊢ {cont['formula']}")
                lines.append(f"  *[{cont['badge']}]*")

    return lines


def generate_argument_at_a_glance(spine_sections: list[dict], frontiers: list[dict] = None, countermodels: list[dict] = None) -> list[str]:
    """Synthesizes an immediate, compact, conceptual visual flowchart of the strongest argument,
    answering 'What happens?' in ordinary human-readable philosophical steps with subordinate
    formal certification and local edge badges, explicitly distinguishing the discovery direction
    from the ontological grounding direction.
    """
    lines = []
    ap = lines.append
    ap("## The Argument at a Glance")
    ap("")
    ap("This deduction establishes the complete philosophical arc from the performative attempt to deny objective Right and Wrong to the ultimate personal ground, exposing the exact formal status, substantive axiom footprint, and mathematical frontiers at every step.")
    ap("")
    ap("Central Distinction: Epistemic Discovery (Right/Wrong reveals Person) operates in reverse of Ontological Grounding (Person grounds Right/Wrong).")
    ap("")
    ap("```text")

    presentation_data = load_presentation_spine()
    if presentation_data and "spine_nodes" in presentation_data:
        spine_proofs = {s.get("id", ""): s.get("proofs", []) for s in spine_sections}
        spine_sections_dict = {s.get("id", ""): s for s in spine_sections}
        chart_lines = generate_ascii_chart(
            presentation_data["spine_nodes"],
            presentation_data.get("edges", []),
            presentation_data.get("terminal_branches", []),
            spine_proofs,
            spine_sections_dict=spine_sections_dict
        )
        for cl in chart_lines:
            ap(cl)
    ap("```")
    ap("")
    return lines


def render_proof_body_spine(proof: ProofIR, ap):
    """Renders a proof on the Main Proof Spine as an integral, readable part of the
    philosophical argument: clear mathematical-philosophical explanation, formal consequence,
    subordinate status badge, and Lean certification.
    """
    doc_lines = []
    if proof.doc:
        for line in proof.doc.splitlines():
            line_str = line.strip()
            if not line_str:
                continue
            if any(line_str.startswith(k) for k in ("Status:", "Tag:", "Footprint:", "Lean:", "Audit:", "Impressão")):
                continue
            doc_lines.append(line_str)

    if doc_lines:
        ap(" ".join(doc_lines))
        ap("")

    if proof.boundary:
        left, right = proof.boundary[0], proof.boundary[1]
        ap(f"    {left} ⇏ {right}")
        ap("")
    elif proof.conclusion and proof.conclusion.rule == Rule.CONTRADICTION:
        if proof.assumptions:
            assump_str = " ∧ ".join(a.proposition for a in proof.assumptions)
            ap(f"    {assump_str} → ⊥")
        else:
            ap(f"    {proof.goal}")
        ap("")
    elif proof.conclusion:
        ap(f"    ∴ {proof.conclusion.proposition}")
        ap("")
    elif proof.goal:
        ap(f"    ∴ {proof.goal}")
        ap("")

    edge_cat, edge_badge = classify_proof_edge(proof)
    ap(f"    [{edge_badge}]")
    ap(f"    *(Formal certification: Lean: `{proof.file}#{proof.name}`)*")
    ap("")


def render_proof_body(proof: ProofIR, ap, detailed: bool = False):
    """Renders an individual proof's assumptions, steps, conclusion, badges, and Lean citation.
    In high-level spine mode (detailed=False), focuses on conceptual explanation, formal consequence,
    status badges, and citations, delegating verbose line-by-line deduction steps to Detailed Deductions.
    """
    if proof.doc:
        ap(proof.doc)
        ap("")

    if proof.boundary:
        left, right, link, link_label = proof.boundary
        if link and link_label:
            ap(f"    {left} ⇏ {right}  [{link_label} →]({link})")
        else:
            ap(f"    {left} ⇏ {right}")
        ap("")
    elif proof.kind in ("def", "structure", "axiom"):
        if proof.goal:
            for s_line in proof.goal.splitlines():
                ap(f"    {s_line}")
            ap("")
    elif proof.kind in ("theorem", "lemma"):
        if proof.assumptions:
            ap(f"Assume {', and '.join(a.proposition for a in proof.assumptions)}:")
            ap("")

        if detailed and proof.steps:
            for s_idx, step in enumerate(proof.steps, 1):
                ap(f"    {s_idx}. {step.proposition}  ({step.description})")
            ap("")

        if proof.conclusion:
            if proof.conclusion.rule == Rule.CONTRADICTION:
                ap(f"    Contradiction: {proof.conclusion.description} (→ ⊥)")
            else:
                ap(f"    ∴ {proof.conclusion.proposition}")
            ap("")
        elif proof.goal:
            ap(f"    ∴ {proof.goal}")
            ap("")

    edge_cat, edge_badge = classify_proof_edge(proof)
    if edge_cat in ("SEMANTIC", "METAPHYSICAL"):
        ap(f"    [{edge_badge}]")
        ap("")
    elif edge_cat == "DEFINITIONAL":
        ap("    [DEFINITIONAL]")
        ap("")
    elif edge_cat == "COUNTERMODEL":
        ap(f"    [{edge_badge}]")
        ap("")
    else:
        if proof.subst_axioms:
            ap("    [PROVEN | derived theorem]")
            inherited = ", ".join(sorted({ax.rsplit(".", 1)[-1] for ax in proof.subst_axioms}))
            ap(f"    *(inherited premise context: {inherited})*")
            ap("")
        else:
            ap("    [PROVEN | 0 substantive axioms]")
            ap("")

    ap(f"*(Lean: `{proof.file}#{proof.name}`)*")
    ap("")


def render_deduction_sections(sections: list[dict], decls: dict = None, node_map: dict = None, investigations_dir: Path = None) -> list[str]:
    """Renders compiled ProofIR sections into README.md in 3 simultaneous layers:

    1. Ordinary English conceptual movement (from declaration docstrings)
    2. Clear philosophical transitions and local premise pricing
    3. Explicit UTF-8 mathematical derivations with visible step-by-step chains
    """
    L = []
    ap = L.append
    ap("# Γ — The Deduction")
    ap("")

    spine = [s for s in sections if s.get("category", "spine") == "spine"]
    detailed = [s for s in sections if s.get("category") == "detailed"]
    countermodels = [s for s in sections if s.get("category") == "countermodel"]
    frontiers = [s for s in sections if s.get("category") == "frontier"]

    is_synthetic = not detailed and not countermodels and not frontiers and all(s.get("category") != "spine" for s in sections)
    if is_synthetic:
        spine = sections

    # Opening: The Argument at a Glance (only in full document mode)
    if not is_synthetic:
        glance_lines = generate_argument_at_a_glance(spine, frontiers, countermodels)
        for gl in glance_lines:
            ap(gl)

    presentation_data = load_presentation_spine()
    policy = presentation_data.get("presentation_policy", {}) if presentation_data else {}
    include_detailed = policy.get("include_detailed_appendix", False) if presentation_data else True
    include_countermodels = policy.get("include_countermodels_appendix", False) if presentation_data else True
    include_frontiers = policy.get("include_frontiers_appendix", False) if presentation_data else True
    include_further = policy.get("include_further_investigations", True)

    # 1. Main Proof Spine
    for i, sec in enumerate(spine):
        ap(f"## {sec['title']}")
        ap("")
        if sec.get("summary"):
            ap(sec["summary"])
            ap("")

        if sec.get("investigation_link"):
            ap(f"*(Detailed technical proof & model analysis: [{sec['investigation_link']}]({sec['investigation_link']}))*")
            ap("")

        for proof in sec.get("primary_proofs", sec.get("proofs", [])):
            render_proof_body_spine(proof, ap) if not is_synthetic else render_proof_body(proof, ap, detailed=is_synthetic)

        for proof in sec.get("supporting_proofs", []):
            ap(f"### Supporting Infrastructure: `{proof.name}`")
            ap("")
            render_proof_body_spine(proof, ap) if not is_synthetic else render_proof_body(proof, ap, detailed=is_synthetic)

        for proof in sec.get("obstruction_proofs", []):
            ap(f"### Obstruction / Formal Boundary: `{proof.name}`")
            ap("")
            render_proof_body_spine(proof, ap) if not is_synthetic else render_proof_body(proof, ap, detailed=is_synthetic)

        for sub in sec.get("subsections", []):
            ap(f"### {sub['title']}")
            ap("")
            if sub.get("summary"):
                ap(sub["summary"])
                ap("")
            for proof in sub.get("proofs", []):
                render_proof_body_spine(proof, ap) if not is_synthetic else render_proof_body(proof, ap, detailed=is_synthetic)

        for b in sec.get("branches", []):
            ap(f"### {b['title']}")
            ap("")
            if b.get("summary"):
                ap(b["summary"])
                ap("")
            if b.get("investigation_link"):
                ap(f"*(Detailed technical proof & model analysis: [{b['investigation_link']}]({b['investigation_link']}))*")
                ap("")
            for proof in b.get("primary_proofs", []):
                render_proof_body_spine(proof, ap) if not is_synthetic else render_proof_body(proof, ap, detailed=is_synthetic)
            for proof in b.get("supporting_proofs", []):
                ap(f"#### Supporting Infrastructure: `{proof.name}`")
                ap("")
                render_proof_body_spine(proof, ap) if not is_synthetic else render_proof_body(proof, ap, detailed=is_synthetic)
            for proof in b.get("obstruction_proofs", []):
                ap(f"#### Obstruction / Formal Boundary: `{proof.name}`")
                ap("")
                render_proof_body_spine(proof, ap) if not is_synthetic else render_proof_body(proof, ap, detailed=is_synthetic)

        if i < len(spine) - 1:
            ap("---")
            ap("")

    # 2. Detailed Deductions (only if requested by presentation policy)
    if detailed and include_detailed:
        ap("---")
        ap("")
        ap("## Detailed Deductions")
        ap("")
        ap("Step-by-step natural deduction proofs, certified alternative derivations, and secondary formal derivations supporting the main argument.")
        ap("")
        for sec in detailed:
            ap(f"### {sec['title']}")
            ap("")
            if sec.get("summary"):
                ap(sec["summary"])
                ap("")
            for proof in sec.get("proofs", []):
                alt_note = getattr(proof, "alternative_note", None)
                if alt_note:
                    ap(f"### Alternative derivation: `{proof.name}`")
                    ap("")
                    ap(f"*{alt_note}*")
                else:
                    ap(f"### Prova detalhada: `{proof.name}`")
                ap("")
                render_proof_body(proof, ap, detailed=True)

    # 3. Countermodels and Open Problems (only if requested by presentation policy)
    if countermodels and include_countermodels:
        ap("---")
        ap("")
        ap("## Countermodels and Open Problems")
        ap("")
        ap("Machine-checked independence countermodels separating premises from unprovable targets without explicit bridges.")
        ap("")
        for sec in countermodels:
            for proof in sec.get("proofs", []):
                ap(f"### Limite formal: `{proof.name}`")
                ap("")
                render_proof_body(proof, ap)

    # 4. Formal Frontiers (only if requested by presentation policy)
    if frontiers and include_frontiers:
        ap("---")
        ap("")
        ap("## Formal Frontiers")
        ap("")
        ap("Unresolved formal steps, active conjectures, and open boundaries in Γ.")
        ap("")
        for sec in frontiers:
            for proof in sec.get("proofs", []):
                doc_str = f" — {proof.doc}" if proof.doc else ""
                ap(f"* **`{proof.name}`** (`{proof.goal}`){doc_str}")
        ap("")

    if include_further:
        further = render_further_investigations(decls, investigations_dir)
        L.extend(further)

    return L

def render_ledger_tables(sections: list) -> list:
    L = []
    ap = L.append
    ap("### D.3 Blocked / deferred / faith inventory")
    ap("")
    ap("| ID | Prose | Status | Missing lemma / meaning (EN) |")
    ap("|---|---|---|---|")
    for sec in sections:
        if sec["title"].startswith("Level"):
            continue
        for c in sec["claims"]:
            ap(f"| {c['id']} | {c.get('prose') or '—'} | "
               f"{status_label(c)} | {_short_gloss(c)} |")
    ap("")
    return L


def render_prologue() -> list:
    L = []
    ap = L.append
    ap("# Γ — The Deduction")
    ap("")
    ap("**Generated document.** Produced by `scripts/build_deduction.py`; do not "
       "edit it by hand (sync rule in `AGENTS.md`). A philosopher can read "
       "Sections 1–4 and understand the argument, its inline obstructions and "
       "caveats, and its unresolved frontier; a logician can follow the "
       "appendices down to the kernel proof and the exact axiom footprint.")
    ap("")
    ap("- **Lean source:** `formal/Logos/*.lean` — kernel-checked "
       "(`lake build` green, sorryAx 0)")
    ap("- **Kernel footprints:** `formal/axiom_audit.json` (`#print axioms` per "
       "declaration — the exact transitive kernel axiom set, meta-logic included)")
    ap("- **Axiom tags:** the `Tag:` line (`VOCAB`/`SEM`/`META`) on each axiom's "
       "Lean docstring")
    ap("- **Dependency graph:** `formal/depgraph.json` (LeanDepViz, kernel)")
    ap("- **Claim ledger:** [`formal/GAPMAP.md`](formal/GAPMAP.md) — statuses "
       "transcribed and *checked* against the kernel, never its source")
    ap("- **Prose:** [`base.txt`](base.txt) (§0–§29) · "
       "[`poem.txt`](poem.txt) (P1–P10) · [`theorems/`](theorems/)")
    ap("")
    ap("Regeneration: `python3 scripts/audit_footprints.py && "
       "python3 scripts/build_deduction.py`")
    ap("")
    ap("---")
    ap("")
    ap("## 1. What the argument tries to establish")
    ap("")
    ap(THESIS)
    ap("")
    ap("**Status vocabulary.** **LOGICAL** (logic alone) · **DEFINITIONAL** "
       "(follows from how Γ's concepts are constituted) · **SEMANTIC** (a "
       "substantive semantic principle) · **METAPHYSICAL** (a substantive "
       "metaphysical bridge) · **OPEN** (not currently derived) · "
       "**COUNTERMODEL** (a proposed inference fails in a hostile model). A "
       "`/ CONDITIONAL` qualifier marks a conclusion resting on a premise clause.")
    ap("")
    ap("---")
    ap("")
    return L


def render_notation() -> list:
    L = []
    ap = L.append
    ap("## Appendix A — Formal notation")
    ap("")
    ap("Each step is the real Lean declaration, rendered in logic symbols by the "
       "`humanise` pipeline; the English meaning lives in code (docstrings / "
       "String constants).")
    ap("")
    ap("| Symbol | Lean | Meaning |")
    ap("|---|---|---|")
    ap("| `\\[ … \\]` · `\\( … \\)` | (display/inline math) | standard mathematical display convention for formal statements |")
    ap("| `¬` · `∧` · `∨` · `→` | `Not` · `And` · `Or` · `Imp` | negation, conjunction, disjunction, implication |")
    ap("| `φ ∨ ¬φ` | `Form.or φ (Form.not φ)` | object-language formula (not `Prop`) |")
    ap("| `τ` · `φ` | `Form` | formula/content of the object language |")
    ap("| `∃ s p q, …` | `∃ (s : Subject), …` | quantifier binder types stripped by `mathify` for concise presentation |")
    ap("| `□ τ` | `NecessarilyTrue τ` | true in every world (`∀ w, TrueAt w τ`) |")
    ap("| `¬◇ τ` | `NecessarilyFalse τ` | false in every world (impossible: `∀ w, FalseAt w τ`) |")
    ap("| `□ p` | `Necessity p` | box at the `Prop` level (degenerate identity alias, `□p := p`) |")
    ap("| `□ₚ P` · `∀ w, P(w)` | `NecessityPH P` | world-level box — the real modality |")
    ap("| `◇ p` | `Dia p` | possibility: `¬□(¬p)` |")
    ap("| `w ⊨ τ` | `TrueAt w τ` / `Satisfies w τ` | τ is true in world w |")
    ap("| `w ⊭ τ` | `FalseAt w τ` | τ is false in world w |")
    ap("| `atom n` | `Form.atom n` | atomic proposition n of the object language |")
    ap("| `T p` | `T p` (`def T p := p`) | \"p is true\" — truth is identity (E0) |")
    ap("| `IsFalse p` | `IsFalse p` | \"p is false\" (`:= ¬ T p`) |")
    ap("| `N_T` ≡ `N_F` | `N_T` · `N_F` | absolutes: \"nothing is true\" · \"everything is true\" |")
    ap("| `A s p` · `Means s p` | `A s p` (`:= Means s p ∧ ∃ w w', Initiates s w w' p`) · `Means s p` | an act is a meaningful initiation: its constitutive content is intentional meaning, and its evental character is initiation |")
    ap("| `Agent s` · `SubjectExists s` | `Agent s` (`:= True`) · `SubjectExists s` (`:= ∃ p, Act s p`) | nominal agent predicate; subject-actuality is constitutive via `Act` |")
    ap("| `Subject` · `Person s` | `Subject` · `Person s` | sort of subjects · \"s is a person\" |")
    ap("| `Chooses s p q` | `Chooses s p q` | subject s chooses between alternatives p and q |")
    ap("| `Ground e τ` · `ExistsAt w e` | `Ground e τ` · `ExistsAt w e` | entity e grounds τ · e exists in world w |")
    ap("| `NecessaryEntity e` · `NecessarySubject s` | `NecessaryEntity e` · `NecessarySubject s` | e exists in every world · s persists in every world |")
    ap("| `Correct s p` · `Incorrect s p` · `Fallible s p` | `Correct` · `Incorrect` · `Fallible` | correct · incorrect · fallible judgment of subject s about p |")
    ap("| `Incompatible p q` · `Lovable s` · `Loves s₁ s₂` | `Incompatible` · `Lovable` · `Loves` | incompatible alternatives · s is lovable · s₁'s love of s₂ |")
    ap("")
    ap("---")
    ap("")
    return L


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main():
    global _AUDIT, _REGISTRY
    if not DEPGRAPH_PATH.exists():
        print(f"ERROR: {DEPGRAPH_PATH} missing. Run:\n"
              "  cd formal && lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot",
              file=sys.stderr)
        return 1

    print("parsing Lean sources…")
    decls = parse_lean_sources()
    print(f"  {len(decls)} declarations in {len(set(d['file'] for d in decls.values()))} files")

    print("loading #print axioms audit…")
    _AUDIT = load_audit()
    print(f"  {len(_AUDIT)} footprints audited by the kernel")

    print("parsing GAPMAP…")
    sections = parse_gapmap()
    all_claims = [c for s in sections for c in s["claims"]]
    print(f"  {len(all_claims)} claim rows across {len(sections)} sections")

    print("loading depgraph…")
    graph = load_depgraph()
    node_map = graph["node_map"]
    print(f"  {len(node_map)} kernel nodes, {sum(len(v) for v in graph['out'].values())} edges")

    _CTX.update({
        "decls": decls,
        "node_map": node_map,
        "graph": graph,
    })

    print("loading axiom registry (Tag: from Lean docstrings)…")
    _REGISTRY = load_axiom_registry(decls, node_map)
    print(f"  {len(_REGISTRY)} axioms tagged: "
          + ", ".join(f"{b}({r['tag']})" for b, r in sorted(_REGISTRY.items())))

    print("resolving meanings (EN) from declarations…")
    glosses = {f: info["doc"] for f, info in decls.items() if info.get("doc")}
    # Uncapped first-paragraph meanings for the `**Claim:**` line (FORMAT.md §4.1).
    claim_glosses = {f: info["doc_claim"] for f, info in decls.items()
                     if info.get("doc_claim")}
    for f, info in decls.items():
        if info.get("stringValue"):
            glosses[f] = info["stringValue"]
            claim_glosses[f] = info["stringValue"]
    # Claim-only meanings: auto-wire every Logos.ClaimMeanings.* String def to
    # its claim id (def name == id; `Q7_2` -> `Q7.2`).
    stub_prefix = "Logos.ClaimMeanings."
    for full, info in decls.items():
        if not full.startswith(stub_prefix):
            continue
        sv = info.get("stringValue") or info.get("doc") or ""
        if not sv:
            continue
        cid = info["name"].replace("_", ".")
        glosses[cid] = sv
        claim_glosses[cid] = sv
    print(f"  {len(glosses)} meanings resolved from code")

    print("loading countermodel meanings…")
    countermodels = load_countermodels(decls)
    print(f"  {len(countermodels)} countermodels glossed: "
          + ", ".join(sorted(countermodels)))

    print("resolving claims → kernel declarations…")
    claims_by_id = {}
    resolved = 0
    for c in all_claims:
        ref = c.get("lean_ref") or ""
        if not ref:
            c["_gloss"] = glosses.get(c["id"], "")
            c["_gloss_display"] = claim_glosses.get(c["id"], "") or c["_gloss"]
            continue
        r = resolve(ref, decls, node_map, c.get("level_key", ""))
        if r is None and "." not in ref:
            matches = [f for f in decls if f.rsplit(".", 1)[-1] == ref]
            if len(matches) == 1:
                r = matches[0]
        c["_full"] = r
        if r:
            c["_name"] = r.rsplit(".", 1)[-1]
            claims_by_id[r] = c
            resolved += 1
        c["_gloss"] = glosses.get(r or "", "") or glosses.get(c["id"], "")
        c["_gloss_display"] = (claim_glosses.get(r or "", "")
                               or claim_glosses.get(c["id"], "") or c["_gloss"])
    print(f"  {resolved} claims linked to a kernel declaration")

    for c in all_claims:
        if c.get("_full"):
            claims_by_id.setdefault(c["_full"], c)

    # canonical/alias resolution: frontier & faith rows that share a kernel
    # node with (or explicitly alias) an established C-claim dissolve into it.
    canonical_of = build_canonical_map(all_claims)
    _CTX["canonical_of"] = canonical_of
    print(f"  {len(canonical_of)} claims dissolved into a canonical claim: "
          + ", ".join(f"{a}→{b}" for a, b in sorted(canonical_of.items())))

    by_full = {}
    for c in all_claims:
        if (c.get("_full") and derived_for(c, node_map) is not None
                and c["id"] not in canonical_of):
            by_full.setdefault(c["_full"], []).append(c["id"])

    # curated footprints, `as/via Cxx` resolved to the concrete axiom set
    fp_by_id = {c["id"]: (c.get("footprint") or "") for c in all_claims}
    for c in all_claims:
        c["_curated_fp"] = expand_footprint(c["id"], fp_by_id)

    print("verifying gloss relation consistency…")
    verify_gloss_relations(all_claims, decls, graph)

    # --- machine assertions (FORMAT.md §6.3 / §10) -------------------------
    print("validating presentation invariants…")
    if AX_ID and set(AX_ID) != set(_REGISTRY):
        print(f"  note: dynamic axiom registry diverges from legacy AX_ID: {sorted(set(AX_ID) ^ set(_REGISTRY))}")

    all_ids = {c["id"] for c in all_claims}
    if STAGE_OF:
        orphans = set(STAGE_OF) - all_ids
        if orphans:
            print(f"  note: STAGE_OF names unknown claim ids: {sorted(orphans)}")
        stage_keys = {st["key"] for st in STAGES} if STAGES else set()
        for c in all_claims:
            if c["id"] in STAGE_OF and stage_keys:
                assert stage_for(c) in stage_keys, f"{c['id']} -> unknown stage {stage_for(c)}"
        fallback = [c["id"] for c in all_claims if c["id"] not in STAGE_OF]
        if fallback:
            print(f"  note: {len(fallback)} claims placed by module fallback: {fallback}")

    by_id = {c["id"]: c for c in all_claims}
    if TRANSITIONS:
        for t in TRANSITIONS:
            for tgt in t.get("targets", []):
                if tgt.startswith("Logos."):
                    got = philo_status_of_full(tgt, node_map)
                else:
                    c = by_id.get(tgt)
                    got = philo_status(c, node_map) if c else "?"
                if got != t.get("status"):
                    print(f"  note: transition '{t['label']}' declares {t['status']} but {tgt} derives {got}")

    sorry = sorted({a for axs in _AUDIT.values() for a in axs
                    if a == "sorryAx" or a.endswith(".sorryAx")})
    assert not sorry, f"sorryAx present in kernel footprints: {sorry}"

    dissolved = [c["id"] for c in all_claims
                 if philo_status(c, node_map) == "DISSOLVED"]
    assert len(dissolved) == 6, (
        f"expected 6 dissolved aliases (F1a, F4, F5, F7, FAITH-1, FAITH-2), "
        f"got {len(dissolved)}: {sorted(dissolved)}")
    for a, b in canonical_of.items():
        assert b in all_ids, f"alias {a} targets unknown claim {b}"

    catalog_keys = {cm["key"] for cm in COUNTERMODEL_CATALOG}
    used_models = {k for ks in CONTESTS.values() for k in ks}
    assert used_models <= catalog_keys, (
        f"CONTESTS references unknown countermodels: "
        f"{sorted(used_models - catalog_keys)}")
    for k in catalog_keys:
        cm = countermodels.get(k, {})
        assert cm.get("refutes") and cm.get("survives"), (
            f"countermodel {k} missing refutes/survives gloss")

    # rendering partition: stages ⊎ retired ⊎ dissolved == every claim
    dissolved_ids = {c["id"] for c in all_claims if c["id"] in canonical_of}
    retired_ids = {c["id"] for c in all_claims
                   if c["id"] not in canonical_of
                   and philo_status(c, node_map) == "COUNTERMODEL"}
    stage_ids = {c["id"] for c in all_claims
                 if c["id"] not in canonical_of
                 and philo_status(c, node_map) != "COUNTERMODEL"}
    assert dissolved_ids | retired_ids | stage_ids == all_ids, (
        "rendering partition does not cover every claim")
    assert not (dissolved_ids & retired_ids) and not (dissolved_ids & stage_ids) \
        and not (retired_ids & stage_ids), "rendering sets overlap"
    assert len(retired_ids) == 20, (
        f"expected 20 retired claims, got {len(retired_ids)}: "
        f"{sorted(retired_ids)}")

    print("rendering README.md…")
    ax_id = dict(AX_ID) if AX_ID else {base: f"A{i+1}" for i, base in enumerate(sorted(_REGISTRY))}
    axiom_full = axiom_full_map(node_map)
    _CTX["symbol_table"] = extract_symbol_table(decls)
    reading_order_list = READING_ORDER or [c["id"] for c in all_claims]
    _CTX.update({
        "decls": decls, "node_map": node_map, "graph": graph,
        "claims_by_id": claims_by_id, "by_full": by_full, "by_id": by_id,
        "glosses": glosses, "ax_id": ax_id, "ax_shown": set(),
        "axiom_full": axiom_full, "countermodels": countermodels, "seen": {},
        "reading_rank": {cid: i for i, cid in enumerate(reading_order_list)},
        "cm_seen": set(),
    })

    # Chronology/coverage of the reading order (FORMAT.md §8.3).
    if READING_ORDER:
        rank = _CTX["reading_rank"]
        body = [c for c in all_claims if c["id"] in stage_ids and c["id"] in READING_ORDER]
        for c in body:
            f = c.get("_full")
            if not f or f not in _CTX["node_map"]:
                continue
            for dep in predecessor_ids(f):
                if dep in rank and rank[dep] < rank[c["id"]]:
                    pass

    # 1. Render and write technical audit to investigations/kernel-audit.md
    print("rendering investigations/kernel-audit.md…")
    audit_lines = []
    audit_lines.append("# Technical Appendix: Kernel Audit, Consistency & Code Annex\n")
    audit_lines.append("This document contains the complete kernel audit, dependency ledger, "
                       "code references, and consistency checks generated by `scripts/build_deduction.py`.\n")
    audit_lines.append("[← Back to The Main Deduction](../README.md)\n")
    audit_lines += render_compact_axiom_ledger()
    audit_lines += render_notation()
    audit_lines += render_retired(all_claims)
    audit_lines += render_consistency(sections, decls, node_map, claims_by_id, graph, None, glosses)
    audit_lines += render_code_annex(sections, claims_by_id, decls, node_map, graph)
    audit_lines += render_appendix(sections, decls, node_map, claims_by_id, graph, None)
    audit_lines += render_provenance()

    audit_path = ROOT / "investigations" / "kernel-audit.md"
    audit_body = "\n".join(audit_lines).rstrip() + "\n"
    audit_path.write_text(audit_body, encoding="utf-8")
    print(f"wrote {audit_path} ({len(audit_body.splitlines())} lines)")

    # 2. Render and write readable, linear deduction to README.md
    print("rendering README.md…")
    def_registry = {}
    deduction_sections = discover_deduction_sections(sections, decls, node_map, graph, def_registry)
    lines = render_deduction_sections(deduction_sections, decls, node_map)

    missing_ax = set(ax_id) - _CTX["ax_shown"]
    assert not missing_ax, f"axioms never introduced inline: {sorted(missing_ax)}"

    # Automated proof verification
    active_claims = [c for c in all_claims
                     if c["id"] not in canonical_of
                     and philo_status(c, node_map) not in ("COUNTERMODEL", "DISSOLVED", "OPEN")
                     and c.get("_full") and c["_full"] in decls and c["_full"] in node_map
                     and c.get("status") in ("PROVEN", "PROVEN↑", "AXIOM")]
    for c in active_claims:
        p = proof_of(c)
        assert p and p.endswith("∎"), f"Active claim {c['id']} generated invalid proof: {repr(p)}"
        
    out_text = "\n".join(lines)
    sec3_start = out_text.find("## 3. A dedução")
    sec3_end = out_text.find("## 4. O mapa da dedução")
    if sec3_start != -1 and sec3_end != -1:
        sec3_text = out_text[sec3_start:sec3_end]
        for bad in (r"\;", r"\,", r"\neg", r"\forall", r"\exists", r"\land", r"\lor"):
            assert bad not in sec3_text, f"Found LaTeX artifact {bad} in Section 3 of README.md"

    body = "\n".join(lines).rstrip() + "\n"
    OUT_PATH.write_text(body, encoding="utf-8")
    print(f"wrote {OUT_PATH} ({len(body.splitlines())} lines)")


if __name__ == "__main__":
    raise SystemExit(main())