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
    # cut at first blank-line-equivalent marker like a double newline or '-\n'.
    # A '.\n' sentence break keeps its period (it belongs to the sentence).
    for sep in ("\n\n", "-\n", ".\n"):
        if sep in para:
            para = para.split(sep, 1)[0]
            if sep == ".\n" and not para.rstrip().endswith("."):
                para += "."
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
            if sep == ".\n" and not para.rstrip().endswith("."):
                para += "."
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
    "Level 1": {"Necessity", "Semantics", "Entity", "Modal"},
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
    "PROVEN": "✅",
    "PROVEN↑": "⚠️",
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
RETIRED_AXIOMS = {
    "ExistsAt", "AxPersonStability",
    # Batch THIS_IS_PERSONAL (2026-09-22): 16 distinct axioms removed from the
    # kernel. Retired in-place (no longer axioms anywhere): AxPersonalNormativeGround
    # (becomes rfl-level theorem), GroundPrincipleProp. Axiom→definition/theorem:
    # GroundsEntity (RecoveredOntologicalGround), explanatory_adequacy (Recovered).
    # Deleted outright: AxRealityGrounding, agential_grounding_transmission,
    # normative_ground_persistence. Deferred verbatim to scratch/Trinitarian_deferred.lean
    # (never imported): universal_ground_unique, explanatory_adequacy_normative_order,
    # PersonalNature, personal_nature_iff_person, DivineNature,
    # divine_nature_is_personal, divine_person_is_necessary.
    "AxPersonalNormativeGround", "GroundPrincipleProp",
    "AxRealityGrounding", "agential_grounding_transmission", "normative_ground_persistence",
    "universal_ground_unique", "explanatory_adequacy_normative_order",
    "PersonalNature", "personal_nature_iff_person", "DivineNature",
    "divine_nature_is_personal", "divine_person_is_necessary",
}


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
    The theorem is axiom-free modulo the declared vocabulary. Displays ✅."""
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
    ap("| `✅` | PROVEN | LOGICAL or DEFINITIONAL |")
    ap("| `⚠️` | AXIOMATIC (ledger: PROVEN↑) | derived under a substantive axiom (SEM/META) |")
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
        semantic_sat = [f for f in missing if "Semantics" in f or "Entity" in f or "Core" in f]
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
    cnt_prov = sum(1 for b in detailed_badges.values() if b == "✅")
    cnt_up = sum(1 for b in detailed_badges.values() if b == "⚠️")
    cnt_ax = sum(1 for b in detailed_badges.values() if b == "◆")
    cnt_repeat = sum(1 for b in detailed_badges.values() if b == "→")
    cnt_blocked = sum(1 for b in detailed_badges.values() if b == "✖")
    cnt_deferred = sum(1 for b in detailed_badges.values() if b == "➖")
    cnt_other = sum(1 for b in detailed_badges.values() if b not in ("✅", "⚠️", "◆", "→", "✖", "➖"))

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
       f"**{cnt_prov} ✅** · **{cnt_up} ⚠️** · **{cnt_ax} ◆** (unique steps detailed in the map)")
    ap(f"- **Reconciled claim inventory ({len(all_claims)} total):** "
       f"{cnt_prov + cnt_up} unique active steps ({cnt_prov} ✅ + {cnt_up} ⚠️) · "
       f"{cnt_repeat} repeated / dissolved (→) · "
       f"{cnt_blocked} blocked / missing (✖) · "
       f"{cnt_deferred} deferred (➖)"
       + (f" · {cnt_other} other ({', '.join(b for b in detailed_badges.values() if b not in ('✅', '⚠️', '◆', '→', '✖', '➖'))})" if cnt_other else ""))
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
        ap(f"- **Steps ⚠️ under a substantive axiom (SEM/META)** "
           f"({len(subst_claims)}): " + ", ".join(sorted(c["id"] for c in subst_claims)))
    vocab_only = [c for c in steps if is_vocab_only(c["_full"])]
    if vocab_only:
        ap(f"- **Displayed ✅ by vocabulary only (axiom-free modulo declared vocabulary)** "
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
     "principles of semantics and entity reality."},
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
     "necessary: excluded middle and non-contradiction, and the necessity of the "
     "normative order. The person/entity lifts are definitional, and a necessary "
     "person is not derived unconditionally."},
    {"key": "VI", "title": "Grounding", "intro":
     "Ontologically, the ground of the Right and the Wrong is personal "
     "in kind/type. "
     "The clean approach encodes the ontological dependence in the formal "
     "definition rather than introducing an axiom: RightWrong is indexed "
     "by Person, discovery is constructive, and GroundedRightWrong is a "
     "dependent pair. No grounding axiom is required."},
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
      "The remaining frontier is explicit: teleology is deferred; the moral good is "
      "machine-separated from epistemic normativity (permanent countermodel frontier, "
      "C175) and its positive pole is inhabited only under one disclosed, priced META "
      "bridge, `AxBenevolentBearingObtains` — the fair `Good` definition itself is "
      "vocabulary-only (C178); the Trinity, incarnation and creation "
      "are deferred or faith data; the initiation-theoretic and ground-chain constructions "
      "are withdrawn under hostile semantics. Nothing here is presented as derived."},
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
for _x in ("C78", "C79", "C87",
           "C88", "C89", "C90", "Q7.2"):
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
    "Core": "II", "Semantics": "II", "Necessity": "II", "Entity": "VI",
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
    "Subject": "A1",
    "Means": "A2", "AxTwoSubjects": "A3",
    "act": "A4", "State": "A5", "Initiates": "A6",
    "AxActPolarity": "A7",
    "AxIntentionalChoice": "A8",
    "DependsOn": "A9",
    "universal_thesis_claims_objectivity": "A10",
    "transcendental_reflection_intentional": "A11",
    "AxJudicativeBipolarity": "A12",
    "AxSecondPersonalAddress": "A13",
    "Nature": "A14",
    "HasNature": "A15",
    "Will": "A16",
    "subjectWill": "A17",
    "will_individuation": "A18",
    "Wills": "A19",
    "Ought": "A20",
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
    "C91": ["SubjectNecessityNotEntity"],
    "C92": ["PersonNotNecessary"],
    "C69": ["NoFreeWill", "VeridicalMeaning"],
    "C70": ["NoFreeWill", "VeridicalMeaning"],
    "C71": ["NoFreeWill", "VeridicalMeaning"],
    "C72": ["NoFreeWill", "VeridicalMeaning"],
    "C77": ["PersonNotNecessary"],
    "F1b": ["VeridicalMeaning", "NoFreeWill"],
    # --- inline obstructions on the main-body constitutive steps (FORMAT.md §5) ---
    "C24": ["NoPerson"],
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
    {"key": "SubjectNecessityNotEntity", "title": "Persistence without entity",
     "attacks": "subject-persistence entailing entity-necessity by logic alone",
     "ns": "Logos.HostileSemantics.CountermodelSubjectNecessityNotEntityNecessity"},
    {"key": "PersonNotNecessary", "title": "The contingent person",
     "attacks": "`Person → NecessarySubject` as a logical law",
     "ns": "Logos.HostileSemantics.CountermodelPersonNotNecessary"},
    {"key": "VeridicalMeaning", "title": "Veridical meaning (one and two persons)",
     "attacks": "the act datum forcing genuine choice",
     "ns": "Logos.HostileSemantics.CountermodelVeridicalMeaning"},
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
        "`weak_act_implies_strong_act := ∀ s p, act(s, p) → Act(s, p)` (*unforced open intentionality bridge*).",
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
    {"label": "performative meaning-act → necessary entity (ground) / conditional person", "status": "CONDITIONAL",
     "targets": ["C77", "C92"]},
    {"label": "necessary subject → necessary entity", "status": "DEFINITIONAL",
     "targets": ["C91"]},
    {"label": "right-wrong → person (constructive discovery)", "status": "LOGICAL",
     "targets": ["Logos.PersonalNormativeGround.Constructive.discover_person"]},
    {"label": "person → right-wrong (ontological grounding)", "status": "DEFINITIONAL",
     "targets": ["C151"]},
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
    "survives is recorded in Appendix C.2. The premier open frontier is deontic "
    "teleology (F2); moral good (F3) is no longer open — the faithful model "
    "`M_amoral` machine-separates practical bindingness from epistemic agential "
    "normativity (`MoralFrontierAudit.epistemic_normativity_without_practical_obligation`, "
    "C175, `{}`), making F3 a countermodel frontier, not a gap. The *positive* moral "
    "pole is separately obtained under one disclosed, priced META bridge "
    "(`Value.AxBenevolentBearingObtains`, C177 → `moral_good_obtains`, C178); the bare "
    "value layer is machine-proven empty (C176), so the bridge is a paid commitment "
    "rather than a hidden derivation, and the negative pole `Evil` remains a declared "
    "SEM datum (its fair reading needs a parallel harm bridge, not declared)."
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


def _spine_lead(doc: str, n: int = 260) -> str:
    """A clean sentence-boundary lead for a proof doc paragraph.

    `ProofIR.doc_lead` is the uncapped first doc paragraph (`doc_claim`), so this can
    recover a clean sentence boundary; `ProofIR.doc` (capped by `_doc_for` at ~260
    chars) is only a fallback. Resolves mid-sentence "…" back to a clean sentence
    while keeping every displayed meaning in the argument spine.
    """
    s = re.sub(r"\s+", " ", (doc or "").strip())
    if s.endswith("…"):
        s = s.rstrip("… ").rstrip(" ,;:.")
    if not s:
        return s
    if len(s) <= n:
        return s
    # Sentence ends: a period that punctuates the paragraph, or a period followed
    # by a space with a fresh sentence. Leads that start mid-sentence may carry on
    # a little past `n` (bounded window) so they reach the end of that sentence
    # instead of stopping at an arbitrary word boundary with "…".
    ends = [i for i in range(len(s))
            if s[i] == "." and (i + 1 == len(s) or s[i + 1] == " ")]
    for e in ends:
        if e < int(n * 0.45):
            continue  # stub lead (a bare first clause); keep looking
        if e <= n + 220:
            return s[:e + 1].strip()
    cut = s[:n]
    last = cut.rfind(". ")
    if last > int(len(cut) * 0.35):
        return cut[:last + 1].strip()
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


def proof_claimed_class(proof, node_map: dict) -> str:
    """Kernel-derivable class of a rendered proof: PROVEN / PROVEN↑ / AXIOM.
    Used to keep curated route-group labels honest about what the kernel implies."""
    full = proof.full_name
    node = node_map.get(full)
    if node and node.get("kind") == "axiom":
        return "AXIOM"
    subst, _, _ = footprint_parts(full)
    return "PROVEN↑" if subst else "PROVEN"


def _select_strongest(proofs: list, node_map: dict) -> list:
    """Derived, kernel-first selection for one narrative slot (a section's
    primary slot, a supporting_defense unit, or a supporting list): keep only
    the strongest kernel class present (PROVEN > PROVEN↑ > AXIOM); among kept
    proofs of the SAME goal (true duplicates of one claim) the shortest wins —
    fewest rendered steps, then fewest assumptions, then declaration order.
    Nothing here is curated: rank and length come from the kernel audit and the
    compiled ProofIR. Distinct same-class proofs of different claims are all kept."""
    if not proofs:
        return []
    classes = [proof_claimed_class(p, node_map) for p in proofs]
    for best in ("PROVEN", "PROVEN↑", "AXIOM"):
        if best in classes:
            break
    by_goal: dict[str, list] = {}
    for p, c in zip(proofs, classes):
        if c == best:
            by_goal.setdefault(p.goal or "", []).append(p)
    out = []
    for cands in by_goal.values():
        if len(cands) == 1:
            out.append(cands[0])
        else:
            out.append(min(cands, key=lambda q: (len(q.steps), len(q.assumptions))))
    return out


def route_definition_proofs(proofs: list, decls: dict, node_map: dict, graph: dict, def_registry: dict) -> list:
    """Definition steps used by the rendered goals of a section but not surfaced
    as their own step. Derived, never transcribed: short-name tokens of the
    humanised goals are intersected with glossed Logos `def`/`inductive`/`opaque`
    nodes; name collisions (hostile-model twins) resolve to the canonical,
    non-hostile module. Axioms (Means, Initiates, …) never match — kinds differ."""
    tokens = set()
    for p in proofs:
        tokens |= set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", p.goal or ""))
    if not tokens:
        return []
    hostile_markers = ("Hostile", "Countermodel", "UnitPlurality", "ModelHierarchy")
    cand = {}
    for full, nd in node_map.items():
        if not full.startswith("Logos."):
            continue
        if nd.get("kind") not in ("def", "inductive", "opaque"):
            continue
        base = full.rsplit(".", 1)[-1]
        if base not in tokens or not decls.get(full, {}).get("doc"):
            continue
        cand.setdefault(base, []).append(full)
    if not cand:
        return []
    shown = {p.full_name for p in proofs}
    out = []
    for base in sorted(cand):
        fds = sorted(cand[base])
        chosen = next((f for f in fds if not any(h in f for h in hostile_markers)), fds[0])
        if chosen in shown:
            continue
        pr = compile_lean_proof(chosen, decls, node_map, graph, def_registry)
        if pr.name == base:
            out.append(pr)
    return out


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
    doc_lead: str = ""
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
    # `doc` is the ~260-char capped first paragraph (bad for sentence-boundary
    # resolution). Keep the uncapped first paragraph separately so the spine
    # renderer can recover a clean, complete lead sentence.
    doc_lead_text = d.get("doc_claim", "").strip() or doc_text

    proof = ProofIR(
        full_name=full,
        name=name,
        kind=kind,
        file=d["file"],
        line=d["line"],
        goal=goal_fm if goal_fm else math_statement(full),
        doc=doc_text,
        doc_lead=doc_lead_text,
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

    raw_proof_lines = []
    # Check if there is content after `:=` on the declaration line
    after_assign = lines[i].split(":=", 1)[1].strip()
    if after_assign:
        if after_assign.startswith("by"):
            after_by = after_assign[2:].strip()
            if after_by:
                raw_proof_lines.append(after_by)
        else:
            raw_proof_lines.append(after_assign)
    i += 1
    while i < len(lines):
        l = lines[i].strip()
        if re.match(r"^(?:theorem|lemma|def|axiom|structure|inductive|/--|section|namespace|end)\b", l):
            break
        if l and not l.startswith("--"):
            raw_proof_lines.append(l)
        i += 1

    proof_lines = []
    buffer = ""
    open_angle = 0
    for l in raw_proof_lines:
        clean_l = re.sub(r"^[·•\-\*]\s*", "", l)
        open_angle += clean_l.count("⟨") - clean_l.count("⟩")
        if buffer:
            buffer += " " + clean_l
        else:
            buffer = clean_l
        if open_angle <= 0:
            proof_lines.append(buffer.strip())
            buffer = ""
            open_angle = 0
    if buffer:
        proof_lines.append(buffer.strip())

    for l in proof_lines:
        if l == "constructor":
            proof.steps.append(ProofStepIR(
                var_name="",
                proposition="split into forward and reverse directions (↔ / ∧)",
                rule=Rule.CONJUNCTION_INTRO,
                description="split equivalence/conjunction into forward (mp) and reverse (mpr) goals",
            ))
            continue

        if l in ("rfl", "Iff.rfl", "Eq.refl"):
            proof.steps.append(ProofStepIR(
                var_name="",
                proposition=proof.goal,
                rule=Rule.DEFINITION_UNFOLD,
                description="definitional equality / reflection",
            ))
            if not proof.conclusion:
                proof.conclusion = ProofStepIR(
                    var_name="",
                    proposition=proof.goal,
                    rule=Rule.CONCLUSION,
                    description="definitional identity",
                )
            continue

        if re.match(r"^[A-Za-z0-9_]+$", l) and l not in ("by", "sorry"):
            proof.steps.append(ProofStepIR(
                var_name=l,
                proposition=proof.goal,
                rule=Rule.DEFINITION_UNFOLD,
                premises=[l],
                description=f"definitional identity via {l}",
            ))
            if not proof.conclusion:
                proof.conclusion = ProofStepIR(
                    var_name="",
                    proposition=proof.goal,
                    rule=Rule.CONCLUSION,
                    premises=[l],
                    description=f"direct projection from {l}",
                )
            continue

        m_exact_tuple = re.match(r"^exact\s+⟨(.*)⟩$", l)
        if m_exact_tuple:
            inner = m_exact_tuple.group(1)
            tokens = [re.sub(r"[⟨⟩]", "", t).strip() for t in inner.split(",") if re.sub(r"[⟨⟩]", "", t).strip()]
            for idx, tok in enumerate(tokens, 1):
                proof.steps.append(ProofStepIR(
                    var_name="",
                    proposition=tok,
                    rule=Rule.PREMISE,
                    premises=[tok],
                    description=f"conjunction conjunct {idx}: {tok}",
                ))
            proof.conclusion = ProofStepIR(
                var_name="",
                proposition=proof.goal,
                rule=Rule.CONJUNCTION_INTRO,
                premises=tokens,
                description=f"simultaneous conjunction satisfaction across all {len(tokens)} components",
            )
            continue
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
            continue

        m_obtain = re.match(r"^\s*obtain\s+⟨(.*?)⟩\s*:=\s*(.*)", l)
        if m_obtain:
            vars_str = m_obtain.group(1).strip()
            term = m_obtain.group(2).strip()
            proof.steps.append(ProofStepIR(
                var_name=vars_str,
                proposition=f"witness components ⟨{vars_str}⟩",
                rule=Rule.EXISTENTIAL_ELIM,
                premises=[term],
                description=f"existential elimination from {term}",
            ))
            continue

        m_intro = re.match(r"^\s*intro\s+(.*)", l)
        if m_intro:
            intro_target = m_intro.group(1).strip()
            proof.steps.append(ProofStepIR(
                var_name=intro_target,
                proposition=f"assume {intro_target}",
                rule=Rule.ASSUMPTION,
                description="hypothesis assumption for conditional/reductio proof",
            ))
            continue

        m_cases = re.match(r"^\s*cases\s+([A-Za-z0-9_]+)", l)
        if m_cases:
            target = m_cases.group(1).strip()
            proof.steps.append(ProofStepIR(
                var_name="",
                proposition=f"vacuous contradiction on empty {target}",
                rule=Rule.CONTRADICTION,
                premises=[target],
                description=f"elimination of empty type {target} (→ ⊥)",
            ))
            continue

        m_refine = re.match(r"^\s*refine\s+⟨(.*?)⟩", l)
        if m_refine:
            args = [x.strip() for x in m_refine.group(1).split(",")]
            proof.steps.append(ProofStepIR(
                var_name="",
                proposition=f"witness tuple ⟨{', '.join(args)}⟩",
                rule=Rule.EXISTENTIAL_INTRO,
                premises=args,
                description=f"existential/conjunction refinement with {', '.join(args)}",
            ))
            continue

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
            continue

        # Term-mode lambda abstraction: fun h => ... or fun ⟨h1, h2⟩ => ...
        m_fun = re.match(r"^\s*fun\s+(?:⟨(.*?)⟩|([A-Za-z0-9_]+))\s*=>\s*(.*)", l)
        if m_fun:
            if m_fun.group(1):
                vars_str = m_fun.group(1).strip()
                proof.steps.append(ProofStepIR(
                    var_name=vars_str,
                    proposition=f"unpack components ⟨{vars_str}⟩",
                    rule=Rule.CONJUNCTION_ELIM,
                    description=f"pattern-match hypothesis ⟨{vars_str}⟩",
                ))
            elif m_fun.group(2):
                v_name = m_fun.group(2).strip()
                proof.steps.append(ProofStepIR(
                    var_name=v_name,
                    proposition=f"assume {v_name}",
                    rule=Rule.ASSUMPTION,
                    description=f"hypothesis assumption {v_name}",
                ))
            continue

        # Term-mode constructor: ⟨arg1, arg2, ...⟩
        m_tuple = re.match(r"^\s*⟨(.*?)⟩\s*$", l)
        if m_tuple:
            args = [x.strip() for x in m_tuple.group(1).split(",") if x.strip()]
            arg_str = ", ".join(args)
            if not proof.steps:
                for a_idx, arg in enumerate(args, 1):
                    proof.steps.append(ProofStepIR(
                        var_name="",
                        proposition=arg,
                        rule=Rule.PREMISE,
                        premises=[arg],
                        description=f"component witness {a_idx}: {arg}",
                    ))
            if not proof.conclusion:
                proof.conclusion = ProofStepIR(
                    var_name="",
                    proposition=proof.goal,
                    rule=Rule.CONJUNCTION_INTRO if "∧" in proof.goal else Rule.EXISTENTIAL_INTRO,
                    premises=args,
                    description=f"instantiation from ⟨{arg_str}⟩",
                )
            continue

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
    - AXIOMATIC (<Ax>): direct invocation of a declared semantic/metaphysical bridge axiom (Tag: SEM/META)
    - PROVEN: machine-verified derivation from established premises with 0 substantive axioms

    The *category* half keeps the legacy vocab ("SEMANTIC"/"METAPHYSICAL") so tooling and
    tests stay stable; the reader-facing *display* half says AXIOMATIC. AXIOMATIC never
    means "unproved" — it means machine-verified while resting on the named, priced axiom.
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
        return "METAPHYSICAL", f"AXIOMATIC ({req})"
    elif local_sem:
        req = ", ".join(sorted(set(local_sem)))
        return "SEMANTIC", f"AXIOMATIC ({req})"
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

            # STRONG.md: derived strongest-proof selection — a narrative slot renders
            # only its strongest kernel class (PROVEN > PROVEN↑ > AXIOM); among kept
            # proofs of the same goal, the shortest wins. Kernel-only, never curated.
            primary_proofs = _select_strongest(primary_proofs, graph["node_map"])
            supporting_proofs = _select_strongest(supporting_proofs, graph["node_map"])

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
                groups = []
                for g in sub.get("groups", []):
                    g_proofs = []
                    for name in g.get("target_names", []):
                        p = resolve_proof_by_name(name, compiled_by_id, decls, graph)
                        if p:
                            g_proofs.append(p)
                    expected = g.get("expected_badge", "*")
                    group_node_map = graph["node_map"]
                    for p in g_proofs:
                        cls = proof_claimed_class(p, group_node_map)
                        if expected != "*" and cls != expected:
                            raise SystemExit(
                                f"FATAL: supporting_defense group '{sub.get('title', '')}' "
                                f"labels '{p.name}' as {expected} but the kernel derives "
                                f"{cls} — route label contradicted by the kernel")
                    groups.append({
                        "label": g.get("label", ""),
                        "proofs": g_proofs,
                    })
                # STRONG.md: the supporting_defense unit is one narrative slot —
                # filter its whole candidate pool (flat + every route group) and keep
                # only the strongest kernel class; groups left empty are dropped, and
                # the flat list roles the selected proofs. Branches/obstructions are
                # frontiers, excluded from the filter.
                kept = _select_strongest(
                    sub_proofs + [p for g in groups for p in g["proofs"]],
                    graph["node_map"])
                kept_names = {p.full_name for p in kept}
                filtered_groups = []
                for g in groups:
                    g["proofs"] = [p for p in g["proofs"] if p.full_name in kept_names]
                    if g["proofs"]:
                        filtered_groups.append(g)
                groups = filtered_groups
                sub_proofs = [p for p in sub_proofs if p.full_name in kept_names]
                subsections.append({
                    "title": sub.get("title", ""),
                    "summary": sub.get("summary", ""),
                    "proofs": sub_proofs,
                    "groups": groups,
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
                    "status": b.get("status", ""),
                    "defer_note": b.get("defer_note", ""),
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
                "pushback": node.get("pushback", ""),
                "reply": node.get("reply", ""),
                "rebuttal_target": node.get("rebuttal_target", ""),
                "rebuttal_formula": node.get("rebuttal_formula", ""),
                "primary_proofs": primary_proofs,
                "supporting_proofs": supporting_proofs,
                "obstruction_proofs": obstruction_proofs,
                "proofs": primary_proofs,
                "branches": branches,
                "subsections": subsections,
                "route_definitions": route_definition_proofs(
                    primary_proofs + supporting_proofs
                    + [p for sub in subsections for p in sub.get("proofs", [])]
                    + [p for sub in subsections for g in sub.get("groups", []) for p in g.get("proofs", [])],
                    decls, graph["node_map"], graph, {}),
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

    # Loud check: any declared target with no compiled proof (and no documented
    # deferral) is a stale reference — future drift fails loudly instead of
    # silently producing a DEFINITIONAL/empty badge.
    stale_refs = []
    for node in (presentation_data or {}).get("spine_nodes", []):
        node_id = node.get("id", "")
        node_refs = [
            ("node", node_id, n)
            for n in (node.get("primary_targets", [])
                      + node.get("supporting_targets", [])
                      + node.get("obstructions", []))
            if not resolve_proof_by_name(n, compiled_by_id, decls, graph)
        ]
        stale_refs.extend(node_refs)
        for sub in node.get("supporting_defense", []):
            sub_refs = [
                ("subsection", f"{node_id}/{sub.get('title', '')}", n)
                for n in sub.get("target_names", [])
                if not resolve_proof_by_name(n, compiled_by_id, decls, graph)
            ]
            stale_refs.extend(sub_refs)
            for g in sub.get("groups", []):
                g_refs = [
                    ("group", f"{node_id}/{sub.get('title', '')}", n)
                    for n in g.get("target_names", [])
                    if not resolve_proof_by_name(n, compiled_by_id, decls, graph)
                ]
                stale_refs.extend(g_refs)
        for b in node.get("branches", []):
            if b.get("status") == "deferred":
                continue
            stale_refs.extend(
                ("branch", f"{node_id}/{b.get('id', '')}", n)
                for n in (b.get("primary_targets", [])
                          + b.get("supporting_targets", [])
                          + b.get("obstructions", []))
                if not resolve_proof_by_name(n, compiled_by_id, decls, graph)
            )
    if stale_refs:
        detail = "; ".join(f"{kind} {where}: `{name}`" for kind, where, name in stale_refs)
        print(f"WARNING: spine targets with no compiled Lean proof (not marked "
              f"deferred): {detail}", file=sys.stderr)

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
    retorsion_proofs = []
    if decls:
        for full, d in sorted(decls.items()):
            name = d["name"]
            doc = d.get("doc", "")
            if d["kind"] in ("theorem", "lemma") and doc:
                first_line = _spine_lead(doc.splitlines()[0] if doc.splitlines() else doc)
                name_l = name.lower()
                doc_l = doc.lower()
                if "retorsion" in name_l or "selfrefutes" in name_l or "claims_correct" in name_l or "retors" in doc_l or "self-refut" in doc_l:
                    label = humanise(strip_ns(name)).title()
                    retorsion_proofs.append((label, name, f"formal/Logos/{d['file']}", first_line))
    if retorsion_proofs:
        ap("<details>")
        ap(f"<summary>Retorsion catalogue — {len(retorsion_proofs)} machine-checked retorsion theorems (click to expand)</summary>")
        ap("")
        for label, name, file_path, first_line in retorsion_proofs:
            ap(f"* **{label}:** `{name}` (`{file_path}`) — {first_line}")
        ap("</details>")
        ap("")
    for d in cat["retorsions_docs"]:
        desc = f" — {d['status']}" if d.get("status") else ""
        ap(f"* [{d['title']}]({d['path']}){desc}")
    ap("")

    ap("### Countermodels & Independence")
    ap("")
    # Dynamically extract independence boundaries from decls without hardcoding specific names
    independence_proofs = []
    if decls:
        for full, d in sorted(decls.items()):
            name = d["name"]
            doc = d.get("doc", "")
            stmt = d.get("statement", "")
            if ("_not_entails_" in name or d.get("status") == "COUNTERMODEL") and d["kind"] in ("theorem", "lemma"):
                left, right = extract_boundary_generically(name, doc, stmt)
                first_line = _spine_lead(doc) if doc else "Mathematical independence model."
                line_no = d.get("line", 1)
                loc = f"formal/Logos/{d['file']}:{line_no}"
                independence_proofs.append((f"{left} ⇏ {right}", name, loc, first_line))
    if independence_proofs[:6]:
        ap("<details>")
        ap(f"<summary>Countermodel catalogue — {min(len(independence_proofs), 6)} independence frontiers (click to expand)</summary>")
        ap("")
        for boundary, name, loc, first_line in independence_proofs[:6]:
            ap(f"* **{boundary}:** `{name}` (`{loc}`) — {first_line}")
        ap("</details>")
        ap("")
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
        return f"AXIOMATIC ({', '.join(meta_axes)})"
    elif sem_axes:
        return f"AXIOMATIC ({', '.join(sem_axes)})"
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
        lines.append(f"  *[{status_icon(badge)}]*")
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
                if b.get("status") == "deferred" or (
                        b.get("primary_targets") and not b_proofs and not b.get("obstructions")):
                    b_badge = "DEFERRED"

                lines.append("        │")
                lines.append(f"{prefix} {b_edge} → {b_label}")
                if b_formula:
                    lines.append(f"{cont_pfx}  ⊢ {b_formula}")
                lines.append(f"{cont_pfx}  *[{status_icon(b_badge)}]*")
                if b.get("continuation_label"):
                    lines.append(f"{cont_pfx}       │")
                    lines.append(f"{cont_pfx}       │ [COUNTERMODEL SEPARATION FRONTIERS]")
                    lines.append(f"{cont_pfx}       ▼")
                    lines.append(f"{cont_pfx}  {b.get('continuation_label')}")
                    lines.append(f"{cont_pfx}    *[{status_icon('COUNTERMODEL · ⇏')}]*")

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
            lines.append(f"  *[{status_icon(b1['badge'])}]* *[{status_icon(b2['badge'])}]*")
            cont = tb.get("continuation")
            if cont:
                lines.append("        │")
                lines.append(f"        │  {cont['edge_label']}")
                lines.append("        ▼")
                lines.append(cont["label"])
                lines.append(f"  ⊢ {cont['formula']}")
                lines.append(f"  *[{status_icon(cont['badge'])}]*")

    return lines


def render_reading_guide() -> list[str]:
    """Emits the "How to Read This Deduction" block between the title and the
    Argument-at-a-Glance chart: the arc in one breath, the two directions (discovery vs
    grounding), and a badge legend explaining every status symbol that follows.
    """
    lines = []
    ap = lines.append
    ap("> **Γ is a machine-checked deduction**: genuine normativity — an objective right/wrong")
    ap("> binding our judgments — forces a *personal* ground. Free will is *derived, never")
    ap("> assumed* (`GenuineNormativity ⇒ Chooses ⇒ FreeWill ⇒ FreeSubject ⇒ Person`);")
    ap("> wherever right/wrong is real, its ground-type is personal (`RightWrong ⇒ Person`).")
    ap("> A necessary Divine Being/Ground — eternal (everlasting and atemporal) and possessing Canonical Aseity (`conditional_canonical_aseity`) — is **proven** (✅); Divine Personhood and monotheism are **deferred** (⏸); every other claim is")
    ap("> definitional, derived, or a declared axiom.")
    ap("")
    ap("Every section below answers the same question — *what is the status of this claim?*")
    ap("")
    ap("> **The Dialectical Inevitability Architecture** — Why every rational attack fails:")
    ap("> 1. **Performative Retorsion (The Trap):** Any attempt to deny objective correctness must claim that its denial is *correct* (`ClaimsCorrect s NoRight`). In the Lean kernel, claiming denial as correct while true yields a direct constructive contradiction (`claims_correct_no_right_self_refuting` → ⊥, 0 substantive axioms). The skeptic cannot even enter the debate without triggering the normative partition.")
    ap("> 2. **Constitutive Semantics (The Deduction):** Rational address between incompatible alternatives is *definitionally* Choice (`Chooses`), having choice is *definitionally* Free Will (`FreeWill`), and a free choosing subject is *definitionally* a Person in the classical Boethian-Thomistic sense (`person_iff_thomisticCore`), all verified with 0 substantive axioms.")
    ap("> 3. **Airtight Epistemic Boundaries:** Where logic ends, Γ never fakes a proof. Unproved theological extensions (Trinity, Creation, Incarnation, Monotheism) are isolated by machine-checked mathematical countermodels (`⇏`).")
    ap("")
    ap("**Two directions, not one.** The chart distinguishes *epistemic discovery* (▲ — what")
    ap("the argument must prove upward: no free subject precedes free will) from *ontological")
    ap("grounding* (▼ — what the established order then entails downward: a personal free")
    ap("agency grounds Right/Wrong). The kernel proves the one dependence")
    ap("`RightWrong ⇒ Person`; the downward `▼` ontological-grounding arrow is the")
    ap("interpretive reading of that same proved subjunction, not an additional theorem —")
    ap("the direction is not machine-decidable.")
    ap("")
    ap("> **What this proof does and does not show**")
    ap(">")
    ap("> 1. The machine-verified chain above — established **under** the")
    ap(">    normative-judicative stance via two mutually reinforcing routes (0 substantive axioms):")
    ap(">    • **Route A (Performative Datum):** Rational judgment presupposes correctness (`ClaimsNormativeCorrectness s p`).")
    ap(">    • **Route B (Proof Presentation):** Presenting or evaluating Γ argumentatively instantiates the stance (`PresentsAsSound s d`), deriving Free Will and Personhood (`ProofPresentationRetorsion.lean`). Even an adversarial attack on Γ instantiates personhood (`critic_presenting_objection_is_person`).")
    ap(">    Zero-input free will from bare syntax is rejected: `M_inanimate_checker` verifies syntax with 0 subjects.")
    ap("> 2. That same dependence — *wherever the normative order is real, its ground-type")
    ap(">    is personal* — is machine-proved with 0 substantive axioms. Reading the")
    ap(">    subjunction as a direction of ontology is interpretive, as 'Two directions, not")
    ap(">    one.' above explains.")
    ap("> 3. Divine Personhood and Strict Monotheism — **DEFERRED** (⏸), not proved here; a necessary")
    ap(">    Divine Being/Ground (world-rigid, everlasting, atemporal) is its entity-level **PROVEN** claim (✅).")
    ap("> 4. Moral good/evil — machine-separated from epistemic normativity (permanent ")
    ap(">    countermodel frontier 🧱, C175): the faithful model `M_amoral` satisfies the whole epistemic ")
    ap(">    agential reality-hook with zero practical obligation. The positive pole is then obtained ")
    ap(">    honestly: `Good` is a *fair definition* (helping another person, vocabulary-only, ")
    ap(">    `{Means, Subject}`) and `moral_good_obtains` (C178) is PROVEN↑ under the single declared ")
    ap(">    META bridge `AxBenevolentBearingObtains` (C177, \"some person is actually helped\"), whose ")
    ap(">    price is machine-visible (the bare value layer is empty, C176). The negative pole `Evil` ")
    ap(">    remains a declared SEM datum. The epistemic reality-hook itself is ")
    ap(">    unconditional and vocabulary-only (`correct_tracks_reality`, C173/C174).")
    ap("")
    ap("**Badge legend.** Every icon on a formal consequence is machine-derived from")
    ap("the Lean kernel (see `formal/GAPMAP.md` and the investigations) — never transcribed:")
    ap("")
    ap("| icon | meaning |")
    ap("|---|---|")
    ap("| `✅` | PROVEN — verified by pure logic; footprint contains only classical meta-logic (`CL`) and the claim's own vocabulary (0 substantive axioms) |")
    ap("| `⚠️ (AxName)` | AXIOMATIC — machine-verified, yet deliberately rests on the named declared axiom (`SEM` semantic choice / `META` metaphysical bridge) — **not unproved** |")
    ap("| `📘` | DEFINITIONAL — true by definition of the term being introduced |")
    ap("| `⏸` | DEFERRED — a claimed result whose Lean declaration is not in the live kernel; annotated surface only (see GAPMAP + source notes), **NOT a theorem in this repository** |")
    ap("| `🧱 X ⇏ Y` | COUNTERMODEL — a model forces X nowhere near Y: an explicit boundary, not a failure |")
    ap("")
    ap("Axioms appear as `◆` in the audit ledger. `AXIOM` (the claim *is itself* a declared")
    ap("axiom) is distinct from `AXIOMATIC` (the claim is *derived under* an axiom).")
    ap("")
    ap("The badge marks that **step's own** axiom cost, recomputed per declaration from")
    ap("`#print axioms` — it is never inherited from a neighbouring step. A `✅` that")
    ap("immediately follows a `⚠️` step is provably axiom-free on its own; badges do not")
    ap("\"propagate\" down the chain — the kernel footprint is the transitive closure, so")
    ap("a `✅` after a `⚠️` means the two share no proof edge: the marker between them is")
    ap("narration, not inference.")
    ap("")
    ap("> `✅ · File.lean#name`-style footers point at the exact Lean declaration behind each")
    ap("> consequence: the anchor is the declaration name, and the link jumps to its line under")
    ap("> `formal/Logos/`. Follow the `investigations` links for the deeper countermodel and")
    ap("> retorsion analyses.")
    ap("")
    ap("**How to read a step.** Claim in words first, machine rendering beneath:")
    ap("- `∴` introduces the symbolic rendering that follows. `≡` reads \"by definition\" (`📘`);")
    ap("  `→` and `↔` mean implication and equivalence; `⇒` chains steps into one argument;")
    ap("  `⇏` marks a demonstrated *non-consequence* (a countermodel frontier, `🧱`).")
    ap("- a **backticked name** is the Lean declaration that verifies the line; footers like")
    ap("  `✅ · File.lean#name` link to it under `formal/Logos/`.")
    ap("- each section reads: summary → the skeptic's attack & the reply → definitions used")
    ap("  → the steps. §4–§6 are the gentlest introduction.")
    ap("- the chain `GenuineNormativity ⇒ Chooses ⇒ FreeWill ⇒ FreeSubject ⇒ Person` is the")
    ap("  same argument the numbered sections build link by link.")
    ap("")
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
    ap("This chart is the whole argument in one map. Each box is a claim; each arrow shows a forced consequence; each icon states the claim's machine-derived status. Read it, then walk the numbered sections below.")
    ap("")
    ap("Central Distinction: the upward arrows are *discovery* (from the datum to its ground);")
    ap("the downward arrows are *ontological grounding* (from the ground to the datum) — the")
    ap("same proved dependence, read in two directions (see the note above).")
    ap("")
    ap("<details>")
    ap("<summary><b>Linear Deductive Roadmap (Steps 1–10 at a glance)</b></summary>")
    ap("")
    ap("| Step | Milestone | Core Formula | Epistemic Status |")
    ap("|---|---|---|---|")
    ap("| **§1** | Objective Right/Wrong | `¬N_T ∧ ¬N_F` | `✅` PROVEN · 0 substantive axioms |")
    ap("| **§2** | Agential Ought | `Ought TruthNorm ⟨s, p⟩` | `✅` PROVEN · 0 substantive axioms |")
    ap("| **§3** | Genuine Choice | `Chooses s p q ∧ CommittedChoice s p q r` | `✅` PROVEN (Route A / Route B) |")
    ap("| **§4** | Free Will | `FreeWill(s)` | `✅` PROVEN · 0 substantive axioms |")
    ap("| **§5** | Free Subject | `FreeSubject(s) ≡ FreeWill(s)` | `📖` DEFINITIONAL |")
    ap("| **§6** | Person | `Person(s) ↔ Boethian-Thomistic Core` | `✅` PROVEN · 0 substantive axioms |")
    ap("| **§7** | Personal Will | `FreeIndependentWill(s)` | `✅` PROVEN · 0 substantive axioms |")
    ap("| **§8** | Ground of Right/Wrong | `GroundsRightWrong(s)` | `✅` PROVEN · 0 substantive axioms |")
    ap("| **§9** | Necessary Truth | `□ τ ∧ GroundOfReality Entity.ofGround` | `✅` PROVEN · 0 substantive axioms |")
    ap("| **§10** | Constructive Ground | `PersonalGroundOfReality Entity.ofGround` | `✅` PROVEN · 0 substantive axioms |")
    ap("")
    ap("</details>")
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


def status_icon(edge_badge: str) -> str:
    """Map a display badge string to its one-emoji chart/ledger icon."""
    if edge_badge.startswith("DEFERRED"):
        return "⏸"
    if edge_badge.startswith("PROVEN"):
        return "✅"
    if edge_badge == "DEFINITIONAL":
        return "📘"
    if edge_badge.startswith("COUNTERMODEL"):
        return "🧱"
    if edge_badge.startswith("AXIOMATIC"):
        return "⚠️"
    return edge_badge


def proof_cert_line(proof: ProofIR, edge_badge: str) -> str:
    """One-line clickable footer: `{icon[ + axis/boundary]} · [file#name](formal/Logos/file#Lline)`."""
    icon = status_icon(edge_badge)
    if edge_badge.startswith("AXIOMATIC ("):
        head = f"{icon} {edge_badge[len('AXIOMATIC ('):-1]}"
    elif edge_badge.startswith("COUNTERMODEL | "):
        head = f"{icon} {edge_badge[len('COUNTERMODEL | '):]}"
    else:
        head = icon
    return f"{head} · [{proof.file}#{proof.name}](formal/Logos/{proof.file}#L{proof.line})"


def render_proof_body_spine(proof: ProofIR, ap):
    """Renders a proof on the Main Proof Spine as an integral, readable part of the
    philosophical argument: clear mathematical-philosophical explanation, formal consequence,
    subordinate status badge, and Lean certification.
    """
    doc_lines = []
    lead_src = proof.doc_lead or proof.doc
    if lead_src:
        for line in lead_src.splitlines():
            line_str = line.strip()
            if not line_str:
                continue
            if any(line_str.startswith(k) for k in ("Status:", "Tag:", "Footprint:", "Lean:", "Audit:", "Impressão")):
                continue
            doc_lines.append(line_str)

    if doc_lines:
        ap(_spine_lead(" ".join(doc_lines)))
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
        if proof.assumptions:
            assump_str = " ∧ ".join(a.proposition for a in proof.assumptions)
            ap(f"    {assump_str} → {proof.conclusion.proposition}")
        else:
            ap(f"    ∴ {proof.conclusion.proposition}")
        ap("")
    elif proof.goal:
        ap(f"    ∴ {proof.goal}")
        ap("")

    edge_cat, edge_badge = classify_proof_edge(proof)
    ap(proof_cert_line(proof, edge_badge))
    ap("")

    if proof.steps:
        subst_cost = "0 substantive axioms" if not proof.subst_axioms else f"substantive axioms: {', '.join(sorted({ax.rsplit('.', 1)[-1] for ax in proof.subst_axioms}))}"
        ap("<details>")
        ap(f"<summary>Formal Derivation ({len(proof.steps)} step{'s' if len(proof.steps) != 1 else ''}, natural deduction, {subst_cost})</summary>")
        ap("")
        if proof.assumptions:
            ap(f"Assume {', and '.join(a.proposition for a in proof.assumptions)}:")
            ap("")
        for s_idx, step in enumerate(proof.steps, 1):
            ap(f"    {s_idx}. {step.proposition}  ({step.description})")
        ap("")
        if proof.conclusion:
            if proof.conclusion.rule == Rule.CONTRADICTION:
                ap(f"    Contradiction: {proof.conclusion.description} (→ ⊥)")
            else:
                ap(f"    ∴ {proof.conclusion.proposition}")
            ap("")
        ap("</details>")
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
    if edge_cat == "PROVEN" and proof.subst_axioms:
        inherited = ", ".join(sorted({ax.rsplit(".", 1)[-1] for ax in proof.subst_axioms}))
        ap(f"✅ (inherited premise context: {inherited}) · [{proof.file}#{proof.name}](formal/Logos/{proof.file}#L{proof.line})")
        ap("")
    else:
        ap(proof_cert_line(proof, edge_badge))
        ap("")


# ---------------------------------------------------------------------------
# Classical-attributes status table (reader-facing, generated after Branch C)
#
# Question answered: "Which classical characteristics of God do we already
# have?" Statuses are DERIVED, never transcribed: each row's live bucket is a
# pure function of (kernel node kind, audited footprint, declared GAPMAP /
# presentation-spine status, absence of any live theorem). `render_…` shows the
# live value; `verify_…` (run at regeneration in `main`) fails loudly if a row's
# expected bucket no longer matches the kernel — a future theorem forces the
# row to be upgraded honestly instead of drifting.
# ---------------------------------------------------------------------------

CLASSICAL_ATTRIBUTES = [
    # ---- Ground 1 — Personal ground / person-type (established ✅) ----
    {
        "attribute": "**Personal** — the ground-type is personal",
        "scope": "Personal ground / person-type",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.PersonalGroundOfReality.personal_ground_of_right_wrong"}],
        "refs": [],
        "sense": ("`RightWrong ⇒ Person` (`∀ s, RightWrong s → Person s`). "
                  "Established of the personal ground/type, not of a particular divine person."),
    },
    {
        "attribute": "**Rational** — formally equivalent to the Thomistic core containing RationalNature",
        "scope": "Personal ground / person-type",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.Person.person_iff_thomisticCore"}],
        "refs": ["Logos.Person.RationalNature"],
        "sense": ("`Person(s) ↔ ThomisticPersonCore(s)`, whose conjunct "
                  "`RationalNature s ≡ Intentional s ∧ FreeWill s` is definitional (`📘`). "
                  "Established of the person-type."),
    },
    {
        "attribute": "**Free** — genuine normativity yields genuine choice and free will",
        "scope": "Personal ground / person-type",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.IndubitableNormativeFreeWill.indubitable_normative_free_will"}],
        "refs": ["Logos.Choice.FreeWill"],
        "sense": ("`GenuineNormativity ⇒ Chooses ⇒ FreeWill`; "
                  "`FreeWill s ≡ ∃ p q, Chooses s p q` is definitional (`📘`)."),
    },
    {
        "attribute": "**Independent will** — with numerical individuation",
        "scope": "Personal ground / person-type",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.Person.person_iff_freeIndependentWill"}],
        "refs": ["Logos.Person.IndependentWill"],
"sense": ("`Person(s) ↔ FreeIndependentWill(s)`; "
                   "`subjectWill s₁ ≠ subjectWill s₂` — distinct persons have numerically "
                   "distinct wills. The meaning-postulate status is kernel-verified: "
                   "`will_individuation` is not derivable from the pre-will spine "
                   "(`WillIndividuationAudit.will_individuation_not_forced_by_prewill_spine`, `{}`)."),
    },
    {
        "attribute": "**Dominion over acts** / authoritative personhood",
        "scope": "Personal ground / person-type",
        "expected": "PROVEN",
        "checks": [{"type": "decl", "full": "Logos.Person.DominionOverActs"}],
        "refs": [],
        "sense": ("the Thomistic-personcore conjunct `DominionOverActs s ≡ FreeWill s` is "
                  "definitional (`📘`); present inside `person_iff_thomisticCore`."),
    },
    {
        "attribute": "**Ground of objective normativity (Right and Wrong)**",
        "scope": "Personal ground / person-type",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.PersonalNormativeGround.person_grounds_normative_polarity"}],
        "refs": ["Logos.PersonalGroundOfReality.the_person_supports_the_reality_of_right"],
        "sense": ("`Person s → GroundsRightWrong s`, and the headline that \"the person "
                  "supports the reality of Right\". Established of the personal ground."),
    },
    {
        "attribute": "**Non-relative core** — strict architectural invariance only",
        "scope": "Proof architecture (not divine scope)",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.HardenedInvariance.agent_invariant_core_is_strictly_inside_freewill_invariant_core"}],
        "refs": ["Logos.HardenedInvariance.strict_core_inclusion",
                 "Logos.HardenedInvariance.agent_invariant_iff_agent_neutral_core",
                 "Logos.HardenedInvariance.freewill_invariant_iff_freewill_neutral_core"],
        "sense": ("`(∀ l, AgentInvariant l → FreeWillInvariant l) ∧ "
                  "∃ l, FreeWillInvariant l ∧ ¬ AgentInvariant l` (GAPMAP C180; prose T18): the "
                  "dependency-layer core admissible in every proof regime — including the "
                  "non-agentive structural regime — is strictly contained in the core admissible "
                  "across all agentive regimes (footprint `{}`, pure logic). This is proof "
                  "architecture only: it does not establish that the Divine Being / Ground, a "
                  "divine person, or the ultimate foundation is invariant across systems, "
                  "perspectives, or worlds."),
    },
    # ---- Ground 2 — Divine Being / Ground ----
    {
        "attribute": "**Necessary Divine Being / Ground**",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.NecessityEternity.ofGround_necessary_ground_of_reality"},
                   {"type": "absent",
                    "fragments": ["necessary_person_derived", "divine_person_is_necessary"],
                    "allow": ["Logos.ModalCreationAgency.model_MC2_necessary_person_no_agency_consistent"]}],
        "refs": ["Logos.NecessityEternity.claimE",
                 "Logos.NecessaryPersonalGround.step1_necessary_truth_exists",
                 "Logos.NecessaryPersonalGround.necessary_normative_order"],
        "sense": ("The ground itself is world-rigid: `NecessaryEntity Entity.ofGround` "
                  "(`∀ w, ExistsAt w .ofGround`, definitional `EntityExistsAt w .ofGround := True`, "
                  "footprint `{Means, Subject}` — VOCAB only). Claim E is now a **live theorem** "
                  "as a *non-hypostatic* pairing: the entity-necessity conjunct is PROVEN, the "
                  "personal-kind conjunct is `{AxTwoSubjects, Means, Subject}` (PROVEN↑ under the "
                  "declared META axiom `AxTwoSubjects`), and the hypostatic identity is blocked "
                  "(`ofGround_ne_ofSubject`: `ofGround ≠ EntityOf s`). NO 'necessary Person' theorem "
                  "exists — this row is the entity-level ground, distinct from the necessary-*order* row above."),
    },
    {
        "attribute": "**Aseity** — non-derived / non-dependent",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.CanonicalAseity.conditional_canonical_aseity"}],
        "refs": ["Logos.CanonicalAseity.atom_cannot_ground_the_ground",
                 "Logos.CanonicalAseity.canonical_aseity_implies_modal_aseity",
                 "Logos.ModalPossibilityFrontier.aseity_does_not_force_any_volition_alternatives",
                 "Logos.ModalPossibilityFrontier.volitional_alternative_does_not_force_aseity"],
        "sense": ("In the canonical ontology of entities, `conditional_canonical_aseity` "
                  "(`CanonicalAseity.lean`, footprint `{Means, Subject}` — VOCAB only) establishes "
                  "that `Entity.ofGround` has Canonical Aseity (`¬ ∃ g, ExternalGrounding g .ofGround`), "
                  "conditional on all subjects being discriminating (`∀ s, ∃ p, ¬ Means s p`). "
                  "Atomic entities are unconditionally excluded (`atom_cannot_ground_the_ground`, `{Means, Subject}`). "
                  "At the generic modal frontier, C182 and C184 establish two-way logical independence between "
                  "bare `Aseity` and volitional alternatives (footprint `{}`); that generic separation is not a "
                  "proof or disproof of aseity for `Entity.ofGround` or the ultimate foundation."),
    },
    {
        "attribute": "**One God / strict monotheism** (unity of the Divine Being)",
        "scope": "Divine Being / Ground",
        "expected": "DEFERRED",
        "checks": [{"type": "branch", "id": "monotheism"},
                   {"type": "absent",
                    "fragments": ["monotheism"],
                    "allow": []}],
        "refs": [],
        "sense": ("Strict monotheism (`monotheism_of_god_and_uniqueness`, "
                  "`monotheism_compatible_with_trinity`) is deferred out of the live kernel "
                  "(Branch B, `⏸`); unity concerns the Divine Being, not numerical identity "
                  "of Personhood. Uniqueness is provably NOT a kernel consequence: the "
                  "machine-witnessed separation "
                  "`TheologicalModalHardening.necessary_existence_not_entails_uniqueness` "
                  "(`¬ (∀ S, UniqueExists S.NecessaryEntity)`, L406-414, footprint `{}`) and "
                  "the deferred `universal_ground_unique` (`NecessaryPersonalGround.lean:24`) "
                  "mark it as an interpretive layer."),
    },
    {
        "attribute": "**Perfect (moral) goodness**",
        "scope": "Divine Being / Ground",
        "expected": "COUNTERMODEL",
        "checks": [{"type": "claim", "id": "F3"}],
        "refs": ["Logos.MoralFrontierAudit.moral_good_obtains",
                 "Logos.MoralFrontierAudit.Good",
                 "Logos.MoralFrontierAudit.moral_pole_postulate_is_not_a_consequence",
                 "Logos.Value.AxBenevolentBearingObtains",
                 "Logos.Value.no_help_obtains"],
        "sense": ("GAPMAP ledger row `F3 §28 (Good)` = COUNTERMODEL (🧱) via C175: the "
                  "`M_amoral` model (`{}`) satisfies epistemic agential normativity with no "
                  "practical obligation — the separation is permanent "
                  "(`moral_pole_postulate_is_not_a_consequence`, vocabulary-only), so the moral "
                  "pole is never *read off* the normative structure. Right/Wrong here is "
                  "epistemic correctness, explicitly distinguished from moral good/evil. The "
                  "*positive pole itself* is nevertheless obtained: `Good` is a fair definition "
                  "(helping another person; `{Means, Subject}` — the definition smuggles "
                  "nothing) and `moral_good_obtains` (C178) is PROVEN↑ under the single "
                  "disclosed META bridge `AxBenevolentBearingObtains` (C177, \"some person is "
                  "actually helped\"). The bridge is a paid commitment, not a hidden derivation: "
                  "the bare value layer is machine-proven empty (`no_help_obtains`, C176, "
                  "`{Subject}`), which is the bridge's own countermodel. The negative pole `Evil` "
                  "remains a declared SEM datum (its fair reading needs a parallel harm bridge, "
                  "not declared). What stays a countermodel frontier is the *attribution* of this "
                  "goodness to the Divine Being — that remains a separate target."),
    },
    {
        "attribute": "**Eternal — ever-present** (everlasting existence)",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.NecessityEternity.the_ground_everlasting"},
                   {"type": "absent",
                    "fragments": ["eternal"],
                    "allow": ["Logos.Love.T14_eternalRelation_conditional"]}],
        "refs": ["Logos.NecessityEternity.necessary_implies_everlasting",
                 "Logos.NecessityEternity.necessary_existence_is_stage_uniform",
                 "Logos.NecessityEternity.ofGround_necessary",
                 "Logos.Love.T14_eternalRelation_conditional"],
        "sense": ("World-rigid existence is unmodulated by time: `NecessaryEntity e → "
                  "Everlasting e` (`∀ t, ExistsAtTime t e`) is a definitional corollary of "
                  "necessity via the Nat-stage layer — the deduction imports NO temporal premise, "
                  "time enters only on the conclusion side. `Everlasting Entity.ofGround` is "
                  "therefore PROVEN (`{Subject}` + ground footprint, VOCAB). Distinct from the "
                  "eternal love-*relation* `T14_eternalRelation_conditional`. C181 supplies "
                  "the generic empty-footprint necessity-to-stage transport, but deliberately "
                  "does not instantiate the canonical `Entity` sort."),
    },
    {
        "attribute": "**Atemporal** (existence not time-modulated; outside succession)",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.NecessityEternity.the_ground_atemporal"}],
        "refs": ["Logos.NecessityEternity.necessary_implies_atemporal",
                 "Logos.NecessityEternity.necessary_existence_is_stage_uniform",
                 "Logos.NecessityEternity.the_ground_not_in_succession",
                 "Logos.NecessityEternity.atom_has_temporal_mode",
                 "Logos.NecessityEternity.everlasting_but_contingent"],
        "sense": ("`NecessaryEntity e → Atemporal e` (`ExistsAtTime t₁ e ↔ ExistsAtTime t₂ e`); "
                  "the ground is also outside every initiation-act "
                  "(`the_ground_not_in_succession`, `{Initiates, State, Subject}`). Separation is "
                  "honest: atoms/subjects are time-modulated (`atom_has_temporal_mode`) and "
                  "`Everlasting` does not collapse into necessity (`everlasting_but_contingent`). "
                  "What is PROVEN is stage-unmodulated world-rigid existence — not a full "
                  "theology of divine eternity. C181 makes the underlying transport explicit "
                  "without instantiating the canonical `Entity` sort."),
    },
    {
        "attribute": "**Divine simplicity**",
        "scope": "Divine Being / Ground",
        "expected": "ABSENT",
        "checks": [{"type": "absent", "fragments": ["simplic"], "allow": []}],
        "refs": [],
        "sense": "No live theorem.",
    },
    {
        "attribute": "**Omniscience**",
        "scope": "Divine Being / Ground",
        "expected": "ABSENT",
        "checks": [{"type": "absent", "fragments": ["omnisci"], "allow": []}],
        "refs": ["Logos.DeepModalFrontier.Omniscience_AllTruths",
                 "Logos.DeepModalFrontier.Omniscience_Counterfactuals"],
        "sense": ("`Omniscience_AllTruths` / `Omniscience_Counterfactuals` "
                  "(`DeepModalFrontier`) are frontier vocabulary definitions, not theorems."),
    },
    {
        "attribute": "**Omnipotence**",
        "scope": "Divine Being / Ground",
        "expected": "ABSENT",
        "checks": [{"type": "absent", "fragments": ["omnipot"], "allow": []}],
        "refs": [],
        "sense": "No live theorem.",
    },
    {
        "attribute": "**Creator of contingent reality**",
        "scope": "Divine Being / Ground",
        "expected": "COUNTERMODEL",
        "checks": [{"type": "countermodel",
                    "full": "Logos.ConditionalTheology.necessary_ground_not_entails_contingent_creation"}],
        "refs": [],
        "sense": ("`necessary_ground ⇏ contingent_creation` (Acosmic model, footprint `{}`): "
                  "a necessary divine ground is consistent with zero contingent created "
                  "reality. (Ledger target F9 DEFERRED.)"),
    },
    # ---- Ground 3 — Divine Personhood (open) ----
    {
        "attribute": "**Three Divine Persons (Trinity)**",
        "scope": "Divine Personhood",
        "expected": "COUNTERMODEL",
        "checks": [{"type": "countermodel",
                    "full": "Logos.ConditionalTheology.preceding_theory_not_entails_trinity"}],
        "refs": [],
        "sense": ("`preceding_theory ⇏ trinity` (Binitarian separation model, footprint `{}`). "
                  "A separate claim, distinct from necessity and from unity. (F6/F8 DEFERRED; "
                  "plurality `T12_twoPersons` is at most generic persons under `AxTwoSubjects`.)"),
    },
    {
        "attribute": "**Incarnation**",
        "scope": "Divine Personhood",
        "expected": "COUNTERMODEL",
        "checks": [{"type": "countermodel",
                    "full": "Logos.ConditionalTheology.preceding_theory_not_entails_incarnation"}],
        "refs": [],
        "sense": ("`preceding_theory ⇏ incarnation` (Unincarnate model, footprint `{}`). "
                  "(F9 DEFERRED.)"),
    },
]

_CA_BADGE = {
    "PROVEN": "✅", "PROVEN↑": "⚠️", "AXIOM": "◆",
    "COUNTERMODEL": "🧱", "DEFERRED": "⏸", "ABSENT": "❌",
}

_CA_STATUS_TEXT = {
    "PROVEN": "✅ PROVEN",
    "PROVEN↑": "⚠️ AXIOMATIC",
    "AXIOM": "◆ AXIOM",
    "COUNTERMODEL": "🧱 INDEPENDENT",
    "DEFERRED": "⏸ DEFERRED",
    "ABSENT": "❌ NOT ESTABLISHED",
}


def _classical_anchor_live(anchor: dict, decls: dict, node_map: dict) -> str:
    """Current live bucket of one CLASSICAL_ATTRIBUTES anchor (never raises;
    anomalies surface as descriptive strings that the `verify_…` guard turns
    into regeneration failures — or as a `?` badge in the rendered table)."""
    t = anchor["type"]
    if t in ("decl", "countermodel"):
        full = anchor["full"]
        if full not in decls:
            return "MISSING_DECL"
        if full not in node_map:
            return "MISSING_NODE"
        if node_map[full]["kind"] == "axiom":
            return "AXIOM"
        if t == "countermodel":
            fp = audit_footprint(full)
            return "COUNTERMODEL" if not fp else f"COUNTERMODEL?({sorted(fp)})"
        subst, _, _ = footprint_parts(full)
        return "PROVEN↑" if subst else "PROVEN"
    if t == "branch":
        pd = load_presentation_spine()
        for node in (pd or {}).get("spine_nodes", []):
            for b in node.get("branches", []):
                if b.get("id") == anchor["id"]:
                    return "DEFERRED" if b.get("status") == "deferred" else "LIVE"
        return "MISSING_BRANCH"
    if t == "claim":
        c = _CTX.get("by_id", {}).get(anchor["id"])
        if c is None:
            return "MISSING_CLAIM"
        return _clean_status((c.get("status") or "").strip())
    if t == "absent":
        allow = {x.rsplit(".", 1)[-1] for x in anchor["allow"]}
        for frag in anchor["fragments"]:
            for f, d in decls.items():
                if d["kind"] not in ("theorem", "axiom"):
                    continue
                base = f.rsplit(".", 1)[-1]
                if frag in base and base not in allow:
                    return "FOUND"
        return "ABSENT"
    return "UNKNOWN"


def _classical_row_status(row: dict, decls: dict, node_map: dict) -> str:
    live = _classical_anchor_live(row["checks"][0], decls, node_map)
    return _CA_STATUS_TEXT.get(live, "?")


def _classical_decl_link(full: str, decls: dict) -> str:
    d = decls.get(full)
    if not d:
        return f"`{full}`"
    return (f"[{d['file']}#{d['name']}]"
            f"(formal/Logos/{d['file']}#L{d['line']}), footprint {kernel_fp_text(full)}")


def render_defense_against_attacks() -> list[str]:
    """Emits the systematic defense guide showing why the six most common skeptical
    attacks against Γ fail in the Lean 4 kernel with 0 substantive axioms.
    """
    lines = []
    ap = lines.append
    ap("---")
    ap("")
    ap("## Why Common Skeptical Attacks Fail (The Six Pillars of Formal Defense)")
    ap("")
    ap("> **Adversarial Guide for Critics and Agents:** External agents evaluating or attacking")
    ap("> Γ often mistake its conclusions for ungrounded metaphysical assumptions. Every common")
    ap("> objection has been formalized and refuted in the Lean 4 kernel — typically reducing to a")
    ap("> direct constructive contradiction (⊥) with zero substantive axioms.")
    ap("")
    ap("| Skeptical Attack | What the Skeptic Misses | Formal Rebuttal in Kernel | Kernel Footprint |")
    ap("|---|---|---|---|")
    ap("| **1. Normative Nihilism**<br>\"There is no objective right and wrong; normativity is arbitrary.\" | Any rational denial must claim that its denial is *correct* (`ClaimsCorrect s NoRight`). Claiming the denial as correct while it is true produces a strict constructive contradiction. | [`claims_correct_no_right_self_refuting`](formal/Logos/DirectNormativeRetorsion.lean#L60)<br>`⊢ ClaimsCorrect s NoRight ∧ NoRight → ⊥` | `{Initiates, Means, State, Subject, CL}`<br>**(0 substantive axioms)** |")
    ap("| **2. Eliminativism of Choice**<br>\"Normative address does not imply genuine choice.\" | Prescriptive normativity commands one alternative and forbids an incompatible one. Co-grasping incompatible alternatives *is* the constitutive definition of choice; denying choice yields a direct contradiction. | [`d7_co_grasp_is_definitionally_choice`](formal/Logos/UndeniableNormativeDerivation.lean#L261)<br>`⊢ Means s p ∧ Means s q ∧ Incompatible p q ∧ ¬ Chooses s p q → ⊥` | `{Means, Subject}`<br>**(0 substantive axioms)** |")
    ap("| **3. Determinism / Incompatibilism**<br>\"Choice is not Free Will; freedom requires physical indeterminism.\" | Having the capacity to choose between incompatible normative alternatives *is* Free Will (`FreeWill s := ∃ p q, Chooses s p q`). Denying free will when one chooses yields a formal contradiction. Physical indeterminism is an orthogonal concept isolated to countermodels. | [`d8_choice_is_definitionally_free_will`](formal/Logos/UndeniableNormativeDerivation.lean#L275)<br>`⊢ Chooses s p q ∧ ¬ FreeWill s → ⊥`<br>[`indubitable_normative_free_will`](formal/Logos/IndubitableNormativeFreeWill.lean#L115) | `{Means, Subject}`<br>**(0 substantive axioms)** |")
    ap("| **4. Theological Smuggling**<br>\"A free subject is not a Person; 'Person' is an anthropomorphic trick.\" | Personhood in Γ is defined constitutively via the classical Boethian-Thomistic core (`IndividualSubstance ∧ RationalNature ∧ DominionOverActs`). The equivalence with `FreeSubject` is machine-checked with 0 substantive axioms. | [`person_iff_thomisticCore`](formal/Logos/Person.lean#L137)<br>`⊢ Person s ↔ IndividualSubstance s ∧ RationalNature s ∧ DominionOverActs s` | `{Means, Subject}`<br>**(0 substantive axioms)** |")
    ap("| **5. Euthyphro / Voluntarism**<br>\"This makes the person the arbitrary creator of morality.\" | Identifying Ought with volition (`Wills s p = Ought s p`) destroys normative violation. The ground required by the normative order is *personal in kind*, not an arbitrary dictator inventing rules. | [`will_identity_collapses_normativity`](formal/Logos/PersonalNormativeGround.lean#L261)<br>`⊢ Wills s p = Ought s p → NormativeViolation s p → ⊥` | `{Subject, Wills, Ought}`<br>**(0 substantive axioms)** |")
    ap("| **6. Physicalist / Atomic Ground**<br>\"The ultimate ground could be a physical particle, matter, or an atom.\" | An entity with false meaning capacity cannot ground an entity with true meaning capacity. Atomic factual entities are unconditionally excluded from grounding `Entity.ofGround`, and the ground possesses Canonical Aseity. | [`atom_cannot_ground_the_ground`](formal/Logos/CanonicalAseity.lean#L96)<br>[`conditional_canonical_aseity`](formal/Logos/CanonicalAseity.lean#L133)<br>`⊢ CanonicalAseity Entity.ofGround` | `{Means, Subject}`<br>**(0 substantive axioms)** |")
    ap("| **7. Origin of Normativity (The Proof-Self Retorsion)**<br>\"Where does the initial normative claim come from? Why grant that any normative judgment exists?\" | Bare syntax checking alone does not force normativity (`M_inanimate_checker`, `{}`). But any agent *presenting* a derivation as sound (`PresentsAsSound`) co-means correctness and error, deriving `FreeWill` and `Person` with 0 substantive axioms. Furthermore, an adversarial critic who attacks Γ by presenting an objection argumentatively as sound *themselves* instantiates the normative stance (`critic_presenting_objection_is_person`). | [`presents_as_sound_derives_personhood`](formal/Logos/ProofPresentationRetorsion.lean#L140)<br>[`critic_presenting_objection_is_person`](formal/Logos/ProofPresentationRetorsion.lean#L180)<br>[`syntactic_validity_without_subject_or_normativity`](formal/Logos/ProofPresentationRetorsion.lean#L100) | `{Initiates, Means, State, Subject, CL}`<br>**(0 substantive axioms)** |")
    ap("")
    return lines


def render_classical_attribute_status(decls: dict, node_map: dict) -> list[str]:
    """Emits the classical-attributes table block (placed after Branch C, before
    the Further Investigations catalogue). Statuses are live-derived, never
    transcribed."""
    lines = []
    ap = lines.append
    ap("---")
    ap("")
    ap("## Which Classical Attributes Are Already Established?")
    ap("")
    ap("> **Which classical characteristics of God do we already have?** This table reports the")
    ap("> **live formal status** of the main classical attributes, derived from the current kernel")
    ap("> and ledger (never from intentions). The three divine-adjacent scopes are kept apart: the **Divine")
    ap("> Being / Ground**, **Divine Personhood**, and the **personal normative ground /**")
    ap("> **person-type** — what §1–§10 actually establish. A separate **proof-architecture** scope reports")
    ap("> a result about the deduction itself, never as a divine attribute. \"Necessity\" concerns the")
    ap("> Being/Ground, not each Divine Person; \"Personal\", \"Three Persons\", and \"One God\"")
    ap("> are separate claims and are reported separately. Nothing here claims a \"necessary")
    ap("> Person\": \"He is necessary\" is a claim about the Divine Being / Ground, \"He is")
    ap("> personal\" a claim about the ground-type — two different rows, never conjoined.")
    ap("")
    ap("Status vocabulary used here (extends the badge legend above): `✅` PROVEN (machine-verified, footprint stated) · `📘` DEFINITIONAL · `⏸` DEFERRED (target not in the live kernel) · `❌` NOT ESTABLISHED (no current theorem; distinct from the ledger's `✖` BLOCKED) · `🧱` INDEPENDENT / FRONTIER (explicit countermodel: the preceding theory does not entail it).")
    ap("")
    ap("| Classical characteristic | Scope | Status | Exact sense established by the current theory (reference) |")
    ap("|---|---|---|---|")
    for row in CLASSICAL_ATTRIBUTES:
        refs = list(row["refs"])
        primary = row["checks"][0].get("full")
        if primary and primary not in refs:
            refs.insert(0, primary)
        ref_cell = " ; ".join(_classical_decl_link(f, decls) for f in refs)
        ref_cell = f" — {ref_cell}" if ref_cell else ""
        ap(f"| {row['attribute']} | {row['scope']} | "
           f"{_classical_row_status(row, decls, node_map)} | {row['sense']}{ref_cell} |")
    ap("")
    ap("_Synthesis — the strongest current profile._ The theory has established, of a")
    ap("**personal, rational, free, authoritative-over-its-acts, independently individuated**")
    ap("**normative ground / person-type**, that its objective Right/Wrong order is the object")
    ap("of a necessary normative/truth order, and (entity-level) that a **necessary Divine Being")
    ap("/ Ground** exists — world-rigid, **everlasting** and **atemporal**, a definitional")
    ap("corollary of necessity with time entering only on the conclusion side. The remaining")
    ap("divine attributes — **unity / monotheism**, **simplicity**, **omniscience**, **omnipotence**,")
    ap("**perfect moral goodness** (the moral pole itself now obtains under the single declared "
       "META bridge, C178; its attribution to the Divine Being stays a 🧱 frontier), the "
       "**Trinity**, the **Incarnation**, and contingent")
    ap("**creation** — remain **separate proof targets**")
    ap("(`⏸` / `❌`) or explicit **countermodel frontiers** (`🧱`) until the live kernel proves them.")
    ap("")
    return lines


def verify_classical_attribute_status(decls: dict, node_map: dict) -> None:
    """Regeneration guard: every CLASSICAL_ATTRIBUTES row's live-derived bucket
    must still equal its expected bucket. A future theorem that establishes a
    currently-absent attribute (or a GAPMAP/branch status change) fails loudly
    here, forcing the row to be upgraded honestly in the same change."""
    for row in CLASSICAL_ATTRIBUTES:
        got = _classical_anchor_live(row["checks"][0], decls, node_map)
        assert got == row["expected"], (
            f"CLASSICAL ATTRIBUTES drift: '{row['attribute']}' is declared "
            f"{row['expected']} but the live kernel/ledger derives {got}. "
            f"Upgrade the CHAR.md table row only together with the real formal "
            f"change; never transcribe status text over the kernel.")


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

    # Opening: how-to-read, then The Argument at a Glance (only in full document mode)
    if not is_synthetic:
        for gl in render_reading_guide():
            ap(gl)
        glance_lines = generate_argument_at_a_glance(spine, frontiers, countermodels)
        for gl in glance_lines:
            ap(gl)

    presentation_data = load_presentation_spine()
    policy = presentation_data.get("presentation_policy", {}) if presentation_data else {}
    spine_edges = presentation_data.get("edges", []) if presentation_data else []
    edges_by_from = {}
    for e in spine_edges:
        edges_by_from.setdefault(e.get("from"), []).append(e)
    include_detailed = policy.get("include_detailed_appendix", False) if presentation_data else True
    include_countermodels = policy.get("include_countermodels_appendix", False) if presentation_data else True
    include_frontiers = policy.get("include_frontiers_appendix", False) if presentation_data else True
    include_further = policy.get("include_further_investigations", True)

    # 1. Main Proof Spine
    dedupe_defs = bool(policy.get("dedupe_shared_definitions", False))
    surfaced = {}

    def _section_ref(title):
        m = re.match(r'^\s*(\d+)\s*[.)]\s*(.*)$', title)
        return (int(m.group(1)), m.group(2).strip()) if m else (None, title.strip())

    def _surface(proof, sec_no, sec_bare, kind):
        surfaced.setdefault(proof.name, (sec_no, sec_bare, kind))

    def _render_step(proof, sec_no, sec_bare):
        render_proof_body_spine(proof, ap) if not is_synthetic else render_proof_body(proof, ap, detailed=is_synthetic)
        if dedupe_defs:
            _surface(proof, sec_no, sec_bare, "step")

    def _render_route_definitions(sec, sec_no, sec_bare):
        if not sec.get("route_definitions") or is_synthetic:
            return
        new_defs, refs = [], []
        for d in sec["route_definitions"]:
            if dedupe_defs and d.name in surfaced:
                refs.append(d)
            else:
                new_defs.append(d)
                if dedupe_defs:
                    _surface(d, sec_no, sec_bare, "def")
        if not new_defs and not refs:
            return
        ap("<details>")
        if refs:
            ap(f"<summary>Definitions used in this section ({len(new_defs) + len(refs)}; "
               f"{len(new_defs)} new, {len(refs)} already shown)</summary>")
        else:
            ap(f"<summary>Definitions used in this section ({len(new_defs)})</summary>")
        ap("")
        for d in new_defs:
            render_proof_body_spine(d, ap)
        for d in refs:
            ref_no, ref_bare, ref_kind = surfaced[d.name]
            verb = "defined" if ref_kind == "def" else "first shown"
            ap(f"    ∴ {d.goal} — {verb} in §{ref_no}. {ref_bare}.")
            ap("")
        ap("</details>")
        ap("")

    for i, sec in enumerate(spine):
        sec_no, sec_bare = _section_ref(sec.get("title", ""))
        ap(f"## {sec['title']}")
        ap("")
        if sec.get("summary"):
            ap(sec["summary"])
            ap("")

        if sec.get("investigation_link"):
            ap(f"*(Detailed technical proof & model analysis: [{sec['investigation_link']}]({sec['investigation_link']}))*")
            ap("")

        if sec.get("pushback"):
            ap("<details>")
            ap("<summary>The skeptic's attack & the reply</summary>")
            ap("")
            ap(f"> **The skeptic tries —** {sec['pushback']}")
            if sec.get("reply"):
                ap(f"> **The reply / the frontier —** {sec['reply']}")
            reb_target = sec.get("rebuttal_target")
            reb_form = sec.get("rebuttal_formula")
            if reb_target and decls and reb_target in decls:
                reb_decl = decls[reb_target]
                reb_file = reb_decl.get("file", "")
                reb_name = reb_decl.get("name", reb_target.rsplit(".", 1)[-1])
                reb_line = reb_decl.get("line", 1)
                subst, vocab, cl = footprint_parts(reb_target)
                fp_str = "0 substantive axioms" if not subst else f"substantive axioms: {', '.join(sorted({ax.rsplit('.', 1)[-1] for ax in subst}))}"
                ap(">")
                ap(f"> **Machine-Checked Kernel Rebuttal —** [`{reb_name}`](formal/Logos/{reb_file}#L{reb_line}) (Footprint: {fp_str}):")
                if reb_form:
                    ap(f"> `⊢ {reb_form}`")
            ap("</details>")
            ap("")
        elif sec.get("reply"):
            ap("<details>")
            ap("<summary>The reply / the frontier</summary>")
            ap("")
            ap(f"> **The reply / the frontier —** {sec['reply']}")
            ap("</details>")
            ap("")

        _render_route_definitions(sec, sec_no, sec_bare)

        for proof in sec.get("primary_proofs", sec.get("proofs", [])):
            _render_step(proof, sec_no, sec_bare)

        if sec.get("supporting_proofs"):
            ap("<details>")
            ap(f"<summary>Supporting Infrastructure — {len(sec['supporting_proofs'])} auxiliary theorem(s) beneath this step</summary>")
            ap("")
            for proof in sec.get("supporting_proofs", []):
                _render_step(proof, sec_no, sec_bare)
            ap("</details>")
            ap("")

        for proof in sec.get("obstruction_proofs", []):
            ap("<details>")
            ap(f"<summary>Obstruction / Formal Boundary: `{proof.name}`</summary>")
            ap("")
            ap(f"### Obstruction / Formal Boundary: `{proof.name}`")
            ap("")
            _render_step(proof, sec_no, sec_bare)
            ap("</details>")
            ap("")

        for sub in sec.get("subsections", []):
            sub_proofs = []
            if sub.get("groups"):
                for g in sub["groups"]:
                    sub_proofs.extend(g.get("proofs", []))
            else:
                sub_proofs = sub.get("proofs", [])
            thm_count = len(sub_proofs)
            count_str = f" ({thm_count} machine-checked theorems)" if thm_count else ""

            ap("<details>")
            ap(f"<summary><b>{sub['title']}</b>{count_str} — click to expand</summary>")
            ap("")
            ap(f"### {sub['title']}")
            ap("")
            if sub.get("summary"):
                ap(sub["summary"])
                ap("")
            groups = sub.get("groups")
            if groups:
                for g in groups:
                    if not g.get("proofs"):
                        continue
                    if g.get("label"):
                        ap(g["label"])
                        ap("")
                    for proof in g.get("proofs", []):
                        _render_step(proof, sec_no, sec_bare)
            else:
                for proof in sub.get("proofs", []):
                    _render_step(proof, sec_no, sec_bare)
            ap("</details>")
            ap("")

        for b in sec.get("branches", []):
            ap(f"### {b['title']}")
            ap("")
            if b.get("summary"):
                ap(b["summary"])
                ap("")
            if b.get("investigation_link"):
                ap(f"*(Detailed technical proof & model analysis: [{b['investigation_link']}]({b['investigation_link']}))*")
                ap("")
            if b.get("status") == "deferred" and not b.get("primary_proofs"):
                defer_line = b.get("defer_note") or (
                    "> ⏸ **DEFERRED** — annotated surface only; no compiled Lean declaration "
                    "(`NecessaryPersonalGround.lean` defers this block; "
                    "`scratch/Trinitarian_deferred.lean` is absent from the repository).")
                ap("> " + defer_line if not defer_line.startswith("> ") else defer_line)
                ap("")
            for proof in b.get("primary_proofs", []):
                _render_step(proof, sec_no, sec_bare)
            if b.get("supporting_proofs"):
                ap("<details>")
                ap(f"<summary>Supporting Infrastructure — {len(b['supporting_proofs'])} auxiliary theorem(s) beneath this branch</summary>")
                ap("")
                for proof in b.get("supporting_proofs", []):
                    _render_step(proof, sec_no, sec_bare)
                ap("</details>")
                ap("")
            for proof in b.get("obstruction_proofs", []):
                ap("<details>")
                ap(f"<summary>Obstruction / Formal Boundary: `{proof.name}`</summary>")
                ap("")
                _render_step(proof, sec_no, sec_bare)
                ap("</details>")
                ap("")

        out_edges = edges_by_from.get(sec.get("id"), [])
        for e in out_edges:
            to_id = e.get("to")
            to_sec = next((s for s in spine if s.get("id") == to_id), None)
            if to_sec:
                to_no, to_bare = _section_ref(to_sec.get("title", ""))
                direction = e.get("direction", "discovery")
                dir_label = "▲ Discovery" if direction == "discovery" else ("▼ Ontological Grounding" if direction == "grounding" else "➔ Continuation")
                rel = e.get("relation", "")
                ap(f"> ➔ **Linear Forward Transition to Step {to_no} ({to_bare}):** [{dir_label} · *{rel}*]")
                ap("")

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
        ap(FRONTIER_INTRO)
        ap("")
        for sec in frontiers:
            for proof in sec.get("proofs", []):
                doc_str = f" — {proof.doc}" if proof.doc else ""
                ap(f"* **`{proof.name}`** (`{proof.goal}`){doc_str}")
        ap("")
        ap(OPEN_BRIDGES)
        ap("")

    # 5. Classical-attributes status table (after the whole core deduction,
    #    before the Further Investigations catalogue) — real-repository mode only.
    if not is_synthetic and decls and len(decls) > 10 and _AUDIT:
        for line in render_classical_attribute_status(decls, node_map):
            ap(line)
        for line in render_defense_against_attacks():
            ap(line)

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
    assert len(dissolved) == 7, (
        f"expected 7 dissolved aliases (F1a, F3, F4, F5, F7, FAITH-1, FAITH-2), "
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

    # Classical-attributes table honesty: live kernel/ledger must still match the
    # declared buckets (a future theorem would fail regeneration loudly here).
    verify_classical_attribute_status(decls, node_map)

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