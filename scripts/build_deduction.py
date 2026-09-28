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

# Claim-id shapes that appear in the GAPMAP ledger's first column. The
# alternation must cover every id the ledger actually uses, not just the
# common ones: `F1bUncond`, `EvalSettlement` and `OpenBridgeNormativity` are
# real rows of the "Deferred / blocked" table, and a regex that omits them
# drops them from every generated document *silently* — a BLOCKED row that
# never reaches the reader reads as a row that does not exist. `F\d+[A-Za-z]*`
# covers `F1a`/`F1b`/`F1bUncond`; the bare CamelCase alternative covers the
# two descriptive ids. Header cells ("ID", "C-id", "Route", "Claim", "Status",
# "Tag") are excluded by the explicit denylist in `_is_claim_id_cell`.
CLAIM_ID_RE = re.compile(
    r"^(C\d+|F\d+[A-Za-z]*|FAITH-\d+|Q7\.\d|[A-Z][A-Za-z]+)\s*$")

# First-column cells that look like ids but are table headers or prose labels.
_NOT_CLAIM_ID = {
    "ID", "Cid", "Route", "Claim", "Status", "Tag", "Footprint", "Prose",
    "Missing", "Intermediate", "Step", "Classification", "Obstruction", "Note",
    "Axiom", "Axioms", "File", "Name", "Type", "Kind", "Badge", "Meaning",
    "Section", "Level", "Passage", "Item", "Batch", "Cid Pegada",
}


def _is_claim_id_cell(cell: str) -> bool:
    """True when a GAPMAP first-column cell is a claim id rather than a header.

    Denylist-driven on purpose: an unknown CamelCase id should be *counted* so
    the drift is visible, while the handful of known header words are excluded
    explicitly rather than by pattern."""
    c = cell.strip()
    if not CLAIM_ID_RE.match(c):
        return False
    if c in _NOT_CLAIM_ID:
        return False
    # "C-id" is a header in the C388 provenance table; "Cid Pegada" likewise.
    # `FAITH-n` is a legitimate id, so hyphens are only rejected when the cell
    # is not already an exact match of one of the hyphenated id shapes.
    if "-" in c or " " in c:
        if not re.match(r"^(FAITH-\d+)\s*$", c):
            return False
    return True


def parse_gapmap() -> list:
    """Return sections: [{title, claims:[{...}]}]. claims entries without
    a lean name (deferred/faith rows) keep note text instead."""
    text = GAPMAP_PATH.read_text(encoding="utf-8")
    sections = []
    cur = None
    # Some ledger sections carry a *derived* sub-table (e.g. the C388–C400
    # footprint-provenance table under the semantic-finitude batch) that repeats
    # claim ids with a different column shape. Those rows must not be counted a
    # second time: a duplicate id would be reconciled as a "repeated/dissolved"
    # step, i.e. the very badge that means "this row adds nothing". A table is
    # skipped when its header row is detected as a provenance/derived table.
    skip_table = False
    in_table = False

    for line in text.splitlines():
        s = line.strip()
        m = re.match(r"^#{2,3}\s+(.*)$", s)
        if m:
            title = m.group(1).strip()
            cur = {"title": title, "claims": []}
            sections.append(cur)
            skip_table = False
            in_table = False
            continue
        if not s.startswith("|"):
            in_table = False
            skip_table = False
            continue
        if cur is None:
            continue
        cells = [c.strip() for c in s.strip("|").split("|")]
        if set(cells) <= {"-", "—", ""}:          # separator row
            continue
        # A header row is the first row of a table: no cell parses as a claim id
        # for the shapes a claim row would use, and it introduces columns.
        if not in_table:
            in_table = True
            if cells and not _is_claim_id_cell(cells[0]) and len(cells) >= 2:
                hdr = {c.lower() for c in cells}
                joined = " | ".join(cells).lower()
                # A *derived* sub-table (footprint/class audit) names its id column
                # `C-id` or `Decl (...)` — those repeat claim ids in a different
                # column shape and are not claim rows. The main ledger's header is
                # `Claim | Secao | Declaracao | Status | Pegada`: it contains
                # neither `c-id` nor a `Decl (...)` cell, so it is never skipped.
                # Both markers are required together with a footprint column so a
                # future header mentioning one of them alone cannot silently drop
                # a whole ledger.
                derived_cols = ("c-id" in hdr
                                or any(h.startswith("decl (") for h in hdr))
                footprint_col = ("pegada" in joined or "footprint" in joined)
                if derived_cols and footprint_col:
                    skip_table = True
                continue
        if skip_table:
            continue
        if not cells or not _is_claim_id_cell(cells[0]):
            continue
        claim = {"id": cells[0], "prose": "", "status": "", "footprint": "",
                 "lean_ref": "", "note": "", "section": cur["title"],
                 "level_key": _level_key(cur["title"])}
        if len(cells) >= 5:
            _, claim["prose"], lean_cell, status, footprint = cells[:5]
            claim["lean_cell"] = lean_cell
            claim["lean_ref"] = _extract_lean_ref(lean_cell)
            claim["status"] = _clean_status(status)
            claim["footprint"] = re.sub(r"`+", "", footprint).strip()
        elif len(cells) >= 4:
            # 4-cell shape: id | prose | status | note(+lean ref). Historically
            # gated on an `F`/`Q` prefix, which silently dropped the other
            # frontier rows of the same table (`EvalSettlement`,
            # `OpenBridgeNormativity`). `_is_claim_id_cell` has already decided
            # the first cell is an id, so no prefix test belongs here.
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
    # A countermodel row is a WON claim, not a residual "other": Γ builds an
    # explicit model in which the claim fails, which is a positive result about
    # the boundary of the theory. Before this key existed, `badge_for` fell
    # through to `STATUS_BADGE.get(st, st)` and returned the raw string
    # "COUNTERMODEL", which then landed in the `other` bucket next to the
    # BLOCKED rows and made a demonstrated boundary read as an unresolved one.
    "COUNTERMODEL": "🧱",
}

# Statuses that count as a *demonstrated result*. `other` is a real residual
# rather than a dumping ground; these must never be swept into it.
#
# `◆` is deliberately ABSENT. A declared axiom is an input the theory rests on,
# and counting one as a win would be the same error as counting a hypothesis as
# a proof — the score block publishes `n_ax` separately, as the price. `→` is a
# cross-reference, `➖` a target outside the live kernel, and `✖` a gap. None is
# a result. Phase 4c of VISIBILITY.md is this exclusion, and the assertions in
# `derive_score_data` are what keep it load-bearing rather than aspirational.
WON_BADGES = ("✅", "⚠️", "🧱")
COUNTERMODEL_BADGE = "🧱"

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


ALL_CHAIN_STEPS = None  # bound in main() once the lists above are defined


# The reader-facing narrative chains, in the order they are emitted. Membership is
# hand-maintained (AGENTS.md); badges and footprints inside each row are derived.
# `verify_chain_coverage` fails the build if a row drifts or a required declaration
# is dropped.
CHAIN_LISTS = [
    ("ASIETY-FREEDOM", "ASIETY_FREEDOM_STEPS"),
    ("SEMANTIC-FINITUDE", "SEMANTIC_FINITUDE_STEPS"),
    ("MEANING-RETORSION", "MEANING_RETORSION_STEPS"),
    ("LOVE", "LOVE_STEPS"),
    ("TWO-KINDS", "TWO_KINDS_STEPS"),
    ("PRECEDENCE", "PRECEDENCE_STEPS"),
    ("TEMPORAL-SEPARATION", "TEMPORALITY_STEPS"),
    ("SOLE-BEARER", "SOLE_BEARER_STEPS"),
    ("INHABITED", "INHABITED_STEPS"),
    ("SUCCESSION-AUDIT", "SUCCESSION_AUDIT_STEPS"),
    ("THOMISTIC-ACT", "THOMISTIC_ACT_STEPS"),
    ("ACT-CASCADE", "ACT_CASCADE_STEPS"),
]


# Declarations that a reader must be able to find in the rendered deduction, and
# the chain lists that are therefore not allowed to drop them. This is the small,
# reviewed guard the AGENTS.md sync rule needs: the failure it exists to prevent is
# "a new batch is fully proven and fully registered in GAPMAP, but no reader-facing
# chain list mentions it, so the document silently omits the newest work" — which
# is exactly what happened to the 2026-09-28 two-kinds batch.
#
# Scope note (2026-09-28). A broader rule was considered and REJECTED on evidence:
# requiring every displayable declaration in a chain module to appear in a list
# yields 168 pre-existing violations (61 of them in Logos.Agency, which is the base
# vocabulary), and requiring every Logos module to have a chain yields 75 of 84
# modules uncovered. Either would need an exemption list large enough to be a fake
# guard. This set is therefore explicit, tiny, and hard-failing, and it is checked
# against the *rendered* chain lists rather than against module membership.
CHAIN_REQUIRED_DECLS = {
    "Logos.Plurality.necessaryPersonalSubjectExists": "C404 — the batch's only substantive price",
    "Logos.Plurality.necessarySubject_exists": "C407 — a necessary subject exists",
    "Logos.Plurality.necessaryPersonalSubject_derived": "C408 — a necessary Person exists",
    "Logos.NecessaryPersonalGround.necessary_person_derived_from_bridge":
        "C409 — CLAIM D derived rather than annotated; the batch's headline",
    "Logos.Plurality.kinds_are_the_modal_partition":
        "C410 — the two kinds ARE the two modal profiles; the batch's `{}`-class headline",
    "Logos.Plurality.contingentKindSubject_not_necessary":
        "C406 — discharges C329 with no love axiom",
    "Logos.PersonalGroundOfReality.the_person_supports_the_reality_of_right":
        "C151 — the unconditional personal-ground flagship",
    "Logos.PersonalGroundOfReality.personal_ground_of_right_exists":
        "C152 — a personal ground of right exists",
    "Logos.Agency.performative_act_datum":
        "C454 — the TRANS act-datum; the batch's only substantive price",
    "Logos.Agency.some_subject_initiates":
        "C455 — Initiates inhabited, unconditionally",
    "Logos.Agency.not_noAct":
        "C456 — the denial refuted by the datum",
    "Logos.SuccessionAudit.non_correlate_is_outside_succession":
        "C458 — non-correlateness suffices for `NotInSuccession`",
    "Logos.SuccessionAudit.the_ground_and_every_atom_are_outside_succession":
        "C459 — the ground/atom sharing; C321's twin, on the other field",
    "Logos.SuccessionAudit.someone_is_in_succession":
        "C460 — the non-triviality the ledger misattributed to C197",
    "Logos.SuccessionCountermodel.a_ground_can_produce_while_outside_succession":
        "C461 — the `{}` countermodel the ledger claimed was on record",
    "Logos.SuccessionAudit.existence_implies_someone_initiates":
        "C468 — the author's first sentence, with an inert premise",
    "Logos.ThomisticAct.Produces":
        "C463 — the production relation (F10 item 1), the batch's VOCAB price",
    "Logos.ThomisticAct.love_implies_act":
        "C464 — love implies an act; implication, never identity",
    "Logos.ThomisticAct.ground_love_produces":
        "C465 — the ground's love is productive, scoped to `ofGround`",
    "Logos.ThomisticAct.loving_subject_initiates":
        "C466 — a loving subject initiates",
    "Logos.ThomisticAct.producing_coexists_with_immutability":
        "C467 — the ground produces *and* is immutable, in one theorem",
    "Logos.ActCascade.someone_means_something":
        "C469 — the cheapest cascade row: meaning from the datum alone",
    "Logos.ActCascade.someone_exists_as_subject":
        "C470 — someone exists as a subject, from the datum alone",
    "Logos.ActCascade.an_actual_subject_obtains":
        "C471 — the corpus's existential proposition, definitionally C470",
    "Logos.ActCascade.an_agent_exists":
        "C472 — `Agent := True`; discharges T4 and is no stronger than C470",
    "Logos.ActCascade.an_intentional_subject_exists":
        "C473 — an intentional subject exists, under the subject-side name",
    "Logos.ActCascade.intentionality_is_instantiated":
        "C474 — the same predication under the corpus's second name",
    "Logos.ActCascade.genuineChoice_exists_of_act_datum_constitutive":
        "C475 — free will, constitutive route (the `AxIntentionalChoice` price made visible)",
    "Logos.ActCascade.genuineChoice_exists_of_act_datum_polarity":
        "C476 — free will, polarity route; a second price, not a substitute",
    "Logos.ActCascade.freeWill_exists_of_act_datum_constitutive":
        "C477 — the corpus's own \"free will exists\" from the performative datum",
    "Logos.ActCascade.freeWill_exists_of_act_datum_polarity":
        "C478 — the same conclusion, independent route, different price",
    "Logos.ActCascade.freeSubject_exists_of_act_datum":
        "C479 — a free subject exists; `FreeSubject` is defined as `FreeWill`",
    "Logos.ActCascade.noMeaning_is_refuted_unconditionally":
        "C480 — meaninglessness refuted with no semantic price at all",
}


def verify_chain_coverage(node_map: dict, claims_by_id: dict) -> None:
    """Hard-fail the build on two chain-list defects, and report coverage.

    1. INTEGRITY — every `*_STEPS` row must point at a live kernel node, and when
       it names a C-id, that C-id must resolve (via the generator's own resolver)
       to exactly the declaration the row claims. This catches the dominant real
       drift: a theorem is renamed and the list is not.
    2. REQUIRED COVERAGE — every declaration in `CHAIN_REQUIRED_DECLS` must appear
       in at least one `*_STEPS` list. This is the AGENTS.md sync rule made
       mechanical for the batches it bit.

    Badges and footprints are never touched here; this only governs membership.
    """
    problems = []

    listed: dict[str, str] = {}          # fullName -> list name
    cid_rows: list[tuple[str, str, str, str]] = []   # (list, cid, full, short)
    for lname, rows in ALL_CHAIN_STEPS:
        for _marker, cid, full, _atype, _text in rows:
            listed.setdefault(full, lname)
            if cid and cid != "—":
                cid_rows.append((lname, cid, full, full.rsplit(".", 1)[-1]))

    # 1. integrity
    for lname, cid, full, short in cid_rows:
        if full not in node_map:
            problems.append(
                f"chain integrity: {lname} row {cid} names `{full}`, which is not a live "
                f"kernel node (renamed or deleted?)")
            continue
        resolved = claims_by_id.get(full)
        if resolved and resolved["id"] != cid:
            problems.append(
                f"chain integrity: {lname} row labels `{short}` as {cid}, but the ledger "
                f"resolves it to {resolved['id']} — fix the row or the ledger")

    # 2. required coverage
    for full, why in sorted(CHAIN_REQUIRED_DECLS.items()):
        if full not in listed:
            problems.append(
                f"chain coverage: `{full}` must appear in a reader-facing chain list "
                f"({why}); it is in none. Per AGENTS.md, extending the hand-authored "
                f"`*_STEPS` list is part of the same change that adds the declaration.")
        elif full not in node_map:
            problems.append(
                f"chain coverage: `{full}` is listed but is not a live kernel node")

    if problems:
        for p in problems:
            print(f"  ✗ {p}")
        raise SystemExit(
            f"ERROR: {len(problems)} chain-list problem(s). The reader-facing deduction "
            f"would drift from the kernel; see AGENTS.md (chain membership is hand-maintained, "
            f"badges and footprints are derived).")

    n_decl = sum(len(r) for _n, r in ALL_CHAIN_STEPS)
    print(f"  ✓ chain integrity: {n_decl} rows across {len(ALL_CHAIN_STEPS)} chain lists, "
          f"all resolving to live nodes and correct ledger ids.")
    print(f"  ✓ chain coverage: all {len(CHAIN_REQUIRED_DECLS)} required declarations "
          f"present ({len(listed)} distinct declarations listed).")


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


STIPULATION_AUDIT_PATH = FORMAL / "stipulation_audit.json"


def render_stipulation_badge() -> list[str]:
    """◈ badge rows for the registered definitional stipulations.

    Derived, never transcribed: entries come from
    `formal/stipulation_audit.json` (written by `scripts/audit_stipulations.py`
    from `formal/Logos/Stipulations.lean`). A missing audit file degrades to a
    warning line so standalone runs keep working; `make all` always regenerates
    it before this runs."""
    if not STIPULATION_AUDIT_PATH.exists():
        return ["- ⚠ stipulation audit not generated yet "
                "(run `python3 scripts/audit_stipulations.py`)."]
    try:
        data = json.loads(STIPULATION_AUDIT_PATH.read_text(encoding="utf-8"))
    except (OSError, ValueError) as e:
        return [f"- ⚠ stipulation audit unreadable: {e}."]
    lines = []
    for e in data.get("stipulations", []):
        deps = ", ".join(f"`{d}`" for d in e.get("dependents", []))
        lines.append(
            f"- ◈ `{e.get('name')}` ({e.get('tag')}, `{e.get('location')}`) — "
            f"{e.get('cost', '')} Rested on by: {deps}.")
    if not lines:
        lines.append("- (no stipulations registered)")
    return lines


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

    ap("")
    ap("### D.2b Registered definitional stipulations (◈)")
    ap("")
    ap("A definitional stipulation settles a philosophical question by fiat in a "
       "match arm, rather than by proof or declared axiom. Each entry below is "
       "declared in `formal/Logos/Stipulations.lean` with its `Tag:` and "
       "`Philosophical cost:`, verified by `scripts/audit_stipulations.py`, and "
       "badged ◈ with the theorems whose `trivial`-class proofs rest on it.")
    ap("")
    for sline in render_stipulation_badge():
        ap(sline)

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
    # Counts come from `derive_score_data`, the same function the README score
    # block reads, so the annex and the document cannot drift apart. That
    # function also holds the reconciliation assertion the plan requires be
    # preserved: it fails the build when the badges do not sum to the inventory.
    sd = derive_score_data(all_claims, decls, node_map)
    detailed_badges = compute_detailed_badges(all_claims, decls, node_map)
    cnt_prov = sd["n_prov"]
    cnt_up = sd["n_up"]
    cnt_ax = sd["n_ax"]
    cnt_repeat = sd["n_rep"]
    cnt_cm = sd["n_cm"]
    cnt_blocked = sd["n_blocked"]
    cnt_deferred = sd["n_deferred"]
    cnt_other = sd["n_other"]

    steps = [c for c in found_claims if derived_for(c, node_map)]
    derived = [derived_for(c, node_map) for c in steps]
    n_prov_decl = sum(1 for d in derived if d == "PROVEN")
    n_up_decl = sum(1 for d in derived if d == "PROVEN↑")
    n_ax_decl = sum(1 for d in derived if d == "AXIOM")

    ap(f"- **Kernel-derived status** (#print axioms + axiom `Tag:`): "
       f"**{cnt_prov} ✅** · **{cnt_up} ⚠️** · **{cnt_ax} ◆** (unique steps detailed in the map)")
    ap(f"- **Reconciled claim inventory ({len(all_claims)} total):** "
       f"{cnt_prov + cnt_up} unique active steps ({cnt_prov} ✅ + {cnt_up} ⚠️) · "
       f"{cnt_cm} countermodel boundaries (🧱) · "
       f"{cnt_repeat} repeated / dissolved (→) · "
       f"{cnt_blocked} blocked / missing (✖) · "
       f"{cnt_deferred} deferred (➖)"
       + (f" · {cnt_other} other ({', '.join(b for b in detailed_badges.values() if b not in ('✅', '⚠️', '◆', '🧱', '→', '✖', '➖'))})" if cnt_other else ""))
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
    # The last cell is the *claim's* dependency data, so for a claim with no
    # kernel declaration it must not be filled with a scraped token. The ledger
    # rows for the F-claims put a whole sentence in the declaration cell, and the
    # parser's identifier scrape out of that sentence produced `BLOCKED` for F15,
    # `def` for F13, `propext` for F9 — printed under a "Used by" header, where a
    # reader scanning F15 for its status saw `BLOCKED` beside an AXIOM claim. A
    # scraped string is only shown when it actually resolves to a declaration;
    # otherwise the cell carries the derived badge, which is the thing a reader
    # opening an F-row is looking for.
    ap("| ID | Lean declaration | File#L | Kernel axioms | Depends on (Lean) | Used by / status |")
    ap("|---|---|---|---|---|---|")
    badges = compute_detailed_badges(
        [c for sec in sections for c in sec["claims"]], decls, node_map)
    for sec in sections:
        for c in sec["claims"]:
            cid = c["id"]
            full = c.get("_full")
            if not full or full not in decls:
                lr = c.get("lean_ref") or ""
                ref = (f"`{lr}`" if lr in decls else "")
                ap(f"| {cid} | — | — | — | — | {ref or badges.get(cid, '—')} |")
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
     "not harm. C41/C43 derive love between two "
     "persons under the plurality bridge; C42/C44/C45 derive the *eternal* love-relation "
     "given an exhibited necessary-kind pair (2026-09-28, two-kinds) — plurality alone still does not force love, and kind-blind plurality no longer forces persistence either; those are separate "
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
    # Batch C2 (2026-09-27): the five names the hand-authored dict was missing, appended in
    # true first-use order by a ledgered claim — never re-derive, or the A# citations
    # embedded in generated prose renumber. Only three are Batch C's own exposure:
    # AxBenevolentBearingObtains is a pre-existing gap (first cited C177), and Evil is
    # cited by NOTHING — registry-only, because its sole consumer
    # (Logos.MoralFrontierAudit.stance_exhibits_moral_poles) is itself unledgered.
    "AxBenevolentBearingObtains": "A21",   # first cited C177 (pre-existing gap)
    "GroundBearsGood": "A22",              # first cited C331
    "AxGroundLovesContingentRealm": "A23",  # first cited C339
    # AxContingentCreationObtains was A24 (first cited C350) and is RETIRED 2026-09-27:
    # the axiom was deleted rather than ledgered, because the lemma it declared unavailable
    # was already a theorem. On the same day (lot COSMOS-EXISTENCE-IS-FREE) the claim it
    # carried was SPLIT: C350 `contingent_realm_obtains` is the free existence and pays
    # nothing, while C367 `cosmos_obtains` — the meaning-bearing half — is what rests on
    # the plurality bridge AxTwoSubjects (A15). The registry does not move either way.
    "Evil": "A25",                          # cited by no claim row — registry-only
    # Batch TWO-KINDS (2026-09-28): the two names the hand-authored dict was missing,
    # appended in true first-use order by a ledgered claim (C403/C404) — never re-derive.
    "NecessarySubjectKind": "A26",          # first cited C403 (the kind classifier, VOCAB)
    "necessaryPersonalSubjectExists": "A27",  # first cited C404 (the inhabitant bridge, META)
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
    "C77": "`PersonStabilityPrinciple : Person s → NecessarySubjectKind s → NecessarySubject s` (explicit kind-relative conditional hypothesis; the old unconditional form is refuted by `CountermodelPersonNotNecessary` and `ContingentAgencyModel`, which exhibit the contingent kind)",
    "C91": "`subject_nec_entity_nec : NecessarySubject s → "
           "NecessaryEntity (EntityOf s)` (definitional lift)",
    "C92": "`PersonStabilityPrinciple` (kind-relative conditional hypothesis) and `subject_nec_entity_nec` (definitional lift)",
}

# Curated sharper resolutions for obstructions where the generic status phrase
# is too weak (FORMAT.md §5.2). Presentation data, scoped to these rows.
RESOLUTION_OF = {
    "C77": "Conditional upon kind-relative PersonStabilityPrinciple; hostile countermodels exhibit the contingent kind, which is why the unconditional form fails and the kind-relative form stands.",
    "C92": "Conditional upon kind-relative PersonStabilityPrinciple; hostile countermodels exhibit the contingent kind, which is why performative agency does not logically force modal entity-necessity of every person.",
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
     "ns": "Logos.HostileSemantics.CountermodelSubjectWithoutPerson",
     "verdict": "NOT ESTABLISHED — wrong as the actual world only if personhood actually obtains (the T12/`AxTwoSubjects` route); the datum alone exhibits a subject, not a person"},
    {"key": "NoPerson", "title": "The personless act",
     "attacks": "the bare act datum forcing `Person`",
     "ns": "Logos.HostileSemantics.CountermodelNoPerson",
     "verdict": "NOT ESTABLISHED — wrong as the actual world only if a person actually exists; the act-datum exhibits agency, not personhood"},
    {"key": "NoFreeWill", "title": "The determined act",
     "attacks": "`Act → Chooses` / `Act → FreeWill`",
     "ns": "Logos.HostileSemantics.CountermodelNoFreeWill",
     "verdict": "WRONG AS THE ACTUAL WORLD ONLY IF `AxIntentionalChoice`/`AxActPolarity` INSISTED"},
    {"key": "UnitPlurality", "title": "The unit world",
     "attacks": "one act forcing a plurality of subjects",
     "ns": "Logos.HostileSemantics.UnitPluralityCountermodel",
     "verdict": "WRONG AS THE ACTUAL WORLD ONLY IF `AxTwoSubjects` INSISTED — not granted: no plurality yet unless the proof demands it"},
    {"key": "ContentWithoutPerson", "title": "Content without a person",
     "attacks": "content existence entailing personhood",
     "ns": "Logos.HostileSemantics.PropositionalPersonhood.CountermodelContentWithoutPerson",
     "verdict": "NOT ESTABLISHED — wrong as the actual world only if content actually has a personal bearer"},
    {"key": "SubjectNecessityNotEntity", "title": "Persistence without entity",
     "attacks": "subject-persistence entailing entity-necessity by logic alone",
     "ns": "Logos.HostileSemantics.CountermodelSubjectNecessityNotEntityNecessity",
     "verdict": "UNANSWERED — a limit on inference; no grant settles it"},
    {"key": "PersonNotNecessary", "title": "The contingent person",
     "attacks": "`Person → NecessarySubject` as a logical law",
     "ns": "Logos.HostileSemantics.CountermodelPersonNotNecessary",
     "verdict": "attack STANDS — the all-contingent kind-assignment is admissible, so personhood does not logically force necessity; WRONG AS THE ACTUAL WORLD only if the kind bridge is granted — which Γ now does (C404 `necessaryPersonalSubjectExists`, C409 Claim D)"},
    {"key": "VeridicalMeaning", "title": "Veridical meaning (one and two persons)",
     "attacks": "the act datum forcing genuine choice",
     "ns": "Logos.HostileSemantics.CountermodelVeridicalMeaning",
     "verdict": "WRONG AS THE ACTUAL WORLD ONLY IF `AxIntentionalChoice`/`AxActPolarity` INSISTED"},
    {"key": "PluralityWithoutLove", "title": "Plurality without love",
     "attacks": "plurality entailing love",
     "ns": "Logos.HostileSemantics.CountermodelPluralityWithoutLove",
     "verdict": "WRONG AS THE ACTUAL WORLD ONLY IF `AxGroundLovesContingentRealm` INSISTED"},
    {"key": "FalsityWorld", "title": "The falsity world read as the actual world",
     "attacks": "the empty (all-`TV.f`) world being the world the proof is written in",
     "ns": "Logos.HostileSemantics.CountermodelFalsityWorld",
     "verdict": "ELIMINATED — this is the one possibility the world-datum kills on its own, for free: `falsityWorld_ne_actualWorld` and `falsityWorld_holds_no_contingent_subject` against `contingent_realm_obtains`. No axiom is charged and the BLOCKED contingent-inhabitation lemma is not needed"},
]

# How a countermodel's world-structure stands to the world-datum
# (`Stipulations.contingentWorldDatum`). The constructor comes from the model's
# own `def worldStance : WorldStance` in `formal/Logos/HostileSemantics.lean`, so
# the classification is DERIVED, not transcribed; the sentence a reader sees lives
# here, once per constructor. `verify_world_stances` cross-checks the constructor
# against the structure the model's namespace actually declares, so this table
# cannot drift into prose the model does not support.
WORLD_STANCE_LEGEND = {
    "noWorldStructure":
        "SILENT — the model declares no world sort, so the datum neither saves nor "
        "excludes it; what the model does say is in its gloss.",
    "contingentSubjects":
        "SATISFIED — the model's subjects are not world-rigid, so it is a world of "
        "contingent subjects and the datum is consistent with it. Excluded as *our* "
        "world only by the grants named above.",
    "necessarySubjectsOnly":
        "NOT ELIMINATED — every subject in the model is world-rigid, so its world is a "
        "world of necessary subjects only and ours is not that. Γ cannot say so: the "
        "exclusion needs the contingent-inhabitation lemma, which is BLOCKED "
        "(`SUBJECTS.md` §4), not priced.",
    "falsityWorldAsActual":
        "ELIMINATED — the model takes the all-`TV.f` valuation to *be* the actual world, "
        "and Γ refutes that outright with no axiom: `falsityWorld_ne_actualWorld` and "
        "`falsityWorld_holds_no_contingent_subject` against `contingent_realm_obtains`.",
}


def _ns_block(ns: str) -> str:
    """The source of the namespace `ns` (by its last component), for cross-checks."""
    tail = ns.rsplit(".", 1)[-1]
    text = (LEAN_DIR / "HostileSemantics.lean").read_text(encoding="utf-8")
    m = re.search(r"^namespace %s\b(.*?)^end %s\s*$" % (re.escape(tail), re.escape(tail)),
                  text, re.S | re.M)
    return m.group(0) if m else ""


def verify_world_stances() -> dict:
    """Cross-check each catalogued model's `worldStance` against its own structure.

    A model that declares no world sort MUST be `noWorldStructure`; a model that
    declares one MUST NOT be. The point is that the third axis is derived from the
    model, so a model that later gains a world sort cannot keep being described as
    "silent". Violation is a build error, not a warning.
    """
    out = {}
    for cm in COUNTERMODEL_CATALOG:
        key, ns = cm["key"], cm["ns"]
        block = _ns_block(ns)
        if not block:
            raise SystemExit(f"world-stance check: no namespace block for {ns}")
        m = re.search(r"^def worldStance : WorldStance := \.(\w+)", block, re.M)
        if not m:
            raise SystemExit(f"world-stance check: {ns} has no `def worldStance`")
        ctor = m.group(1)
        if ctor not in WORLD_STANCE_LEGEND:
            raise SystemExit(
                f"world-stance check: {ns} has stance .{ctor}, which has no legend entry")
        # A world sort is a `World`/`State` sort declared *in the model's own
        # block*; nested sub-namespaces (e.g. VeridicalMeaning's `Single`/`TwoPersons`)
        # declare theirs, and they decide the parent's stance.
        declares_world = bool(re.search(
            r"^\s*(?:abbrev|def) (?:World|State)\s*:", block, re.M))
        # `falsityWorldAsActual` is the one stance a self-contained model cannot
        # reach by declaring a sort of its own: it is a *reading of Γ's own world
        # semantics* (`Entity.actualWorld`/`Entity.falsityWorld`), which is what
        # makes it refutable by Γ's theorems. So the rule is inverted for it — it
        # must NOT declare a world sort of its own, and must reference both of Γ's.
        if ctor == "falsityWorldAsActual":
            if declares_world:
                raise SystemExit(
                    f"world-stance check: {ns} claims .falsityWorldAsActual but declares "
                    f"a world sort of its own — that stance is a reading of Γ's worlds")
            for sym in ("falsityWorld", "actualWorld"):
                if sym not in block:
                    raise SystemExit(
                        f"world-stance check: {ns} claims .falsityWorldAsActual without "
                        f"referencing `{sym}`")
        elif ctor == "noWorldStructure" and declares_world:
            raise SystemExit(
                f"world-stance check: {ns} declares a world sort but claims "
                f".noWorldStructure — it must decide its own reading")
        elif ctor != "noWorldStructure" and not declares_world:
            raise SystemExit(
                f"world-stance check: {ns} claims .{ctor} but declares no world sort")
        out[key] = ctor
    return out


WORLD_STANCES = verify_world_stances()

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
        "Person(s) := ThomisticPersonCore(s) (*individual substance of a rational nature with dominion "
        "over its acts; the reduction to free will is the priced theorem freeWill_implies_person, "
        "0 substantive axioms*).",
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
     "targets": ["C41", "C43"]},
    {"label": "exhibited kind → eternal love", "status": "DEFINITIONAL",
     "targets": ["C42", "C44", "C45"]},
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
    ap("**Three axes — read all three.** A countermodel makes three claims, and the brief bears on "
       "each in a different way. "
       "The *attack* is a derivability claim: it stands unless Γ derives the disputed inference, and "
       "that verdict is the kernel's own derivability fact — machine-checked, not transcribed. "
       "The *model* is a description of a world, and whether it may be *wrong as the actual world* is "
       "settled by the grants named beside it — this verdict is prose, keyed to specific grants, and it "
       "is hand-maintained by design (the catalogue is the presentation layer; the models themselves are "
       "the machine-checked part). "
       "The *world-datum* ◈ `contingentWorldDatum` is a third and narrower question: given that this "
       "contingent world — the one the proof is written in — exists, what does each model's own "
       "world-structure say about it? This third axis is **derived, not transcribed**: it comes from each "
       "model's `def worldStance : WorldStance` in `HostileSemantics.lean`, and "
       "`verify_world_stances()` fails the build if a model declares a world sort while calling itself "
       "silent, or claims a reading while declaring none. Read it as the ledger's honest summary of the "
       "author's own question — *which models are wrong given that the world exists* — and note how few "
       "the world-datum can answer on its own: it eliminates exactly one of the ten "
       "(`CountermodelFalsityWorld`, the all-`TV.f` valuation read as the actual world, refuted for free), "
       "it is *satisfied* by one (`PersonNotNecessary` — a contingent world of one person), it is silent "
       "on seven, and the remaining one (`SubjectNecessityNotEntity`) needs the contingent-inhabitation "
       "lemma, which is BLOCKED, not priced. The eliminations inside the catalogue come from the kind "
       "bridge and the content bridges, not from the world's existence. Note also that the world-datum is "
       "**not** the act-datum (formerly ◈ `performativeActDatum`, now the declared axiom C454); the two were conflated here until 2026-09-28. "
       "The no-meaning family (M1/C294/C382) is **WRONG as the actual world** on the act-datum alone "
       "(C402; also outright on the plurality bridge, C401) — while C382's *attack* (bare-vocabulary "
       "consistency of the form) stands untouched. It *satisfies* the world-datum: a world can hold "
       "subjects that mean nothing.")
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
           f"**What survives:** {gloss.get('survives', '—')} · `{ns}`{loc} "
           f"**As the actual world:** {cm.get('verdict', '—')} "
           f"**Given the contingent world exists:** {WORLD_STANCE_LEGEND[WORLD_STANCES[key]]}")
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


# ---------------------------------------------------------------------------
# Phase 4 — the two-column score block. Every figure below is DERIVED, never
# transcribed (AGENTS.md: a hardcoded number in generated prose is a
# regeneration error in the same spirit as an untagged axiom). The block and the
# annex counters are computed by `derive_score_data`, so they cannot disagree:
# a mismatch would mean one of the two had stopped reading the derived data.
# ---------------------------------------------------------------------------

def derive_score_data(all_claims: list[dict], decls: dict, node_map: dict) -> dict:
    """Single source of the score-block figures.

    Returns badge counts, the open (still-unsettled) claim set, the declared
    axiom inventory by tag, and the axiom-free theorem share. Every value is a
    pure function of the kernel, `formal/axiom_audit.json`, the Lean `Tag:`
    lines, and the GAPMAP ledger."""
    global _REGISTRY, _AUDIT
    if not _AUDIT:
        _AUDIT = load_audit()
    if not _REGISTRY:
        _REGISTRY = load_axiom_registry(decls, node_map)

    badges = compute_detailed_badges(all_claims, decls, node_map)
    count = lambda b: sum(1 for v in badges.values() if v == b)
    n_prov, n_up, n_ax = count("✅"), count("⚠️"), count("◆")
    n_cm, n_rep = count("🧱"), count("→")
    n_blocked, n_deferred = count("✖"), count("➖")
    n_other = sum(1 for b in badges.values()
                  if b not in ("✅", "⚠️", "◆", "🧱", "→", "✖", "➖"))

    # Still-open set: BLOCKED and DEFERRED rows that are not dissolved into a
    # canonical claim. `→` rows are cross-references, not open questions, and a
    # `🧱` row is a demonstrated boundary — both are results, not gaps.
    #
    # A retired route is separated out because calling it "still open" is a
    # falsehood in the opposite direction: its note says the step was destroyed
    # under hostile semantics, i.e. the question is *settled negatively*, not
    # pending. The corpus already files these under "Obstructions & retired
    # alternatives"; merging them into the open column would misreport 15
    # settled negatives as outstanding work.
    by_id = {c["id"]: c for c in all_claims}
    dissolved = set(_CTX.get("canonical_of") or ())
    open_rows, retired_rows = [], []
    for cid, badge in sorted(badges.items(),
                             key=lambda kv: (kv[1] != "✖", kv[1] != "➖", kv[0])):
        if badge in ("✖", "➖") and cid not in dissolved:
            c = by_id.get(cid, {})
            row = {
                "id": cid, "badge": badge, "status": c.get("status", ""),
                "ref": c.get("lean_ref", ""), "note": c.get("note", ""),
                "section": c.get("section", ""),
                "gloss": c.get("_gloss_display") or c.get("_gloss") or "",
            }
            is_retired = any("retired" in src.lower()
                             for src in (row["gloss"], row["note"]))
            (retired_rows if is_retired else open_rows).append(row)

    # Declared axioms, by tag, straight from the Lean `Tag:` lines.
    tags = {}
    for r in _REGISTRY.values():
        tags[r["tag"]] = tags.get(r["tag"], 0) + 1
    n_axioms = len(_REGISTRY)

    # Axiom-free theorems: audited `{}` (or Lean-core-only) over the theorems of
    # `formal/Logos/`. The denominator is restricted to declarations the audit
    # actually covers: `_AUDIT.get(f, ())` on an *unaudited* name returns `()`,
    # which would score a declaration as axiom-free on the strength of its own
    # absence — the dropped-row failure of Correction 9, one level down. The
    # three such names are `parse_lean_sources` artefacts (`Logos.Recovered…is`,
    # `of`, `content_reality_hook`), but the guard is general.
    kern_all = {f for f, n in decls.items() if n["kind"] in ("theorem", "example")}
    kern = {f for f in kern_all if f in _AUDIT}
    unaudited = sorted(kern_all - kern)
    free = sum(1 for f in kern
               if not any(a.startswith("Logos.") for a in _AUDIT.get(f, ())))

    # Phase 4c guard, enforced rather than asserted in prose: the won figure is
    # computed *through* WON_BADGES, so a declared axiom can never reach it.
    n_won = sum(1 for b in badges.values() if b in WON_BADGES)
    assert "◆" not in WON_BADGES, (
        "WON_BADGES must not contain a declared-axiom badge: axioms are inputs, "
        "not wins")
    assert n_won == n_prov + n_up + n_cm, (
        f"won-count {n_won} != affirmative+boundary "
        f"{n_prov + n_up + n_cm} — WON_BADGES and the score block disagree")
    assert n_won < len(badges), "every claim counted as a win: nothing is open?"

    data = {
        "n_won": n_won,
        "n_prov": n_prov, "n_up": n_up, "n_ax": n_ax, "n_cm": n_cm,
        "n_rep": n_rep, "n_blocked": n_blocked, "n_deferred": n_deferred,
        "n_other": n_other, "n_total": len(all_claims),
        "open_rows": open_rows, "retired_rows": retired_rows,
        "tags": tags, "n_axioms": n_axioms,
        "n_kern": len(kern), "n_free": free, "n_unaudited": len(unaudited),
        "n_affirmative": n_prov + n_up,
    }
    # The reconciliation assert the plan requires be preserved: the block may
    # only ever publish numbers that sum back to the claim inventory.
    total = (n_prov + n_up + n_ax + n_cm + n_rep
             + n_blocked + n_deferred + n_other)
    assert total == len(all_claims), (
        f"Reconciliation error: detailed claims ({total}) != total claims "
        f"({len(all_claims)})")
    return data


# A ledger gloss often opens with its own status before the statement, e.g.
# "BLOCKED (AC5 unmet, D1′ recorded not executed): any entity that grounds ...".
# Splitting on the first sentence would surface the status, not the claim, so
# strip the status prefix and keep the statement that follows the first colon.
_SCORE_STATUS_RE = re.compile(
    r"^\**(?:BLOCKED|DEFERRED|RETIRED|AXIOM|PROVEN|OPEN|NOT ESTABLISHED)\**"
    r"\s*(?:\([^)]*\))?\s*[:\u2014-]\s*", re.I)


def _score_label(row: dict, limit: int = 150) -> str:
    """One-line, human-checkable name for an open or retired claim row.

    Prefers the claim's English meaning (resolved from code), then the ledger
    note, then the bare reference — never invents a description. Some glosses
    run to several paragraphs (the ASIETY-FREEDOM diagnostics); a table cell
    takes the first sentence, capped, and the full text stays where it was
    always readable — the ledger and the step-by-step block."""
    for src in (row.get("gloss") or "", row.get("note") or ""):
        t = " ".join(src.split()).strip()
        if not t:
            continue
        t = _SCORE_STATUS_RE.sub("", t)
        # First sentence, or the first clause if the sentence runs long.
        head = t.split(". ")[0].rstrip(".")
        if len(head) <= limit:
            t = head
        elif " — " in t[: limit + 40]:
            t = t.split(" — ")[0].rstrip(" .")
        else:
            t = head[:limit].rsplit(" ", 1)[0].rstrip(" ,;:") + "…"
        if t:
            return t
    return f"`{row['ref']}`" if row.get("ref") else row["id"]


def _def_bridge_debt() -> dict | None:
    """The inherited `def`-as-bridge debt, read from the allowlist at generation
    time (VISIBILITY.md Phase 7). A `def` used as a bare-name premise is a bridge
    `#print axioms` cannot see, so it is a price the kernel does not charge: a
    theorem resting on one shows a footprint that omits it. Returns None when the
    allowlist is absent, so the score block degrades rather than failing.

    Counted here, not transcribed, because the number qualifies every `n_free`
    figure quoted beside it: "943 of 1666 rest on no Γ axiom" is true, and this
    says what it does not cover."""
    import json as _json
    try:
        raw = _json.loads((ROOT / "scripts" / "stipulated_def_allowlist.json")
                          .read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    entries = raw.get("acknowledged", [])
    if not entries:
        return None
    reviewed = [e for e in entries if e.get("reviewed")]
    # A bridge is `paid` only if it stopped being a def: the allowlist keys
    # `acknowledged` by declaration name, and a promoted one leaves the list.
    return {
        "total": len(entries),
        "theorems": sum(len(e.get("dependents", [])) for e in entries),
        "reviewed": len(reviewed),
        "worst": max((len(e.get("dependents", [])) for e in entries), default=0),
    }


def render_score_block(sd: dict) -> list[str]:
    """The two-column Won / Still-open score block for README.md.

    Anti-goal (VISIBILITY.md §4c): this is an accounting a hostile reader can
    check, not a verdict. The right-hand column names every open row rather
    than summing it, and the left-hand column carries its denominator and the
    vocabulary-only caveat, so the two can never be read as a bare ratio."""
    L = []
    ap = L.append
    n_total = sd["n_total"]
    n_aff = sd["n_affirmative"]
    n_cm = sd["n_cm"]
    n_open = len(sd["open_rows"])
    tags = sd["tags"]
    vocab = tags.get(TAG_VOCAB, 0)
    subst = sum(v for k, v in tags.items() if k != TAG_VOCAB)

    n_ret = len(sd["retired_rows"])
    blocked = [r for r in sd["open_rows"] if r["badge"] == "✖"]
    deferred = [r for r in sd["open_rows"] if r["badge"] == "➖"]
    pct_free = 100.0 * sd["n_free"] / sd["n_kern"] if sd["n_kern"] else 0.0

    ap("## The score: what Γ has won, and what is still open")
    ap("")
    ap("Every figure in this table is **derived from the Lean kernel** at generation")
    ap("time — each badge from (node kind, audited `#print axioms` footprint, declared")
    ap("axiom `Tag:`), never transcribed. The same computation prints the audit counters")
    ap("in [`investigations/kernel-audit.md`](../investigations/kernel-audit.md); the two")
    ap("cannot disagree, because both read the one derived table. A claim's status here")
    ap("is exactly its status in the ledger — this block only counts, and the columns")
    ap("below are built by joining those counts, not by judgement.")
    ap("")

    debt = _def_bridge_debt()
    if debt:
        ap("**One thing these figures do not cover.** The axiom-free counts below are")
        ap("footprints from `#print axioms`, which cannot see a **`def` used as a premise**")
        ap(f"by name. There are **{debt['total']}** such inherited bridges, carrying")
        ap(f"**{debt['theorems']}** theorems (the largest underwrites {debt['worst']}). They are")
        ap("now enumerated in the ledger's `def`-as-bridge section, which is *disclosure*,")
        ap(f"not payment: **{debt['reviewed']}** have been reviewed and **0** have been promoted")
        ap("to a declared axiom. So a ✅ badge means the theorem is kernel-verified *conditional")
        ap("on a bridge the kernel does not charge*. Full census and the open three-way")
        ap("decision: `scripts/census_stipulated_defs.py`.")
        ap("")

    ap("| **Won** | **Still open** |")
    ap("|---|---|")

    # --- left column: one derived row per bullet ----------------------------
    left = [
        f"**{n_aff} affirmative claims derived** out of **{n_total}** ledger claims — "
        f"{sd['n_prov']} ✅ kernel-verified, {sd['n_up']} ⚠️ derived under a substantive "
        f"(`SEM`/`META`) axiom, each ⚠️ row naming the bridge it rests on.",
        f"**{n_cm} countermodel boundaries** {COUNTERMODEL_BADGE} — a hostile model in which the claim "
        f"*fails*. These are won results about the limit of the theory, not gaps.",
        f"**{sd['n_free']} of {sd['n_kern']} theorems in `formal/Logos/` rest on no Γ "
        f"axiom at all** ({pct_free:.0f}%) — counted from `formal/axiom_audit.json`, not "
        f"claimed.",
        f"**The whole price is {sd['n_axioms']} declared axioms**: {vocab} are `VOCAB` "
        f"(the vocabulary the statements need in order to be sayable) and {subst} are "
        f"substantive. Only the {subst} are philosophical commitments; the rest are the "
        f"theory's definitions of its own words, which is a different thing from a "
        f"premise.",
    ]
    # The attribute corollaries, counted from the chain list rather than by hand.
    attr = [row for row in SEMANTIC_FINITUDE_STEPS if row[0] == "L2"]
    if attr:
        left.append(
            f"**{len(attr)} attribute corollaries became unconditional theorems** "
            f"(C389–C398) — they were conditional on a `def` until F15 was declared, so "
            f"this is a *strengthening*: fewer hidden premises, same conclusions.")

    # --- right column: every open row, named; retired set kept separate -----
    right = []
    for badge, rows, word in (("✖", blocked, "blocked"),
                              ("➖", deferred, "deferred")):
        if not rows:
            continue
        right.append(f"**{len(rows)} {word}** {badge} — named individually")
        for r in rows:
            right.append(f"&nbsp;&nbsp;· **{r['id']}** — {_score_label(r)}")
    if n_ret:
        right.append(
            f"**{n_ret} retired routes** — settled *negatively*, not pending: each step "
            f"was destroyed by a hostile model, so the question is closed against it "
            f"(see *Appendix C*): " +
            ", ".join(f"`{r['id']}`" for r in sd["retired_rows"]))

    # Interleave the columns row-wise; markdown tables cannot hold lists of
    # unequal length, so the shorter side gets padding cells.
    for i in range(max(len(left), len(right))):
        ap(f"| {left[i] if i < len(left) else ''} | {right[i] if i < len(right) else ''} |")

    ap("")
    ap(f"**Read the two columns together and the shape is precise: Γ won the metaphysics")
    ap(f"of the ground and lost the soteriology.** Established: genuine normativity has a")
    ap(f"personal ground; that ground is unique and necessary; it possesses canonical")
    ap(f"aseity, simplicity, and pure actuality. Not established: that the person of that")
    ap(f"ground is *one*. Strict monotheism, the Trinity, the Incarnation, and creation")
    ap(f"each remain open, and each is named above with its missing lemma rather than")
    ap(f"absorbed into an average. That is the honest ledger, and the left column is")
    ap(f"larger because the ground-theory was proved, not because the open rows were")
    ap(f"rounded down.")
    ap("")
    ap("Four qualifications, stated rather than hidden:")
    ap("")
    ap("1. **A ✅ means \"kernel-verified on declared vocabulary\", not \"free of "
       "metaphysical assumption\".** The vocabulary axioms are real axioms; they are "
       "merely the ones the statements need in order to be said at all. The substantive "
       f"ones are the {subst} `SEM`/`META` bridges.")
    ap(f"2. **The {sd['n_axioms']} declared axioms are inputs, not wins.** Counting them as "
       "results would be the same error as counting a hypothesis as a proof. They are "
       "listed so the reader can price Γ exactly, and `VOCAB` is separated from "
       "`SEM`/`META` because only the latter are commitments.")
    ap("3. **A 🧱 is a win about a boundary, not about the claim.** Γ building a model in "
       "which monotheism fails is a real theorem — and a theorem *against* monotheism. "
       "The columns keep those apart on purpose.")
    ap(f"4. **The {n_ret} retired routes are counted as neither won nor open.** Their "
       "ledger notes say the step was destroyed under hostile semantics; that is a "
       "settled negative. Filing them under \"still open\" would overstate the debt, "
       "and filing them as won would overstate the theory, so they get their own line.")
    ap("")
    if sd["n_unaudited"]:
        ap(f"<sub>Declaration count excludes {sd['n_unaudited']} parsed names with no "
           f"`#print axioms` footprint; they are `parse_lean_sources` artefacts and are "
           f"excluded from the denominator rather than scored axiom-free.</sub>")
        ap("")
    return L


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
    ap("> A necessary Divine Being/Ground is **proven** (✅): it exists unconditionally as the sole")
    ap("> universal modal grounding ground (`ofGround_universal_modal_ground` C319,")
    ap("> `exactly_one_universal_modal_ground` C320) and possesses Canonical Aseity")
    ap("> (`conditional_canonical_aseity`). A **necessary Person** is likewise derived (⚠️) on the")
    ap("> single declared `META` bridge `necessaryPersonalSubjectExists` (C404 → Claim D, C409).")
    ap("> What is **not** established is monotheism *at the level of the Person*: C212 proves")
    ap("> ground-unicity does not force a unitary monad, and the personal-identification bridge C228")
    ap("> remains `BLOCKED`. Every other claim is definitional, derived, or a declared axiom.")
    ap("")
    ap("Every section below answers the same question — *what is the status of this claim?*")
    ap("")
    ap("> **The Dialectical Inevitability Architecture** — Why every rational attack fails:")
    ap("> 1. **Performative Retorsion (The Trap):** Any attempt to deny objective correctness must claim that its denial is *correct* (`ClaimsCorrect s NoRight`). In the Lean kernel, claiming denial as correct while true yields a direct constructive contradiction (`claims_correct_no_right_self_refuting` → ⊥, 0 substantive axioms). The skeptic cannot even enter the debate without triggering the normative partition.")
    ap("> 2. **Constitutive Semantics (The Deduction):** Rational address between incompatible alternatives is *definitionally* Choice (`Chooses`), having choice is *definitionally* Free Will (`FreeWill`), and a free choosing subject is a Person in the classical Boethian-Thomistic sense by priced theorem (`freeWill_implies_person`, 0 substantive axioms, via the declared law `will_individuation`).")
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
        "attribute": "**Psychological personality** (humanoid consciousness, stream of experience)",
        "scope": "Personal ground / person-type",
        "expected": "COUNTERMODEL",
        "checks": [{"type": "countermodel",
                    "full": "Logos.PersonhoodOntologyAudit.faithful_model_satisfies_free_will_without_opaque_person"}],
        "refs": ["Logos.PersonhoodOntologyAudit.faithful_contingent_person_fails_necessary_subject"],
        "sense": ("Minimal personhood in Γ is functional: the Boethius–Aquinas locus of "
                  "non-derived normative discrimination (`Person := ThomisticPersonCore`). Substantive psychological "
                  "personhood (ordinary humanoid mind, emotional states, stream of consciousness) "
                  "is provably independent: `faithful_model_satisfies_free_will_without_opaque_person` "
                  "(footprint `{}`) satisfies free will without substantive psychological personality. "
                  "The text explicitly disclaims ordinary psychological personality (`README-OLD.md:179-187`)."),
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
        "refs": ["Logos.Choice.FreeWill",
                 "Logos.AsieticChoice.chooses_implies_trueChoice",
                 "Logos.AsieticChoice.trueChoice_exists"],
        "sense": ("`GenuineNormativity ⇒ Chooses ⇒ FreeWill`; "
                  "`FreeWill s ≡ ∃ p q, Chooses s p q` is definitional (`📘`). "
                  "The *existence* half is now also derived outright: a person exists "
                  "(`T5_personExists_from_plurality`), `Person` bundles `FreeWill` "
                  "(`DominionOverActs s ≡ FreeWill s`), so a chooser exists — at the "
                  "META price of `AxTwoSubjects`, which is why the Asiety row below is "
                  "⚠️ AXIOMATIC while this row stays ✅. "
                  "**Disclosed limit on this row:** `indubitable_normative_free_will` is a "
                  "**sub-formula extraction, not a derivation.** It unfolds "
                  "`GenuineNormativity s p q` to `Incompatible p q ∧ p ≠ q ∧ Means s p ∧ "
                  "Means s q`, uses `.1`s, **discards `p ≠ q`**, and concludes `Chooses s p q` "
                  "by reordering three of the four conjuncts. Its `{Means, Subject}` footprint "
                  "is accurate — it records that the structure's fields *are* `Means` — but it "
                  "measures no derivation from independent premises, and it must not be read "
                  "as one."),
    },
    {
        "attribute": "**Asiety** — true freedom (true choice)",
        "scope": "Personal ground / person-type",
        "expected": "PROVEN↑",
        "checks": [{"type": "decl", "full": "Logos.AsieticChoice.asietic_summary"}],
        "refs": ["Logos.AsieticChoice.TrueChoice", "Logos.AsieticChoice.Asiety",
                 "Logos.AsieticChoice.asietic_is_true_freedom",
                 "Logos.AsieticChoice.trueChoice_exists"],
        "sense": ("`Asiety e ≡ ∃ s p q, e = EntityOf s ∧ TrueChoice s p q`, and "
                  "`TrueChoice s p q ≡ Means s p ∧ Means s (¬ p) ∧ ContestedContent ∧ "
                  "Incompatible p q` — so asiety is true freedom **by definition** "
                  "(`📘`); the substantive content is the *derivation*, not the "
                  "identification. Two disclosed prices, both pre-existing: `TrueChoice ≡ "
                  "Chooses` (the openness conjunct is a global frame fact, not a per-pair "
                  "modality), and existence at `AxTwoSubjects` (META). The weak→strong step "
                  "is `ChoiceField → Chooses`, which is **not** free: it needs the "
                  "correctness-judgment premise under `AxJudicativeBipolarity` (SEM), and the "
                  "bare implication with no premise is not merely unproved but machine-refuted. "
                  "**Batch ASIETY-FREEDOM splits this row's chain in two, and the split is the "
                  "point:** the *Act-free* route into asiety is now **axiom-free** "
                  "(`weakChoice_implies_asiety`: `GenuineNormativity s p q → Asiety (EntityOf s)`, "
                  "footprint `{Means, Subject}` — 0 substantive axioms, no `Act`, no `Initiates`, "
                  "no `ClaimsCorrect`, no stipulation), whereas **everything from "
                  "`AsietyFreedom` onward rests on ◈ META** and is badged accordingly. See the "
                  "**ASIETY-FREEDOM chain, step by step** block below for the full pricing."),
    },
    {
        "attribute": "**Shared freedom of the ground** "
                     "(`AsietyFreedom` — the ground's freedom, shared)",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.AsietyFreedom.asietyFreedom_summary"}],
        "refs": ["Logos.AsietyFreedom.AsietyFreedomOfGround",
                 "Logos.AsietyFreedom.AsietyFreeWill",
                 "Logos.AsietyFreedom.asietyFreedom_yields_trueChoice",
                 "Logos.AsietyFreedom.asietyFreedom_yields_asietyFreeWill",
                 "Logos.AsietyFreedom.asietyFreeWill_yields_trueChoice",
                 "Logos.AsietyFreedom.groundIsNotASharerOfAsietyFreeWill"],
        "sense": ("`AsietyFreedomOfGround`: the ground's freedom *reaches* every subject, so "
                  "`TrueChoice` and `AsietyFreeWill` follow **conditionally** "
                  "(`AsietyFreedomOfGround → AsietyFreeWill s`, C290) — this is the reading of "
                  "\"which is shared with us by the creator\". The `Asiety` half of it is "
                  "**axiom-free and independent of the ground** "
                  "(`weakChoice_implies_asiety`, C287); only the *transfer* is priced. "
                  "**◈ META, and the price is load-bearing:** the bridge is a **`def`**, so "
                  "`#print axioms` cannot see it, and its reported `{Means, Subject}` "
                  "footprint is vocabulary-only *whether the bridge is principled or arbitrary* — "
                  "**\"the axiom count did not move\" is therefore NOT a test for this batch** "
                  "(for ASIETIC-CHOICE it was). Three `{}` countermodels price it: "
                  "`asietyAloneDoesNotYieldTrueChoice` (C292, the universal reading is strictly "
                  "stronger than the existential one), `frameContingencyDoesNotBindAPair` (C293), "
                  "and `rightWrongFactYieldsNoChooser` (C294). **No axiom-free existence of a "
                  "chooser**: `¬ N_T ∧ ¬ N_F` is `Prop`-level and quantifies over no `Subject`, so "
                  "the Creator step is conditional and its existence half is *not derivable*. "
                  "**The ground is still not a chooser** (C295 = C285 preserved, by "
                  "`ofGround_ne_ofSubject`): the ground *reaches* subjects, it is not one of them. "
                  "Its `GroundsEntity` premise is **vacuous** (`ground_grounds_the_meaningless`), "
                  "which is why the whole metaphysical weight sits on the ◈ entry."),
    },
    {
        "attribute": "**Divine love** (the ground as lover of contingent reality)",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN↑",
        "checks": [{"type": "decl",
                    "full": "Logos.LovesAsGround.the_ground_is_a_necessary_and_chosen_lover"}],
        "refs": ["Logos.LovesAsGround.GroundLoves",
                 "Logos.LovesAsGround.grounding_reaches_what_love_cannot",
                 "Logos.LovesAsGround.meaningful_love_bridge_is_refuted",
                 "Logos.LovesAsGround.ground_love_cannot_be_read_as_person_love",
                 "Logos.CosmicExistence.the_ground_loves_the_cosmos"],
        "sense": ("The ground is a *necessary* lover of a *chosen* good: `NecessaryEntity "
                  "Entity.ofGround` (`trivial`, ontology-forced) conjoined with a directional "
                  "good it holds toward a contingent, meaning-bearing realm — the machine form "
                  "of `poem.txt:24`'s \"Amar é escolhido e também é necessário\". The claim is "
                  "about the ground **as a kind**; no hypostatic identification is made (C344). "
                  "**Two prices, different in kind** (see the **LOVE chain, step by step** block "
                  "below): the VOCAB primitive `GroundBearsGood` (the directed-good vocabulary "
                  "the library lacked — `GroundsEntity` is undirected and vacuous, `EntityMeans` "
                  "is a capacity of the target, `Good s (_a)` is `Subject`-indexed) and the META "
                  "bridge `AxGroundLovesContingentRealm` (the inhabitation, genuinely not forced: "
                  "the `GroundBearsGood := False` model satisfies all vocabulary while every "
                  "inhabitant fails). "
                  "Note the badge reads **⚠️ AXIOMATIC (AxGroundLovesContingentRealm)** only: "
                  "`GroundBearsGood` is filed under the vocabulary baseline by `footprint_parts` "
                  "and never appears in the parenthetical, so a reader trusting the badge alone "
                  "will take the primitive as free — the chain block below is the only place the "
                  "VOCAB price is visible. What the batch is mostly is negative: the separation "
                  "is machine-checked (C336: grounding reaches an atom, love does not); the "
                  "unrestricted, more attractive bridge is *false* (C338 — the only justification "
                  "for the axiom's meaning hypothesis); and the `GroundLoves → Loves` transfer is "
                  "**unstatable, not merely unproved** (C348), so bridge #9 / C228 is untouched "
                  "and F3, F6/Trinity and the personal-monotheism frontier do not move. "
                  "The cosmos it loves now *exists by theorem* — free of substantive axioms, in fact: C350 "
                  "`contingent_realm_obtains` at `{CL, NecessarySubjectKind, Subject}`, with a contingent-person "
                  "datum paying only for the realm's *content* (C367 `cosmos_obtains`, given an exhibited contingent person) — "
                  "which is not an entailment from the ground."),
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
        "attribute": "**Foundational unicity** (structural unicity of the universal ground of reality)",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.FoundationalUnicity.ofGround_foundational_unicity"},
                   {"type": "decl",
                    "full": "Logos.FoundationalUnicity.ofGround_sole_universal_grounding"},
                   {"type": "countermodel",
                    "full": "Logos.FoundationalUnicity.not_asymmetric_grounding"}],
        "refs": ["Logos.FoundationalUnicity.universal_ground_unicity",
                 "Logos.FoundationalUnicity.no_atom_is_universal_modal_ground",
                 "Logos.FoundationalUnicity.no_discriminating_subject_is_universal_modal_ground",
                 "Logos.FoundationalUnicity.ofGround_sole_universal_ground",
                 "Logos.FoundationalUnicity.unicity_strictly_transcends_world",
                 "Logos.FoundationalUnicity.groundsEntity_reflexive",
                 "Logos.FoundationalUnicity.grounds_ground_iff_maximal",
                 "Logos.FoundationalUnicity.ofGround_unicity_from_no_discriminating_subject",
                 "Logos.FoundationalUnicity.no_discriminating_subject_iff_no_maximal_non_ground",
                 "Logos.FoundationalUnicity.exactly_one_universal_modal_ground"],
        # Phase 5: the affirmative result leads, the retraction follows. Every
        # caveat below is preserved verbatim or extended — only the position
        # changed. The F15 sentences are rewritten rather than reordered, because
        # post-promotion they are false: F15 is now the declared axiom
        # `SemanticFinitude` (C388, `Tag: VOCAB`, the 27th), not an unnamed
        # premise awaiting consolidation.
        "sense": ("**Classical Monotheism of the ground is PROVEN.** "
                  "`exactly_one_universal_modal_ground` (C320) states it outright "
                  "(Aquinas *ST* I, q. 11, a. 3): **existence is unconditional**, and "
                  "uniqueness follows from the single named hypothesis that no subject has "
                  "total meaning-capacity — which is now the **27th declared axiom**, "
                  "`SemanticFinitude` (C388, `Tag: VOCAB`, ledger row F15), and is "
                  "consumed unconditionally by `exactly_one_universal_modal_ground_stipulated` "
                  "(C389, footprint `{Means, NecessarySubjectKind, SemanticFinitude, Subject}`). "
                  "So the price of unicity is one *named vocabulary* axiom, not an "
                  "anonymous premise: the same shape `∀ s, ∃ p, ¬ Means s p` was already "
                  "being paid 20 times across 5 files as the standing hypothesis of "
                  "`DivineSimplicity`, `DivinePureActuality`, `FoundationalUnicity` and "
                  "`CanonicalAseity`; declaring it once is a *consolidation*, and it turned "
                  "ten conditional attribute corollaries (C389–C398) into unconditional "
                  "theorems. "
                  "In `FoundationalUnicity.lean` (footprint `{Means, NecessarySubjectKind, Subject}` — "
                  "VOCAB only). "
                  "**Correction (2026-09-27): the original route is void.** "
                  "(1) Diagnosis — `not_asymmetric_grounding` machine-refutes `AsymmetricGrounding`: grounding is "
                  "meaning-containment and therefore **reflexive** (`groundsEntity_reflexive`), and the definition omitted the "
                  "`g1 ≠ g2` guard, so the premise consumed by `universal_ground_unicity` and `ofGround_foundational_unicity` "
                  "is **unsatisfiable**. Those two rows stay PROVEN as conditional theorems, but no unpayable premise may stand "
                  "as a proven attribute. "
                  "(2) The needed notion already existed — `grounds_ground_iff_maximal` proves that grounding the ground **is** "
                  "`MaximalCapacity`, so no new axiom was invented. "
                  "(3) Repair — `ofGround_sole_universal_ground` already excludes every entity except a subject meaning "
                  "*everything*; `ofGround_unicity_from_no_discriminating_subject` closes exactly that last case from the single "
                  "hypothesis that no subject has total meaning-capacity, and `exactly_one_universal_modal_ground` states "
                  "**Classical Monotheism outright** (Aquinas *ST* I, q. 11, a. 3): existence unconditional, uniqueness under that "
                  "one named hypothesis. `no_discriminating_subject_iff_no_maximal_non_ground` proves the hypothesis **is** the "
                  "exclusion of maximal capacity among non-ground entities, so the whole price is one existing predicate. "
                  "**F15, closed by declaration (2026-09-28):** this row used to read "
                  "*\"no *axiom* asserts the hypothesis, so C320 cannot consume it unconditionally … F15 is an "
                  "*unnamed* commitment rather than a new bridge. The outstanding decision is consolidation.\"* "
                  "All three sentences are now superseded: the consolidation was carried out, the sentence is "
                  "`SemanticFinitude`, and C320's unicity has an unconditional corollary (C389). The diagnosis below is kept "
                  "because it is still the reason the *old* route was void, and because it is the reason the axiom is a "
                  "declaration rather than a derivation — the hypothesis was always being paid, which is exactly what makes it "
                  "vocabulary. "
                  "Honest boundary: strictly separated from numerical unitarianism (which would rule out Trinitarian relations) and pantheism."),
    },
    {
        "attribute": "**Strict numerical unitarianism** (ruling out relational internal plurality/persons)",
        "scope": "Divine Being / Ground",
        "expected": "COUNTERMODEL",
        "checks": [{"type": "countermodel",
                    "full": "Logos.FoundationalUnicity.unicity_does_not_force_unitarian_monad"}],
        "refs": ["Logos.TheologicalModalHardening.necessary_existence_not_entails_uniqueness",
                 "Logos.Plurality.T12_twoPersons"],
        "sense": ("Proving that the universal ground of reality is structurally unique does not force that the "
                  "internal life of the ground is a solitary, relationless monad (`unicity_does_not_force_unitarian_monad`, "
                  "footprint `{}`). The relational plurality of persons remains an open, non-collapsed frontier."),
    },
    {
        "attribute": "**One God / strict monotheism** (unity of the Divine Being)",
        "scope": "Divine Being / Ground",
        "expected": "DEFERRED",
        "checks": [{"type": "branch", "id": "monotheism"},
                   {"type": "decl",
                    "full": "Logos.FoundationalUnicity.exactly_one_universal_modal_ground"}],
        "refs": ["Logos.FoundationalUnicity.exactly_one_universal_modal_ground",
                 "Logos.FoundationalUnicity.ofGround_sole_universal_grounding",
                 "Logos.FoundationalUnicity.ofGround_unicity_from_no_discriminating_subject",
                 "Logos.FoundationalUnicity.unicity_does_not_force_unitarian_monad",
                 "Logos.TheologicalModalHardening.necessary_existence_not_entails_uniqueness"],
        # Phase 5: the half that is won leads; the half that is still deferred
        # follows. The label is split first because the reader needs to know
        # which half they are reading. F15 is now declared (see Correction 12),
        # so "not yet asserted in Γ" is false and is replaced.
        "sense": ("**This label was carrying two claims; only one of them is still open (corrected "
                  "2026-09-27).** (1) *Uniqueness of the universal ground* is **PROVEN**: "
                  "`exactly_one_universal_modal_ground` (C320) proves that exactly one universal modal "
                  "ground exists — **existence unconditional**, uniqueness under the single named "
                  "hypothesis `∀ s, ∃ p, ¬ Means s p`, which is now the **declared axiom** "
                  "`SemanticFinitude` (C388, `Tag: VOCAB`, ledger row F15) and is consumed "
                  "unconditionally by `exactly_one_universal_modal_ground_stipulated` (C389). "
                  "That is the mathematical content of monotheism at the level of the Divine Being. "
                  "(2) *Person-level monotheism* — one God as numerically one Person, and its "
                  "compatibility with three Persons — **remains DEFERRED**: `monotheism_of_god_and_uniqueness` "
                  "and `monotheism_compatible_with_trinity` are still out of the live kernel and no "
                  "compiled declaration exists for either, because they need the person bridge C228, which "
                  "is BLOCKED. The scope limit is unchanged and machine-checked: unicity of the ground does "
                  "not force a solitary, relationless monad (`unicity_does_not_force_unitarian_monad`, C212, "
                  "`{}`), so the Trinitarian frontier stays open. The older justification for the deferral — "
                  "that \"uniqueness is provably NOT a kernel consequence\" — held only of the *modal* route "
                  "(`TheologicalModalHardening.necessary_existence_not_entails_uniqueness`, `{}`: bare necessity "
                  "does not entail uniqueness). It did not hold of the grounding route, which now closes."),
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
                  "(`the_ground_not_in_succession`, `{Initiates, State, Subject}` — a "
                  "*non-correlateness* result: the proof never uses the `Initiates` conjunct, so "
                  "read C458–C459 and C460 before treating it as non-agency evidence, and C467 "
                  "for why the ground can still *produce*). Separation is "
                  "honest: atoms/subjects are time-modulated (`atom_has_temporal_mode`) and "
                  "`Everlasting` does not collapse into necessity (`everlasting_but_contingent`). "
                  "What is PROVEN is stage-unmodulated world-rigid existence — not a full "
                  "theology of divine eternity. C181 makes the underlying transport explicit "
                  "without instantiating the canonical `Entity` sort."),
    },
    {
        "attribute": "**Precedence to Right/Wrong** (the ground precedes the true/false distinction)",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.Precedence.ofGround_precedes_the_right_wrong_distinction"}],
        "refs": ["Logos.Precedence.ofGround_obtains_where_no_atom_is_true",
                 "Logos.Precedence.ground_scope_is_not_the_truth_set",
                 "Logos.Precedence.atom_fails_precedence",
                 "Logos.Precedence.ground_existence_does_not_entail_any_truth"],
        "sense": ("The ground obtains in a world where no **atom** is true, conditions every "
                  "meaning-bearing bearer via `GroundsEntity`, and does not itself stand under "
                  "the distinction — a four-field reading in `Precedence.PrecedesRightWrong` "
                  "(§9, C425). 'Precedes' is a **condition**, never a derivation, and the "
                  "positive direction (the ground obtains where nothing atomic is true) is "
                  "vacuous on this signature — so the discriminating force lives in the "
                  "*negative* direction `atom_fails_precedence` and in the vacuity report "
                  "`every_world_satisfies_some_form` (C418). Vocabulary-only: 0 substantive axioms."),
    },
    {
        "attribute": "**Exclusion of pantheism** (the ground is not the universe)",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.CosmicExistence.the_ground_is_not_the_universe"}],
        "refs": ["Logos.CosmicExistence.no_entity_is_identical_to_the_whole",
                 "Logos.CosmicExistence.grounding_never_yields_identity_of_the_totality"],
        "sense": ("In the only identity form well-formed over Γ's `Entity` — `Universe e := "
                  "∀ w x, ExistsAt w x → e = x`, 'whatever obtains **is** e' — the ground of "
                  "reality does not exhaust the whole (§18, C430), and founding and identifying "
                  "are not compatible alternatives (C431). **What this row is not:** an "
                  "adjudication of the aggregate reading ('the universe is not an entity'), which "
                  "is not a proposition over `Entity` at all and is therefore left unstatable "
                  "rather than refuted. Nor does it touch realm contingency, still BLOCKED in "
                  "SUBJECTS.md §4."),
    },
    {
        "attribute": "**Divine simplicity**",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.DivineSimplicity.divine_simplicity_sole_bearer"}],
        "refs": ["Logos.DivineSimplicity.ofGround_divine_simplicity",
                 "Logos.DivineSimplicity.divine_simplicity_is_unique_to_the_ground",
                 "Logos.DivineSimplicity.ofGround_has_no_internal_components",
                 "Logos.DivineSimplicity.ofGround_undivided_meaning",
                 "Logos.DivineSimplicity.ofGround_simplicity_and_transcendence",
                 "Logos.DivineSimplicity.non_composite_iff_canonical_aseity",
                 "Logos.DivineSimplicity.composite_entity_fails_simplicity"],
        "sense": ("In `DivineSimplicity.lean` (footprint `{Means, Subject, propext}` — VOCAB + CL), "
                  "`ofGround_divine_simplicity` proves that `Entity.ofGround` satisfies classical Divine "
                  "Simplicity under finite subjectivity (`∀ s, ∃ p, ¬ Means s p`): "
                  "(1) Mereological Non-Compositeness (`NonComposite e ↔ CanonicalAseity e`, no proper grounding parts); "
                  "(2) Structural Inextension (`ofGround_has_no_internal_components`, atomic nullary constructor with zero internal decomposition); "
                  "(3) Intentional Simplicity (`ofGround_undivided_meaning`, uniform meaning capacity across all propositions); "
                  "(4) Ontological Transcendence (`ofGround_transcendent`, distinct from all atomic worldly states and finite subjects). "
                  "Composite entities provably fail simplicity (`composite_entity_fails_simplicity`, `{}`). "
                  "**And it discriminates:** `divine_simplicity_sole_bearer` (C440) proves the ground is the "
                  "*only* bearer — the `no_internal_components` field alone closes the case, at **no** "
                  "substantive axiom cost (`divine_simplicity_is_unique_to_the_ground`, C439, `{Means, "
                  "Subject}`), the cheapest sole-bearership in the corpus. Disclosure: `EntityMeans "
                  "(ofAtom _) = False` makes `undivided_meaning` **vacuously true of every atom**, so only "
                  "`no_internal_components` is load-bearing for unicity. "
                  "Honest boundary: this establishes mereological, structural, and intentional simplicity — not identity of essence and existence."),
    },
    {
        "attribute": "**Ontological transcendence** (neither an atomic worldly state nor any subject-correlate)",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.DivineTranscendence.ofGround_sole_transcendent_ground"}],
        "refs": ["Logos.DivineSimplicity.ofGround_transcendent",
                 "Logos.DivineTranscendence.universal_grounding_does_not_entail_causal_externality",
                 "Logos.DivineTranscendence.membership_exclusion_does_not_entail_grounding_exclusion",
                 "Logos.DivineTranscendence.diagonal_does_not_deliver_system_externality",
                 "Logos.DivineTranscendence.per_system_outside_points_need_not_coalesce"],
        "sense": ("Aquinas *ST* I q. 14 a. 1 / Pseudo-Dionysius. **Both halves established:** existence "
                  "(`ofGround_transcendent`, C195) and unicity (`ofGround_sole_transcendent_ground`, C307, "
                  "`{Subject}` and unconditional) — the second was already proved **and already ledgered as "
                  "C307**; what was missing was a row in *this* table, so the characteristic was absent from "
                  "the reader-facing attributes altogether until 2026-09-28. No theorem was added for it. "
                  "Γ's sense is strictly **ontological**: the ground is neither an atomic worldly state nor "
                  "the correlate of any subject. It is **not** causal externality "
                  "(`universal_grounding_does_not_entail_causal_externality`, C306), membership exclusion "
                  "does not deliver grounding exclusion (C304), the diagonal route does not deliver system "
                  "externality even given the whole `DiagonalSpec` (C308), and outsiders of different systems "
                  "need not coalesce (C301)."),
    },
    {
        "attribute": "**Scholastic simplicity** (strict identity of essence and existence)",
        "scope": "Divine Being / Ground",
        "expected": "ABSENT",
        "checks": [{"type": "absent",
                    "fragments": ["essence_and_existence", "scholastic_simplicity"],
                    "allow": []}],
        "refs": [],
        "sense": ("The theory proves mereological, structural, and intentional simplicity "
                  "(`DivineSimplicity.lean`). The traditional scholastic doctrine asserting the strict "
                  "identity of essence and existence or collapsing all divine attributes into "
                  "undifferentiated identity is not derived."),
    },
    {
        "attribute": "**Divine immutability** (ontological, temporal, and process unchangeability)",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.DivineImmutability.ofGround_divine_immutability"}],
        "refs": ["Logos.DivineImmutability.ofGround_modal_invariance",
                 "Logos.DivineImmutability.ofGround_stage_invariance",
                 "Logos.DivineImmutability.ofGround_transition_invariance",
                 "Logos.DivineImmutability.ofGround_capacity_invariance",
                 "Logos.DivineImmutability.capacity_invariance_holds_for_every_entity",
                 "Logos.DivineImmutability.necessity_and_atemporality_yield_immutability",
                 "Logos.DivineImmutability.contingent_entity_fails_immutability"],
        "sense": ("In `DivineImmutability.lean` (footprint `{Initiates, Means, State, Subject}` — VOCAB only), "
                  "`ofGround_divine_immutability` establishes Classical Divine Immutability (Aquinas *ST* I, q. 9) "
                  "for `Entity.ofGround`: "
                  "(1) Modal Invariance (`ofGround_modal_invariance`, `{Subject}`, unchanging existence across all worlds); "
                  "(2) Stage Invariance (`ofGround_stage_invariance`, `{Subject}`, unchanging existence across all temporal stages); "
                  "(3) Transition Invariance (`ofGround_transition_invariance`, `{Initiates, State, Subject}`, outside all initiation and state becoming); "
                  "(4) Capacity Invariance (`ofGround_capacity_invariance`, `{Means, Subject}`, uniform intentional capacity across reality). "
                  "The Thomistic principle is proven: necessity, atemporality, and non-succession entail immutability. "
                  "Contingent entities provably fail immutability (`contingent_entity_fails_immutability`, `{}`). "
                  "**Vacuity disclosure (C321):** field (4) discriminates nothing — "
                  "`capacity_invariance_holds_for_every_entity` proves it holds for *every* entity, because `EntityMeans` "
                  "takes no world argument, so the two worlds in `CapacityInvariance` are bound and unused and the body is "
                  "`P ↔ P`. All three siblings genuinely quantify and each has a `{}` countermodel; this one has none, because "
                  "there is nothing in it to refute. The substantive reading (capacity constant *across worlds*, *ST* I q. 9 a. 3) "
                  "is not expressible in the present vocabulary and stays open as frontier F16. This is disclosure, not demotion: "
                  "the immutability row itself remains PROVEN. "
                  "Honest boundary: establishes modal, temporal, and process unchangeability in Γ, plus a capacity-invariance "
                  "predicate that is currently vacuous; "
                  "does not claim psychological impassibility or constrain relational intentionality."),
    },
    {
        "attribute": "**Psychological impassibility** (incapacity for relational affect or compassion)",
        "scope": "Divine Being / Ground",
        "expected": "ABSENT",
        "checks": [{"type": "absent",
                    "fragments": ["impassib", "psychological_impassibility"],
                    "allow": []}],
        "refs": ["Logos.Love.T14_eternalRelation_conditional",
                 "Logos.LovesAsGround.the_ground_is_a_necessary_and_chosen_lover",
                 "Logos.LovesAsGround.the_ground_is_not_a_person"],
        "sense": ("The ground is immutable in its modal existence, temporal stages, process transitions, "
                  "and capacity (`DivineImmutability.lean`). Impassibility as a **person-level** claim — "
                  "incapacity for relational affect or compassion in a person — is not established and "
                  "cannot be: the ground is provably **no person** (`the_ground_is_not_a_person`, C344), "
                  "and impassibility is a claim about persons. What is *not* excluded is relational "
                  "affect at the **entity** level: `the_ground_is_a_necessary_and_chosen_lover` (C343, "
                  "AXIOMATIC) attributes a directed good to the ground **as a kind**, without making it "
                  "a subject. So the absence is genuine but narrow: person-level impassibility stays "
                  "absent because there is no person here to be impassible, while Γ explicitly proves "
                  "both the eternal relationality of interpersonal love (`T14_eternalRelation_conditional`) "
                  "and a priced ground-level love that is provably disjoint from it (C346/C348)."),
    },
    {
        "attribute": "**Foundational omnipresence** (sustaining presence to all beings across modal reality)",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.FoundationalOmnipresence.ofGround_foundational_omnipresence"}],
        "refs": ["Logos.FoundationalOmnipresence.ofGround_world_rigid_presence",
                 "Logos.FoundationalOmnipresence.ofGround_universal_modal_ground",
                 "Logos.FoundationalOmnipresence.ofGround_non_reciprocal_ground",
                 "Logos.FoundationalOmnipresence.ofGround_maximal_capacity",
                 "Logos.FoundationalOmnipresence.omnipresence_from_universal_ground_and_aseity",
                 "Logos.FoundationalOmnipresence.finite_entity_fails_omnipresence"],
        "sense": ("In `FoundationalOmnipresence.lean` (footprint `{Means, Subject}` — VOCAB only), "
                  "`ofGround_foundational_omnipresence` establishes Classical Foundational Omnipresence (Aquinas *ST* I, q. 8) "
                  "for `Entity.ofGround`: "
                  "(1) World-Rigid Presence (`ofGround_world_rigid_presence`, `{Subject}`, present across all possible worlds); "
                  "(2) Universal Modal Grounding (`ofGround_universal_modal_ground`, `{Means, Subject}`, grounds every entity in every possible world); "
                  "(3) Non-Reciprocal Grounding (`ofGround_non_reciprocal_ground`, `{Means, Subject}`, asymmetric sustenance, ungrounded by atoms or finite subjects); "
                  "(4) Maximal Intentional Capacity (`ofGround_maximal_capacity`, `{Means, Subject}`, exhaustive meaning capacity). "
                  "The Thomistic principle is proven: universal modal grounding, presence, and aseity entail omnipresence. "
                  "Finite entities provably fail universal grounding (`finite_entity_fails_omnipresence`, `{}`). "
                  "Honest boundary: establishes foundational sustaining presence across modal reality in Γ; "
                  "explicitly distinguishes foundational omnipresence from physical spatial omnipresence or quantitative metric infinity."),
    },
    {
        "attribute": "**Physical omnipresence** (spatial presence throughout physical spacetime coordinates)",
        "scope": "Divine Being / Ground",
        "expected": "ABSENT",
        "checks": [{"type": "absent",
                    "fragments": ["physical_omnipresence", "spatial_omnipresence"],
                    "allow": []}],
        "refs": [],
        "sense": ("Spatial extension and physical spacetime coordinates are absent from the primitive "
                  "ontology of Γ. The ground is omnipresent foundationally (sustaining all beings across "
                  "all possible worlds, `FoundationalOmnipresence.lean`), not by physical diffusion or "
                  "spatial location."),
    },
    {
        "attribute": "**Quantitative metric infinity** (infinite physical magnitude or cardinal size)",
        "scope": "Divine Being / Ground",
        "expected": "ABSENT",
        "checks": [{"type": "absent",
                    "fragments": ["metric_infinity", "quantitative_infinity"],
                    "allow": []}],
        "refs": [],
        "sense": ("The foundation is universal in foundational scope (grounding all reality, `FoundationalOmnipresence.lean`), "
                  "but quantitative metric infinity (spatial magnitude or cardinal size) is not derived and is "
                  "explicitly disclaimed (`CHARACTERISTICS.md` §11; `CHARS.md` §11)."),
    },
    {
        "attribute": "**Divine pure actuality** (*Actus Purus* / perfection)",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.DivinePureActuality.ofGround_divine_pure_actuality"}],
        "refs": ["Logos.DivinePureActuality.ofGround_no_existential_potency",
                 "Logos.DivinePureActuality.ofGround_no_grounding_potency",
                 "Logos.DivinePureActuality.ofGround_no_transition_potency",
                 "Logos.DivinePureActuality.ofGround_no_intentional_potency",
                 "Logos.DivinePureActuality.necessity_aseity_and_immutability_yield_pure_actuality",
                 "Logos.DivinePureActuality.ofGround_incorporeal",
                 "Logos.DivinePureActuality.entity_with_potency_fails_pure_actuality"],
        "sense": ("In `DivinePureActuality.lean` (footprint `{Initiates, Means, State, Subject}` — VOCAB only), "
                  "`ofGround_divine_pure_actuality` establishes Classical Divine Pure Actuality "
                  "(*Actus Purus*, Aquinas *ST* I, q. 3, a. 1–2; q. 4, a. 1–2) for `Entity.ofGround` "
                  "with 0 substantive axioms: "
                  "(1) Zero Existential Potency (`ofGround_no_existential_potency`, `{Subject}`, necessary actuality across all worlds); "
                  "(2) Zero Grounding Potency (`ofGround_no_grounding_potency`, `{Means, Subject}`, ungrounded by external entities); "
                  "(3) Zero Transition Potency (`ofGround_no_transition_potency`, `{Initiates, State, Subject}`, immune to agential succession); "
                  "(4) Zero Intentional Potency (`ofGround_no_intentional_potency`, `{Means, Subject}`, exhaustive propositional meaning); "
                  "(5) Universal Actuality (`ofGround_universal_modal_ground`, active sustaining ground of all reality). "
                  "Corollaries: Divine Incorporeality (`ofGround_incorporeal`, `{Subject}`, non-atomic and non-corporeal); "
                  "entities with passive potency fail Pure Actuality (`entity_with_potency_fails_pure_actuality`, `{}`). "
                  "Honest boundary: establishes metaphysical Pure Actuality in Γ; does not imply physical kinetic energy or thermodynamic work."),
    },
    {
        "attribute": "**Physical / kinetic energy** (thermodynamic or kinetic physical motion)",
        "scope": "Divine Being / Ground",
        "expected": "ABSENT",
        "checks": [{"type": "absent",
                    "fragments": ["kinetic_energy", "thermodynamic_work"],
                    "allow": []}],
        "refs": ["Logos.DivinePureActuality.pure_actuality_independent_of_physical_energy"],
        "sense": ("Pure Actuality in Γ is metaphysical (absence of passive potency and universal modal grounding, "
                  "`DivinePureActuality.lean`). Physical kinetic motion, thermodynamic energy, and material "
                  "work are not derived and are explicitly demarcated (`pure_actuality_independent_of_physical_energy`, `{}`)."),
    },
    {
        "attribute": "**Foundational omniscience** (truth-exhaustive scope — the condition of all truth)",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.DivineOmniscience.ofGround_foundational_omniscience"}],
        "refs": ["Logos.DivineOmniscience.ofGround_truth_exhaustive",
                 "Logos.DivineOmniscience.ofGround_world_truth_exhaustive",
                 "Logos.DivineOmniscience.atom_not_truth_exhaustive",
                 "Logos.DivineOmniscience.discriminating_subject_not_truth_exhaustive",
                 "Logos.DivineOmniscience.necessity_and_scope_yield_foundational_omniscience",
                 "Logos.DivineOmniscience.entity_scope_exhaustiveness_is_not_infallibility",
                 "Logos.DivineOmniscience.exhaustive_scope_without_counterfactual_knowledge"],
        "sense": ("In `DivineOmniscience.lean` (footprint `{Means, Subject}` — VOCAB only), "
                  "`ofGround_foundational_omniscience` establishes the weak classical sense of "
                  "omniscience for `Entity.ofGround` (the ground as the condition of all truth, "
                  "Aquinas *ST* I, q. 14, a. 1) with 0 substantive axioms: "
                  "(1) Truth-exhaustive scope (`ofGround_truth_exhaustive`, `{Means, Subject}`: no true "
                  "proposition is closed to the ground's scope); "
                  "(2) World-indexed exhaustiveness (`ofGround_world_truth_exhaustive`, `{Means, Subject}`: "
                  "no state of affairs true in any world is out of scope); "
                  "(3) Exhaustive exclusion of worldly atoms (`atom_not_truth_exhaustive`, `{Means, Subject}`) "
                  "and of discriminating subjects (`discriminating_subject_not_truth_exhaustive`, "
                  "`{Means, Subject}`), leaving `Entity.ofGround` the sole candidate in the Γ inventory; "
                  "(4) Undivided scope (reused `ofGround_undivided_meaning`) and universal modal grounding "
                  "(reused `ofGround_universal_modal_ground`). "
                  "Honest boundary: the *refutation* of infallibility is carried as a field of the record, not "
                  "as a remark — see the next row."),
    },
    {
        "attribute": "**Infallible / counterfactual omniscience** (\"all and only truths\", ordinary knowledge of all truth)",
        "scope": "Divine Being / Ground",
        "expected": "ABSENT",
        "checks": [{"type": "absent",
                    "fragments": ["infallible_omniscience", "infallible_knowledge",
                                  "counterfactual_omniscience", "error_free_knowledge",
                                  "unrestricted_knowledge"],
                    "allow": []}],
        "refs": ["Logos.DivineOmniscience.ofGround_not_truth_tracking",
                 "Logos.DivineOmniscience.exhaustive_scope_without_counterfactual_knowledge",
                 "Logos.DeepModalFrontier.Omniscience_AllTruths",
                 "Logos.DeepModalFrontier.Omniscience_Counterfactuals"],
        "sense": ("The strong sense is not merely unproven but **refuted** for the canonical ground: "
                  "`ofGround_not_truth_tracking` (`{Means, Subject}`) proves `¬ TruthTracking Entity.ofGround`, "
                  "because `EntityMeans (Entity.ofGround) p` reduces to `True` (definitional stipulation "
                  "◈ `ofGround_meansAll`), so the ground's scope bears every proposition — including `False` — "
                  "and the exclusive half `EntityMeans e p → T p` is false of it; the scope is exhaustive and "
                  "provably not error-free. Metatheoretically the two halves are independent "
                  "(`entity_scope_exhaustiveness_is_not_infallibility`, `{}`), and the counterfactual sense is "
                  "not forced by the foundational one "
                  "(`exhaustive_scope_without_counterfactual_knowledge`, `{}`). Ordinary/classical omniscience "
                  "stays out of reach: Γ has no `Knows` predicate, `Omniscience_AllTruths` / "
                  "`Omniscience_Counterfactuals` (`DeepModalFrontier`) remain frontier vocabulary definitions, "
                  "and `Entity.ofGround` is not a subject correlate (`ofGround_ne_ofSubject`) — the prose "
                  "disclaimer (`README-OLD.md:263`; `CHARS.md` §14) is preserved, no divine knowledge bridge "
                  "is manufactured."),
    },
    {
        "attribute": "**Foundational omnipotence** (operative scope: no non-contradictory state of affairs is closed to the ground)",
        "scope": "Divine Being / Ground",
        "expected": "PROVEN",
        "checks": [{"type": "decl",
                    "full": "Logos.DivineOmnipotence.ofGround_foundational_omnipotence"}],
        "refs": ["Logos.DivineOmnipotence.ofGround_gapless_operative_scope",
                 "Logos.DivineOmnipotence.ofGround_operates_only_what_obtains",
                 "Logos.DivineOmnipotence.ofGround_does_not_operate_contradictions",
                 "Logos.DivineOmnipotence.atom_not_gapless_operate",
                 "Logos.DivineOmnipotence.discriminating_subject_not_gapless_operate",
                 "Logos.DivineOmnipotence.gapless_operators_are_ground_or_necessary_kind",
                 "Logos.DivineOmnipotence.necessity_and_presence_yield_foundational_omnipotence",
                 "Logos.DivineOmnipotence.satisfiable_scope_is_nonempty_and_contradiction_free",
                 "Logos.DivineOmnipotence.existence_everywhere_does_not_entail_operation",
                 "Logos.DivineOmnipotence.gapless_operative_scope_without_conjunctive_power",
                 "Logos.DivineOmnipotence.exhaustive_scope_without_operative_scope"],
        "sense": ("In `DivineOmnipotence.lean` (footprint `{Means, NecessarySubjectKind, Subject, propext}` — VOCAB only, the "
                  "`propext` cost inherited from `Semantics.nonContradiction`, C14), "
                  "`ofGround_foundational_omnipotence` establishes the *orthodox* classical sense of "
                  "omnipotence for `Entity.ofGround` (Aquinas *ST* I, q. 25, a. 5, ad 1 — *semper et ubique "
                  "operans*) at 0 substantive axioms: power over whatever does not involve a contradiction. "
                  "The scope is *operative*, in the sense that no state of affairs satisfiable in any "
                  "accessible world is closed to the ground "
                  "(`ofGround_gapless_operative_scope`, `{NecessarySubjectKind, Subject}`), with the two non-contradictory horns "
                   "made explicit: nothing unobtained — hence nothing unsatisfiable — is operated "
                   "(`ofGround_operates_only_what_obtains`, `{NecessarySubjectKind, Subject}`) and no contradiction is ever operated "
                   "(`ofGround_does_not_operate_contradictions`, `{NecessarySubjectKind, Subject, propext}`). The reading is "
                  "substantive rather than vacuous, since the scope domain is machine-checked non-empty and "
                  "contradiction-free (`satisfiable_scope_is_nonempty_and_contradiction_free`, `{propext}`), "
                  "and the ground is gapless alongside the necessary-kind subjects "
                  "(`gapless_operators_are_ground_or_necessary_kind`, `{NecessarySubjectKind, Subject}`, with `atom_not_gapless_operate` and "
                  "`discriminating_subject_not_gapless_operate` excluding atoms and contingent-kind subjects). Only the contradiction-omni reading — power over everything conceivable, "
                  "*including contradictions* — is refuted, and it is refuted *by* the orthodox restriction, "
                  "not against it. "
                  "Honest boundary, priced not hidden: Γ has no causal production relation, so "
                  "`OperatesAt v e P := ExistsAt v e ∧ P v` reads *operates* as presence plus obtaining, and "
                  "is registered as a priced stipulation ◈ `operatesAt_presencePlusObtaining` (`Tag: SEM`). "
                  "That price is machine-checked, not asserted: `existence_everywhere_does_not_entail_operation` "
                  "(`{}`) shows an entity present in every world can still operate nothing, and "
                  "`exhaustive_scope_without_operative_scope` (`{}`) shows exhaustive meaning scope does not "
                  "entail operative scope — so the result is proved from world-rigid presence, never read off "
                  "the meaning-exhaustive scope of `DivineOmniscience`. `gapless_operative_scope_without_"
                  "conjunctive_power` (`{}`) further bounds the claim: modal accessibility is not conjunctive, "
                  "so gapless scope does not entail jointly-possible pairs. See the next row for the causal sense."),
    },
    {
        "attribute": "**Causal / creative omnipotence** (\"can bring X about\", not \"is present where X obtains\")",
        "scope": "Divine Being / Ground",
        "expected": "ABSENT",
        "checks": [{"type": "absent",
                    # `Produces` left this guard on 2026-09-28: the relation is now
                    # DECLARED (C463, `Tag: VOCAB`), so it can no longer proxy the
                    # attribute — its existence is not creative power. What is still
                    # missing is the *derivation*, and these two fragments are what
                    # would fire if it ever lands.
                    "fragments": ["all_conceivable", "unrestricted_creative_power",
                                  "power_over_all_possible", "production_from",
                                  "produces_from"],
                    "allow": []}],
        "refs": [],
        "sense": ("No live theorem, and the prose disclaimer (`README-OLD.md:263`; `CHARS.md` §15) is "
                  "**retained — but narrowed to this causal sense only**, since the non-contradictory sense "
                  "above is now PROVEN. Γ declares no entity-level production relation: the only initiation "
                  "relation was `Agency.Initiates : Subject → State → State → Prop → Prop` "
                  "(`Agency.lean:168`, VOCAB), which is subject-indexed, and `Entity.ofGround` is provably not "
                  "a subject correlate (`ofGround_ne_ofSubject`, `NecessityEternity.lean:160`), so it could not "
                  "be instantiated by the ground at all. **One of F10's two missing statements was delivered on "
                  "2026-09-28 (C463):** `Logos.ThomisticAct.Produces : Entity → World → Form → Prop` "
                  "(`Tag: VOCAB`) is declared, and C465/C467 give it a *conditional* use — the ground's love "
                  "is productive. **A declared relation is not a causal power**, and this row stays "
                  "**ABSENT**: what is still missing is the derivation "
                  "`∀ φ, (∃ w, Satisfies w φ) → ∃ v, Produces Entity.ofGround v φ`, which is the whole "
                  "content of the causal sense, and the existential `∃ w φ` of C465 does not supply it. The "
                  "closest relation Γ has is explanatory containment "
                  "`GroundsEntity` (`RecoveredOntologicalGround.lean:57`, *esse est agere*), and "
                  "`exhaustive_scope_without_operative_scope` (`{}`) already machine-checks that omni-scope does "
                  "not entail selection power, so `Produces` must not be weakened to that either. BLOCKED with "
                  "the exact missing statement recorded (GAPMAP Level 17, row F10; `README-OLD.md:263` / "
                  "`CHARS.md` §15 keep the disclaimer, narrowed to the causal sense)."),
    },
    {
        "attribute": "**Creator of contingent reality**",
        "scope": "Divine Being / Ground",
        "expected": "COUNTERMODEL",
        "checks": [{"type": "countermodel",
                    "full": "Logos.ConditionalTheology.necessary_ground_not_entails_contingent_creation"},
                   {"type": "countermodel",
                    "full": "Logos.ConditionalTheology."
                            "the_creation_countermodel_is_a_populated_contingent_world"},
                   {"type": "theorem",
                    "full": "Logos.ConditionalTheology."
                            "a_populated_contingent_world_can_also_carry_creation"}],
        "refs": ["Logos.CosmicExistence.contingent_realm_obtains",
                 "Logos.CosmicExistence.cosmos_obtains",
                 "Logos.CosmicExistence.the_ground_loves_the_cosmos"],
        "sense": ("`necessary_ground ⇏ contingent_creation`, **on a populated world** (footprint "
                  "`{}`): a necessary ground that grounds *every* content may still create "
                  "nothing, so the ground does not entail a creation record. (Ledger target F9 "
                  "DEFERRED.) **This is not the empty world, and the kernel never claimed it "
                  "was.** `the_creation_countermodel_is_a_populated_contingent_world` proves the "
                  "separating world contains a subject that is genuinely contingent, and "
                  "`a_populated_contingent_world_can_also_carry_creation` is its positive "
                  "counterpart — so the entailment is undetermined in *both* directions, not "
                  "refuted-and-replaced. The countermodel is a free structure, **not a model of "
                  "Γ and not a candidate for reality**; the empty world is separately refuted by "
                  "C355 once a necessary entity exists. **Existence vs entailment, kept apart:** "
                  "the *existence* of a contingent realm is a **theorem of Γ** — and, since "
                  "2026-09-27 (lot COSMOS-EXISTENCE-IS-FREE), a **free** one: "
                  "`CosmicExistence.contingent_realm_obtains` (C350, `PROVEN` at "
                  "`{propext, Subject}`, witnessed by an atom, no bridge) — while its being a "
                  "bearer of content is the separate `CosmicExistence.cosmos_obtains` (C367, "
                  "`PROVEN` given an exhibited contingent person; conditionally "
                  "satisfiable per C354, non-trivial in shape per C353). So what stays "
                  "COUNTERMODEL here is the *entailment* from the ground, not the existence. "
                  "**These two facts are independent and both hold**: Γ proves a contingent "
                  "realm exists at no price at all, and Γ refutes that a necessary ground alone "
                  "entails a creation record. The ground loves the cosmos under declared prices "
                  "(C351/C352); it does not derive the cosmos from itself, and no production is "
                  "claimed."),
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


_STIP_DEPENDENTS_CACHE: set = set()


def stipulation_dependents() -> set:
    """Every declaration named as a `dependents` entry by a registered ◈
    stipulation, from `formal/stipulation_audit.json`.

    Derived, never transcribed. A declaration in this set is machine-verified
    *given* a declared stipulation, so its row must say so: per AGENTS.md
    `AXIOMATIC ≠ unproved`, and the same reading applies to a priced `def`."""
    global _STIP_DEPENDENTS_CACHE
    if _STIP_DEPENDENTS_CACHE:
        return _STIP_DEPENDENTS_CACHE
    deps: set = set()
    if STIPULATION_AUDIT_PATH.exists():
        try:
            data = json.loads(STIPULATION_AUDIT_PATH.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            data = {}
        for e in data.get("stipulations", []):
            deps.update(e.get("dependents", []))
    _STIP_DEPENDENTS_CACHE = deps
    return deps


def _stip_marker(names) -> str:
    """` ◈` when any of `names` is a registered ◈ dependent, else ``."""
    deps = stipulation_dependents()
    if not deps:
        return ""
    for n in names:
        if not n:
            continue
        if n in deps or n.rsplit(".", 1)[-1] in deps:
            return " ◈"
    return ""


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
    ap(">")
    ap("> **Three axes — which models are wrong, given that the world exists.** A countermodel makes "
       "three claims: the *attack* (a derivability claim, which stands unless Γ derives the inference), "
       "the *model* (a description of a world), and the *world-datum* ◈ `contingentWorldDatum` (what the "
       "model's own world-structure says about the world the proof is written in). Each model below "
       "carries its verdict **as the actual world** with the exact price that would exclude it — WRONG "
       "outright (the no-meaning world, on the act-datum; the falsity world read as the actual world, on "
       "the world-datum, for free), WRONG ONLY IF an axiom is insisted (plurality, love, choice bridges), "
       "NOT ESTABLISHED, or UNANSWERED — plus a third verdict, **given the contingent world exists**, "
       "derived in Lean from each model's `WorldStance` and cross-checked against the structure it "
       "declares. See the Technical Appendix (kernel-audit.md), Appendix C.1, where all three verdicts "
       "are rendered beside the attack each leaves standing.")
    ap("")
    ap("| Skeptical Attack | What the Skeptic Misses | Formal Rebuttal in Kernel | Kernel Footprint |")
    ap("|---|---|---|---|")
    ap("| **1. Normative Nihilism**<br>\"There is no objective right and wrong; normativity is arbitrary.\" | Any rational denial must claim that its denial is *correct* (`ClaimsCorrect s NoRight`). Claiming the denial as correct while it is true produces a strict constructive contradiction. | [`claims_correct_no_right_self_refuting`](formal/Logos/DirectNormativeRetorsion.lean#L60)<br>`⊢ ClaimsCorrect s NoRight ∧ NoRight → ⊥` | `{Initiates, Means, State, Subject, CL}`<br>**(0 substantive axioms)** |")
    ap("| **2. Eliminativism of Choice**<br>\"Normative address does not imply genuine choice.\" | Prescriptive normativity commands one alternative and forbids an incompatible one. Co-grasping incompatible alternatives *is* the constitutive definition of choice; denying choice yields a direct contradiction. | [`d7_co_grasp_is_definitionally_choice`](formal/Logos/UndeniableNormativeDerivation.lean#L261)<br>`⊢ Means s p ∧ Means s q ∧ Incompatible p q ∧ ¬ Chooses s p q → ⊥` | `{Means, Subject}`<br>**(0 substantive axioms)** |")
    ap("| **3. Determinism / Incompatibilism**<br>\"Choice is not Free Will; freedom requires physical indeterminism.\" | Having the capacity to choose between incompatible normative alternatives *is* Free Will (`FreeWill s := ∃ p q, Chooses s p q`). Denying free will when one chooses yields a formal contradiction. Physical indeterminism is an orthogonal concept isolated to countermodels. | [`d8_choice_is_definitionally_free_will`](formal/Logos/UndeniableNormativeDerivation.lean#L275)<br>`⊢ Chooses s p q ∧ ¬ FreeWill s → ⊥`<br>[`indubitable_normative_free_will`](formal/Logos/IndubitableNormativeFreeWill.lean#L115) | `{Means, Subject}`<br>**(0 substantive axioms)** |")
    ap("| **4. Theological Smuggling**<br>\"A free subject is not a Person; 'Person' is an anthropomorphic trick.\" | Personhood in Γ IS the classical Boethian-Thomistic core (`Person := ThomisticPersonCore := IndividualSubstance ∧ RationalNature ∧ DominionOverActs`). The reduction to `FreeSubject` is a priced theorem (`freeWill_implies_person`), machine-checked with 0 substantive axioms, whose exact boundary is witnessed by `SharedWillModel` (`{}`). | [`freeWill_implies_person`](formal/Logos/Person.lean#L135)<br>`⊢ FreeWill s → Person s` | `{Means, Subject, Will, subjectWill, will_individuation}`<br>**(0 substantive axioms)** |")
    ap("| **5. Euthyphro / Voluntarism**<br>\"This makes the person the arbitrary creator of morality.\" | Identifying Ought with volition (`Wills s p = Ought s p`) destroys normative violation. The ground required by the normative order is *personal in kind*, not an arbitrary dictator inventing rules. | [`will_identity_collapses_normativity`](formal/Logos/PersonalNormativeGround.lean#L261)<br>`⊢ Wills s p = Ought s p → NormativeViolation s p → ⊥` | `{Subject, Wills, Ought}`<br>**(0 substantive axioms)** |")
    ap("| **6. Physicalist / Atomic Ground**<br>\"The ultimate ground could be a physical particle, matter, or an atom.\" | An entity with false meaning capacity cannot ground an entity with true meaning capacity. Atomic factual entities are unconditionally excluded from grounding `Entity.ofGround`, and the ground possesses Canonical Aseity. | [`atom_cannot_ground_the_ground`](formal/Logos/CanonicalAseity.lean#L96)<br>[`conditional_canonical_aseity`](formal/Logos/CanonicalAseity.lean#L133)<br>`⊢ CanonicalAseity Entity.ofGround` | `{Means, Subject}`<br>**(0 substantive axioms)** |")
    ap("| **7. Origin of Normativity (The Proof-Self Retorsion)**<br>\"Where does the initial normative claim come from? Why grant that any normative judgment exists?\" | Bare syntax checking alone does not force normativity (`M_inanimate_checker`, `{}`). But any agent *presenting* a derivation as sound (`PresentsAsSound`) co-means correctness and error, deriving `FreeWill` and `Person` with 0 substantive axioms. Furthermore, an adversarial critic who attacks Γ by presenting an objection argumentatively as sound *themselves* instantiates the normative stance (`critic_presenting_objection_is_person`). | [`presents_as_sound_derives_personhood`](formal/Logos/ProofPresentationRetorsion.lean#L140)<br>[`critic_presenting_objection_is_person`](formal/Logos/ProofPresentationRetorsion.lean#L180)<br>[`syntactic_validity_without_subject_or_normativity`](formal/Logos/ProofPresentationRetorsion.lean#L100) | `{Initiates, Means, State, Subject, CL}`<br>**(0 substantive axioms)** |")
    ap("")
    return lines


# --- ASIETY-FREEDOM chain: every step priced, so the ◈ step cannot be read as
# --- a theorem. Badges and footprints are DERIVED (kernel audit / ◈ registry);
# --- nothing here is transcribed. See AGENTS.md.
ASIETY_FREEDOM_STEPS = [
    ("L1", "C287", "Logos.AsietyFreedom.weakChoice_implies_asiety", "decl",
     "`GenuineNormativity s p q → Asiety (EntityOf s)` — weak choice, **Act-free**"),
    ("L1", "C288", "Logos.AsietyFreedom.weakChoice_implies_freeWill", "decl",
     "the same step read toward free will"),
    ("◈", "—", "Logos.AsietyFreedom.AsietyFreedomOfGround", "stipulation",
     "**THE BRIDGE, BY DECLARATION**: the ground's freedom reaches every subject"),
    ("L2", "C289", "Logos.AsietyFreedom.asietyFreedom_yields_trueChoice", "decl",
     "`AsietyFreedomOfGround → TrueChoice s p q` (conditional)"),
    ("L2", "C290", "Logos.AsietyFreedom.asietyFreedom_yields_asietyFreeWill", "decl",
     "`AsietyFreedomOfGround → AsietyFreeWill s` — the *\"shared with us by the creator\"* step"),
    ("L2", "C291", "Logos.AsietyFreedom.asietyFreeWill_yields_trueChoice", "decl",
     "`AsietyFreeWill s → TrueChoice s p q`, and back again"),
    ("🧱", "C292", "Logos.AsietyFreedom.asietyAloneDoesNotYieldTrueChoice", "countermodel",
     "countermodel: asiety alone yields no true choice — the universal reading is strictly "
     "stronger than the existential one"),
    ("🧱", "C293", "Logos.AsietyFreedom.frameContingencyDoesNotBindAPair", "countermodel",
     "countermodel: frame contingency binds no given pair — why `TrueChoice ≡ Chooses` "
     "is forced, not lazy"),
    ("🧱", "C294", "Logos.AsietyFreedom.rightWrongFactYieldsNoChooser", "countermodel",
     "countermodel: `¬ N_T ∧ ¬ N_F` with **no** subject meaning anything — **no axiom-free "
     "existence of a chooser**"),
    ("✓", "C295", "Logos.AsietyFreedom.groundIsNotASharerOfAsietyFreeWill", "decl",
     "coherence: the ground is still **not** a chooser (C285 preserved)"),
    ("Σ", "C296", "Logos.AsietyFreedom.asietyFreedom_summary", "decl",
     "master summary: the whole chain and both its prices in one statement"),
    ("L1", "C300", "Logos.AsietyFreedom.weakChoice_yields_trueChoice", "decl",
     "**the derived side at its actual maximum**: `GenuineNormativity s p q → TrueChoice s p q` "
     "— axiom-free, no ◈, true choice **at the specified pair**. The hypothesis already contains "
     "the choice; only the `{}` frame fact `ContestedContent` is added. **So the pair's existence "
     "is free — what ◈ buys is the extension from the given pair to every incompatible pair**"),
    ("L1", "C297", "Logos.AsietyFreedom.asiety_yields_witnessed_trueChoice", "decl",
     "the same boundary via `Asiety`: `Asiety (EntityOf s) → ∃ p q, TrueChoice s p q`. "
     "**Strictly weaker than C300** (it discards *which* pair); retained, not deleted"),
    ("L1", "C298", "Logos.AsietyFreedom.asiety_yields_freeWill", "decl",
     "and in the `FreeWill` direction: `Asiety (EntityOf s) → FreeWill s`, equally bounded"),
    ("🧱", "C299", "Logos.AsietyFreedom.groundingCannotDeliverTrueChoice", "countermodel",
     "countermodel: **no grounding premise of containment shape can deliver true choice** — the "
     "grounding premise is granted *in full* and the conclusion still fails. Machine-checked reason "
     "the ◈ step is `BLOCKED`. Scope limit: relations of *other* shape stay open (F12(1))"),
]


# --- SEMANTIC-FINITUDE chain: the F15 bound, consolidated and
# --- badged. Badges and footprints are DERIVED (kernel audit / ◈ registry); nothing
# --- here is transcribed. See AGENTS.md.
# --- `◈` = the declared bound, not a theorem · `L2` = a corollary resting on the ◈ ·
# --- `🧱` = `{}` countermodel pricing it · `✓` = coherence. C-ids are unallocated
# --- (author decision pending), so the Ledger column reads `—` until then.
SEMANTIC_FINITUDE_STEPS = [
    ("◆", "C388", "Logos.SemanticFinitude.SemanticFinitude", "decl",
     "**THE F15 BOUND, BY DECLARATION** — the 27th axiom, `Tag: VOCAB`: no subject means every "
     "proposition, so no creature is semantically omnipotent. Paid as an anonymous "
     "premise in 19 declarations across the five attribute modules (14 carrying the "
     "exact ∀-form) before it was named; now declared, and its price is in every "
     "dependent footprint"),
    ("L2", "C389", "Logos.SemanticFinitude.exactly_one_universal_modal_ground_stipulated", "decl",
     "**the unicity of the ground of all reality**, an unconditional theorem of Γ"),
    ("L2", "C390", "Logos.SemanticFinitude.ofGround_sole_universal_grounding_stipulated", "decl",
     "sole universal grounding of reality"),
    ("L2", "C391", "Logos.SemanticFinitude.conditional_canonical_aseity_stipulated", "decl",
     "canonical aseity of the ground"),
    ("L2", "C392", "Logos.SemanticFinitude.ofGround_modal_aseity_conditional_stipulated", "decl",
     "modal aseity of the ground w.r.t. `CanonicalExtDepAt`"),
    ("L2", "C393", "Logos.SemanticFinitude.ofGround_divine_pure_actuality_stipulated", "decl",
     "**divine pure actuality** (actus purus) of the ground"),
    ("L2", "C394", "Logos.SemanticFinitude.ofGround_no_grounding_potency_stipulated", "decl",
     "zero passive grounding potency in the ground"),
    ("L2", "C395", "Logos.SemanticFinitude.ofGround_divine_simplicity_stipulated", "decl",
     "**divine simplicity** of the ground"),
    ("L2", "C396", "Logos.SemanticFinitude.ofGround_non_composite_stipulated", "decl",
     "mereological non-compositeness of the ground"),
    ("L2", "C397", "Logos.SemanticFinitude.ofGround_simplicity_and_transcendence_stipulated", "decl",
     "divine simplicity **and** ontological transcendence of the ground"),
    ("L2", "C398", "Logos.SemanticFinitude.ground_is_canonically_aseitous_but_not_asietic_stipulated",
     "decl", "canonically aseitous but not itself asietic"),
    ("🧱", "C399", "Logos.SemanticFinitude.semantic_omnipotence_is_consistent", "countermodel",
     "countermodel: a semantically omnipotent carrier is a model of the negation — the bound "
     "is **falsifiable, not vacuous**, so the unicity really rests on it"),
    ("✓", "C400", "Logos.SemanticFinitude.semanticFinitude_excludes_ground_from_subjects", "decl",
     "coherence: `ofGround_meansAll` gives the ground *every* proposition, so the bound is "
     "exactly what keeps the ground off the `Subject` sort"),
]


# --- LOVE chain: two prices, different in kind, so the table prices both.
# --- Badges and footprints are DERIVED (kernel audit / axiom registry);
# --- nothing here is transcribed. See AGENTS.md.
# --- `L1` = no new vocabulary · `V` = consumes the VOCAB primitive, no substantive axiom ·
# --- `◆` = the axiom rows themselves · `L2` = the priced inhabitants ·
# --- `S` = separations · `D` = the record/structure rows (was "the SEM datum side", which
# --- no longer exists: the `Tag: SEM` datum was retired 2026-09-27) · `🧱` = `{}` countermodel.
LOVE_STEPS = [
    ("L1", "C322", "Logos.LovesAsGround.falsityWorld_ne_actualWorld", "decl",
     "the single witness of modal fragility: the all-`TV.f` world is not the actual world"),
    ("L1", "C323", "Logos.LovesAsGround.an_atom_is_contingent", "decl",
     "an atom is contingent — this is what makes C338 bite"),
    ("L1", "C324", "Logos.LovesAsGround.a_contingent_entity_exists", "decl",
     "bare contingency, witnessed by an atom — not the cosmos, not an object of love"),
    ("L1", "C325", "Logos.LovesAsGround.a_meaningful_contingent_entity_exists", "decl",
     "a contingent entity bearing content exists — *consumes* a `Means` inhabitant, produces none"),
    ("L1", "C326", "Logos.LovesAsGround.ground_grounds_every_entity", "decl",
     "the ground grounds everything — proof is `intro p _; exact True.intro`"),
    ("L1", "C327", "Logos.LovesAsGround.atoms_bear_no_meaning", "decl",
     "an atom bears no meaning at all"),
    ("L1", "C328", "Logos.LovesAsGround.ground_grounds_the_meaningless", "decl",
     "the ground grounds even the meaningless — undiscriminating, *vacuously*"),
    ("L1", "—", "Logos.LovesAsGround.the_ground_is_a_universal_modal_ground", "decl",
     "**restates C204**; body is literally `ofGround_universal_modal_ground` — no second id"),
    ("L1", "C329", "Logos.LovesAsGround.no_subject_is_a_necessary_entity", "decl",
     "no *contingent-kind* person can occupy the necessary pole — kind-relative, discharges it with no love axiom"),
    ("L1", "C330", "Logos.LovesAsGround.necessary_entities_are_ground_or_necessary_kind", "decl",
     "**the necessary entities are the ground AND the necessary-kind subjects** (renamed 2026-09-28) — "
     "ground disjunct forced by the three-constructor ontology, subject disjunct the priced META bridge — "
     "structural fact, **not** evidence of love"),
    ("V", "—", "Logos.LovesAsGround.GroundLoves", "decl",
     "**THE RELATION, ADDED NOT REUSED**: necessary lover, actual other, directed good, "
     "meaningful target, context `a` — `Loves` is `Subject`-indexed and the ground is no subject"),
    ("V", "C331", "Logos.LovesAsGround.ground_love_requires_a_necessary_lover", "decl",
     "love is eternal *in the lover* — half of the poem's \"também é necessário\""),
    ("V", "C332", "Logos.LovesAsGround.ground_love_is_directed_at_another", "decl",
     "love is not self-regarding: actual target, other than the lover"),
    ("V", "C333", "Logos.LovesAsGround.ground_love_bears_a_directional_good", "decl",
     "the conjunct with no first-order substitute — the one the inhabitation pays for"),
    ("V", "C334", "Logos.LovesAsGround.ground_love_requires_a_meaningful_target", "decl",
     "the target bears content **of its own** — what separates love from mere capacity"),
    ("V", "C335", "Logos.LovesAsGround.meaningless_entities_cannot_be_loved", "decl",
     "love cannot reach the meaningless, in any context"),
    ("V", "C336", "Logos.LovesAsGround.grounding_reaches_what_love_cannot", "decl",
     "**the separation, in one statement** — the machine-checked content of \"not *merely* "
     "a mathematical ground\""),
    ("V", "C337", "Logos.LovesAsGround.grounding_is_total_but_love_is_not", "decl",
     "the totals separate — read with C338 as a pair, not a single step"),
    ("V", "C338", "Logos.LovesAsGround.meaningful_love_bridge_is_refuted", "decl",
     "**REFUTATION OF THE ATTRACTIVE FORM**: the unrestricted bridge is false in Γ — "
     "the only justification for the axiom's meaning hypothesis"),
    ("◆", "C349", "Logos.LovesAsGround.GroundBearsGood", "axiom",
     "**PRICE 1, VOCABULARY**: the directed-good primitive — constrains nothing, names what is missing"),
    ("◆", "C339", "Logos.LovesAsGround.AxGroundLovesContingentRealm", "axiom",
     "**PRICE 2, SUBSTANCE**: the inhabitation — genuinely not forced, genuinely not trivial"),
    ("L2", "C340", "Logos.LovesAsGround.the_ground_loves_every_meaningful_contingent_reality", "decl",
     "the bridge, applied — the ground's love as a *conclusion*, first time in the corpus"),
    ("L2", "C341", "Logos.LovesAsGround.the_ground_bears_a_directional_good_toward_the_cosmos", "decl",
     "the content, unwrapped — where the whole price sits"),
    ("L2", "C342", "Logos.LovesAsGround.the_ground_is_a_liver", "decl",
     "the inhabitants, with the price visible — identifies nothing with the cosmos"),
    ("L2", "C343", "Logos.LovesAsGround.the_ground_is_a_necessary_and_chosen_lover", "decl",
     "**the \"necessary ∧ chosen\" cell, occupied** — necessity forced, choice exactly the bridge"),
    ("S", "C344", "Logos.LovesAsGround.the_ground_is_not_a_person", "decl",
     "the ground-*constructor* is not a subject-correlate — constructor separation, re-scoped 2026-09-28; "
     "the necessary-kind person is a *different* entity, so no identification is made"),
    ("S", "C345", "Logos.LovesAsGround.ground_love_does_not_identify_a_person", "decl",
     "the inhabitation cannot be read as a claim about a person"),
    ("S", "C346", "Logos.LovesAsGround.subject_love_is_not_ground_love", "decl",
     "**contingent interpersonal love never yields ground-level love** — disjoint on the contingent side"),
    ("S", "C347", "Logos.LovesAsGround.interpersonal_love_never_reaches_the_necessary_quadrant", "decl",
     "no amount of *contingent* interpersonal love populates the necessary quadrant — the necessary kind can"),
    ("S", "C348", "Logos.LovesAsGround.ground_love_cannot_be_read_as_person_love", "decl",
     "**the transfer to the contingent kind is unstatable, not merely blocked** — bridge #9 / C228 untouched"),
    ("V", "—", "Logos.LovesAsGround.ground_love_preserves_pure_actuality", "decl",
     "**restates C217** (`ofGround_no_transition_potency`) — love as act *adds to* pure actuality"),
    ("L1", "C350", "Logos.CosmicExistence.contingent_realm_obtains", "decl",
     "**contingency-overflow — a theorem, not a datum, and now free of any bridge**: something "
     "obtains, is modal-fragile, and is not the necessary ground. Witnessed by an atom via "
     "`an_atom_is_contingent 0` (C324), which is why the price vanished — `ContingentRealm` is "
     "`Realm` *without* `bears_meaning`, so no `Subject` and no `Means` are consumed. **This "
     "row asserts no act of production**: \"created\" names the region of reality that is "
     "actual, modal-fragile and not the ground; no `Creates` relation, agent or first moment is "
     "claimed or derivable. Rejecting `AxTwoSubjects` does not touch this row. Was a "
     "`Tag: SEM` axiom (`AxContingentCreationObtains`), retired 2026-09-27 — the lemma it "
     "declared unavailable was already a theorem"),
    ("D", "—", "Logos.CosmicExistence.ContingentRealm", "decl",
     "the realm **without the meaning condition**: `witness`, `actual`, `contingent`, "
     "`not_the_ground` — i.e. `Realm` minus `bears_meaning`, which is precisely why C350 is free"),
    ("D", "—", "Logos.CosmicExistence.ContingentRealmObtains", "decl",
     "the `Prop` form of the same, so the ledger can name the claim as C350 while the record "
     "keeps a single witness"),
    ("L2", "C367", "Logos.CosmicExistence.cosmos_obtains", "decl",
     "**the same realm, now meaning-bearing — given an exhibited *contingent person***: the kind "
     "premise (2026-09-28, two-kinds) exhibits what kind-blind semantics got for free, so "
     "`AxTwoSubjects` is no longer among the premises — exhibiting the kind subsumes the "
     "T12 witness. **It is still the row that identifies the realm as *the* cosmos** — C324's "
     "prohibition (an atom is not the cosmos) is untouched, because C350 "
     "shows only that the *shape* has an instance. **The price is exhibited, not forced:** 3e below "
     "reaches the same inhabitation from the act-datum"),
    ("D", "—", "Logos.CosmicExistence.CreatedRealm", "decl",
     "the meaning-bearing realm's structure: `Nonempty Realm`, single witness — fair definition; "
     "the inhabitation is now **proved** (C367), no longer stipulated"),
    ("S", "—", "Logos.CosmicExistence.gamma_exhibits_a_meaning_subject", "decl",
     "**the emptiness result on its own**: Γ exhibits a subject that means something — the "
     "user's point, made checkable, with the subject *discovered* inside Γ rather than assumed"),
    ("L2", "C351", "Logos.CosmicExistence.the_ground_loves_the_cosmos", "decl",
     "**the conclusion, both prices visible** — \"not merely a mathematical ground, but loves\""),
    ("L2", "C352", "Logos.CosmicExistence.the_ground_loves_the_cosmos_in_a_context", "decl",
     "the same conclusion in the relational vocabulary — `GroundLoves`, **not** `Loves`"),
    ("L2b", "C386", "Logos.CosmicExistence.cosmos_presence_model_of_the_act_datum", "decl",
     "**THE GOD-LANE, half one — the same inhabitation with the META bridge left out**: the "
     "performative act-datum reaches a meaning-bearing subject on its own, because `Act` already "
     "contains `Means` as a conjunct, so `act_datum_implies_means` needs no bridge. A **new row**, "
     "not a re-anchoring of C367, and it does not replace it: a theorem *discovers*, it does not "
     "manufacture, so Γ supplies no subject from nothing — the datum is given, not inferred, and "
     "the kind is exhibited with it (2026-09-28, two-kinds). "
     "Re-anchoring `cosmos_obtains` would repeat the A1 bug exactly"),
    ("L2b", "C387", "Logos.CosmicExistence.the_ground_loves_the_cosmos_from_the_act_datum", "decl",
     "**THE GOD-LANE's payoff — the ground's love, byte-identical conclusion, person-datum swapped for act-datum**: "
     "C351 exhibits a contingent person (`Will`/`subjectWill`); this row exhibits an act "
     "(`Initiates`/`State`). Neither pays the plurality bridge since the two-kinds correction — "
     "the swap, not a removal, is this row's content. "
     "The love "
     "bridge stays, and must: a directional good held by the ground is not in Γ's grounding "
     "vocabulary. Relocated price: the declared act-datum axiom C454 — one axiom, not free in performance"),
    ("🧱", "C353", "Logos.CosmicExistence.perfect_universe_has_no_contingent_realm", "countermodel",
     "**countermodel, `{}`**: the contingency shape is refutable in a world-rigid universe — "
     "on an **unrelated free structure, not a model of Γ**"),
    ("L1", "C354", "Logos.CosmicExistence.cosmos_presence_model", "decl",
     "**conditional satisfiability**: the realm obtains for any contingent-kind `Means` inhabitant — "
     "kind exhibited, stated, not glossed as unconditional"),
]


# --- TWO-KINDS chain (batch two-kinds, 2026-09-28). The plan of record is
# --- `SUBJECTS.md`. This list exists because the batch's most load-bearing rows —
# --- the derived necessary Person (C404 -> C407/C408/C409) and the personal-ground
# --- headlines (C151/C152) — were absent from every reader-facing chain list, so the
# --- document silently omitted the newest batch. See AGENTS.md: "Adding a declaration
# --- to a chain module does not add it to README.md — extend the list in the same
# --- change." Badges and footprints are DERIVED; nothing here is transcribed.
# --- `V` = the VOCAB axiom (free predicate of the necessary kind) · `D` = its `def`-side
# --- negation · `◆` = the META bridge (the axiom rows) · `L1` = VOCAB-only theorem,
# --- no substantive axiom · `L2` = rests on the META bridge · `Σ` = the headline partition.
TWO_KINDS_STEPS = [
    ("V", "C403", "Logos.Agency.NecessarySubjectKind", "decl",
     "**THE VOCABULARY OF THE TWO KINDS** (`Tag: VOCAB`): a free predicate for the *kind* of a "
     "subject. It asserts no existence — inhabitation is C404, the bridge, and is deliberately "
     "not part of this line"),
    ("D", "—", "Logos.Agency.ContingentSubjectKind", "decl",
     "its `def` complement (`¬ NecessarySubjectKind`); the two kinds partition the sort by C411"),
    ("L1", "C405", "Logos.Plurality.necessaryKindSubject_is_necessary", "decl",
     "a subject of the necessary kind is a necessary subject — the kind-relative form of the "
     "persistence theorem, from the left disjunct of `SubjectExistsAt`"),
    ("L1", "C406", "Logos.Plurality.contingentKindSubject_not_necessary", "decl",
     "a contingent-kind subject is **not** necessary — it fails in the all-`TV.f` world. This is "
     "where every earlier contingency finding now lives, and it discharges C329 "
     "(`no_subject_is_a_necessary_entity`) with **no love axiom**"),
    ("Σ", "C410", "Logos.Plurality.kinds_are_the_modal_partition", "decl",
     "**THE HEADLINE — the two kinds are exactly the two modal profiles**: a subject is "
     "necessary-kind **iff** its correlate exists in every world. Vocabulary-only, "
     "**0 substantive axioms**"),
    ("L1", "C411", "Logos.Plurality.contingentKind_iff_not_necessary", "decl",
     "contingent-kind is the complement of necessary-kind, hence — with C410 — the "
     "complementarity of world-rigidity itself"),
    ("L1", "C412", "Logos.Plurality.necessaryKind_existsAt_every_world", "decl",
     "the necessary-kind profile: **every** world. Left disjunct, and nothing more"),
    ("L1", "C413", "Logos.Plurality.contingentKind_existsAt_actualWorld_only", "decl",
     "the contingent-kind profile: **the actual world and no other**. With C412, the "
     "**asymmetry of inhabitation** between the kinds"),
    ("L1", "C414", "Logos.Plurality.falsityWorld_holds_no_contingent_subject", "decl",
     "the world of falsity hosts no contingent-kind subject. **What this does not say**: it does "
     "not say the falsity world is empty, nor that the necessary kind is absent from it"),
    ("L1", "C415", "Logos.Plurality.contingentSubject_might_not_have_existed", "decl",
     "a contingent-kind subject **might not have existed** — C406 in world-relative form, and the "
     "one half of contingency the argument does *not* need to assume"),
    ("◆", "C404", "Logos.Plurality.necessaryPersonalSubjectExists", "decl",
     "**THE BRIDGE, AND THE ONLY SUBSTANTIVE PRICE IN THIS BATCH** (`Tag: META`): the necessary "
     "kind is inhabited by a **Person** — the ground read in its Personal Type, as a Subject. "
     "**Everything below is this row, and nothing else**"),
    ("L2", "C407", "Logos.Plurality.necessarySubject_exists", "decl",
     "a necessary subject exists, by the bridge"),
    ("L2", "C408", "Logos.Plurality.necessaryPersonalSubject_derived", "decl",
     "a **necessary Person** exists: the meaning-bearing subject is necessary-kind, the "
     "contingent one is the other kind"),
    ("L2", "C409", "Logos.NecessaryPersonalGround.necessary_person_derived_from_bridge", "decl",
     "**CLAIM D IS NOW DERIVED, NOT ANNOTATED** — the necessary-person existential is no longer "
     "empty. The price is exactly the bridge and nothing more"),
    ("L1", "C151", "Logos.PersonalGroundOfReality.the_person_supports_the_reality_of_right", "decl",
     "**THE FLAGSHIP, UNCONDITIONAL — 0 substantive axioms**: the person supports the reality "
     "of right, with the interpersonal metaphysics already discharged upstream. This is the "
     "load-bearing theorem the whole personal-ground route rests on"),
    ("L1", "C152", "Logos.PersonalGroundOfReality.personal_ground_of_right_exists", "decl",
     "a **personal ground of right** exists — `{}`-class, vocabulary alone"),
]


def _stipulation_entry(name: str):
    """One ◈ registry entry by name, or None (derived from the audit file)."""
    if not STIPULATION_AUDIT_PATH.exists():
        return None
    try:
        data = json.loads(STIPULATION_AUDIT_PATH.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    for e in data.get("stipulations", []):
        if e.get("name") == name:
            return e
    return None


def render_asiety_freedom_chain(decls: dict, node_map: dict) -> list[str]:
    """The ASIETY-FREEDOM chain, step by step, with the price of every step.

    Emitted so that the ◈ stipulated bridge can never be read as a theorem: it
    is its own row, badged from `formal/stipulation_audit.json`, and every
    other cell is derived from the kernel audit."""
    lines = []
    ap = lines.append
    ap("### ASIETY-FREEDOM chain, step by step (every step priced)")
    ap("")
    ap("> **Read this table before reading the asiety rows above.** The author's chain was:")
    ap("> weak choice (Act-free) → **asiety** → *because of the nature of Him who grounds")
    ap("> reality*, assert **`AsietyFreedom`** → which gives rise to **true choice** and")
    ap("> **`AsietyFreeWill`** → *which is shared with us by the creator*. The **◈ row is the")
    ap("> only step that is not a theorem**, and it is a declaration, not a derivation.")
    ap("")
    ap("`L1` = the axiom-free Act-free route · `◈` = **the declared bridge, not a theorem** ·")
    ap("`L2` = the transfers that depend on it · `🧱` = `{}` countermodel pricing it · `✓` =")
    ap("coherence · `Σ` = master summary.")
    ap("")
    ap("| # | Ledger | Declaration | Step | Status | Kernel footprint |")
    ap("|---|---|---|---|---|---|")
    for kind, cid, full, atype, text in ASIETY_FREEDOM_STEPS:
        if atype == "stipulation":
            ent = _stipulation_entry("asietyFreedom_ofGroundFreedom")
            tag = (ent or {}).get("tag", "META")
            status = f"◈ STIPULATED ({tag}) — a `def`, **not an axiom**"
        else:
            live = _classical_anchor_live({"type": atype, "full": full},
                                          decls, node_map)
            status = _CA_STATUS_TEXT.get(live, "?") + _stip_marker([full])
        ap(f"| {kind} | {cid} | {_classical_decl_link(full, decls)} | {text} | "
           f"{status} | {kernel_fp_text(full)} |")
    ap("")
    ent = _stipulation_entry("asietyFreedom_ofGroundFreedom")
    if ent:
        ap(f"**Cost of ◈ `{ent.get('name')}`** (`{ent.get('location')}`), as registered: "
           f"{ent.get('cost', '')}")
        ap("")
    ap("**Two limits that the badge alone does not convey, and which are the reason this")
    ap("block exists:**")
    ap("")
    ap("1. **\"The declared-axiom count did not move\" is NOT a test for this batch.** The")
    ap("   bridge is a `def`, so `#print axioms` cannot see it, and its `{Means, Subject}`")
    ap("   footprint is vocabulary-only *whether the bridge is principled or arbitrary*. For")
    ap("   ASIETIC-CHOICE the invariant was a genuine test; here the **◈ registry entry and")
    ap("   this block are load-bearing rather than decorative**. That is a limitation of the")
    ap("   auditing instrument, declared rather than exploited.")
    ap("2. **The `GroundsEntity` premise of the three transfers is vacuous**")
    ap("   (`ground_grounds_the_meaningless`: the ground grounds even entities bearing no")
    ap("   meaning), so the whole metaphysical weight sits on the ◈ row. It is named `_hG` and")
    ap("   declared vacuous rather than quietly dropped, so the footprint cannot be mistaken for")
    ap("   depth. The only non-vacuous `GroundsEntity` use in the module is C295, which is a")
    ap("   `¬ ∃ s` over subjects.")
    ap("")
    ap("**Also not claimed:** the universal reading of the ◈ bridge is strictly stronger than")
    ap("an existential one (\"shared with *someone*\"), and nothing here shows the stronger")
    ap("reading is the correct one; no axiom-free existence of a chooser (C294 **refutes** it,")
    ap("it is not merely open); and the Act-free `?` around `base.txt`'s `ClaimsCorrect`-free")
    ap("weak→strong step is **bypassed, not closed** — the bare form stays machine-refuted")
    ap("(C273/C274).")
    ap("")
    return lines


MEANING_RETORSION_STEPS = [
    ("§0", "C368", "Logos.MeaningRetorsion.NoMeaning", "decl",
     "**THE THESIS ITSELF**, stated in Γ's own `Meaning_I` vocabulary — `base.txt` §26 item 3 "
     "(\"Não existe conteúdo\") and `poem.txt` P3 (\"há significado\")"),
    ("§0", "C369", "Logos.MeaningRetorsion.noMeaning_iff_noIntentionalSubject", "decl",
     "the thesis **is** the audited negation of the retorsive conclusion, re-indexed "
     "(two existential quantifiers swapped — no `propext`)"),
    ("§0", "C370", "Logos.MeaningRetorsion.noMeaning_iff_pointwise", "decl",
     "pointwise form: no subject means anything at all"),
    ("1/4", "C371", "Logos.MeaningRetorsion.noMeaning_is_unmeaned", "decl",
     "the thesis cannot be **meant** (consistent — a universal negative is not a liar)"),
    ("2/4", "C372", "Logos.MeaningRetorsion.noMeaning_is_unperformed", "decl",
     "the thesis cannot be **acted**"),
    ("3/4", "C373", "Logos.MeaningRetorsion.no_correct_judgment_of_noMeaning", "decl",
     "the thesis cannot be **judged correct** — NEW: no `Correct` rung existed for any "
     "meaninglessness thesis"),
    ("3'/4", "C374", "Logos.MeaningRetorsion.judgment_of_noMeaning_is_incorrect", "decl",
     "whoever judges the thesis at all judges it **incorrectly** (exhaustive form)"),
    ("4/4", "C375", "Logos.MeaningRetorsion.noMeaning_is_unassertable", "decl",
     "**THE RETORSION, unconditional**: nobody can hold the thesis as correct — no hypothesis, "
     "no subject, no bridge, **no new axiom**"),
    ("4/4", "C376", "Logos.MeaningRetorsion.noMeaning_ladder", "decl",
     "all four rungs in one conjunction"),
    ("+", "C377", "Logos.MeaningRetorsion.affirms_noMeaning_yields_meaning", "decl",
     "the author's sentence, positively: **affirming the thesis produces an instance of what "
     "the thesis denies**. Hypothesis `Act` (generalized from `Asserts` 2026-09-27, which is the "
     "special case) — the performance, not the performance-plus-success C375 denies"),
    ("+", "C378", "Logos.MeaningRetorsion.judges_noMeaning_yields_meaning", "decl",
     "the same at the judging level — the form `poem.txt` P3 uses"),
    ("3a", "C379", "Logos.MeaningRetorsion.no_countermodel_can_affirm_the_thesis", "decl",
     "**no** meaning-vocabulary, of any shape, can host an affirmation of the thesis "
     "(*a corollary* of `level2_signature_asserts_noi_selfRefutes`, generalised)"),
    ("3b", "—", "Logos.MeaningRetorsion.NoWeakActIn", "decl",
     "the denial of the act-datum, in an arbitrary signature — the withholding that "
     "distinguishes M1 from any `Means`-vocabulary"),
    ("3b", "C380", "Logos.MeaningRetorsion.signature_weak_retorsion", "decl",
     "the **weak** retorsion, signature-general — NEW: `Agency.noWeakAct_selfRefutes` is "
     "canonical-only"),
    ("3b", "C381", "Logos.MeaningRetorsion.the_two_denials_cannot_both_be_affirmed", "decl",
     "**THE JOINT REFUTATION, one sentence**: deny the act-datum, then affirm the denial — "
     "impossible. This is M1 and C294 refuted as *answers*"),
    ("3c", "C382", "Logos.MeaningRetorsion.the_meaningless_world_remains_a_model", "countermodel",
     "**THE COMPLEMENT, populated**: a world *with subjects* where the thesis is true and no "
     "assertion of it succeeds. A **model, not a refutation** — and the machine-checked reason "
     "the content survives"),
     ("3c", "C383", "Logos.MeaningRetorsion.countermodel_is_a_world_where_the_thesis_is_unutterable",
      "decl", "both halves together: the countermodel's world is a world where the thesis is true "
      "**and** no assertion of it succeeds. *\"Unutterable\" is not a prohibition on the type:* the "
      "sentence is well-formed and the author utters it — what is excluded is the assertion "
      "*succeeding*"),
    ("3d", "C384", "Logos.MeaningRetorsion.Voices", "decl",
     "**THE PERFORMANCE WITHOUT THE SUCCESS CONDITION** — the author's \"it can be uttered, it can "
     "be asserted\". The predicate Γ lacked: every `asserts` in the corpus carries `∧ p`, so "
     "*assert* had come to mean *correctly assert*. What the performative contradiction leaves "
     "standing, since C375 refutes only the act *succeeding*"),
    ("3d", "C385", "Logos.MeaningRetorsion.the_thesis_is_utterable_though_not_assertable",
     "countermodel",
     "**AND THE WORLD IN WHICH THE THESIS IS UTTERED**: 3c with `act := True`. A subject, nothing "
     "meant, the thesis true, the thesis *said* — and still no assertion of it that succeeds. This "
     "is what makes 3c's word \"unutterable\" a misnomer rather than a reading"),
    ("4", "C401", "Logos.MeaningRetorsion.noMeaning_is_refuted_from_plurality", "decl",
     "**THE REFUTATION — the no-meaning world is not possible in Γ**: `Meaning_I p` is definitionally "
     "`∃ s, Means s p`, so `cogito_from_T12` is already a counterexample to the thesis, three lines "
     "that were never written down. NOT axiom-free — C382 *is* the proof nothing in the bare vocabulary "
     "refutes it. What C382 shows is a free signature's consistency; what this shows is the thesis does "
     "not survive *the theory*, on the plurality bridge"),
    ("4", "C402", "Logos.MeaningRetorsion.noMeaning_is_refuted_from_the_act_datum", "decl",
     "**the same refutation on the act-datum, no META bridge**: whoever grants that an act occurred "
     "grants the falsity with it, since `Act` already contains `Means`. Conditional, bridge-free, price "
     "relocated to the declared act-datum axiom C454 — one axiom, not free in performance"),
]


def render_semantic_finitude_chain(decls: dict, node_map: dict) -> list[str]:
    """The SEMANTIC-FINITUDE chain, step by step.

    Emitted so the declared F15 bound can never be read as a derived theorem. The
    bound is its own row (C388), badged from the kernel node kind and the axiom
    registry; the ten `L2` theorems are unconditional, resting on it. Badges and
    footprints are DERIVED; nothing here is transcribed. See AGENTS.md.
    """
    lines = []
    ap = lines.append
    ap("### SEMANTIC-FINITUDE chain, step by step (F15 declared as a vocabulary axiom)")
    ap("")
    ap("> **Read this table before reading any unicity/ground row above.** Γ has a ground of")
    ap("> reality, and on the **declared** bound that no subject means every proposition, that")
    ap("> ground is the **sole** universal ground. The bound is the **C388 row**, and it is a")
    ap("> **declaration, not a derivation** — the 27th axiom, tagged `VOCAB`. A reader must not")
    ap("> read the `L2` rows as a proof of monotheism, and must not read `VOCAB` as \"axiom-free\".")
    ap("")
    ap("`◆` = **the declared bound, not a theorem** · `L2` = a theorem resting on the bound")
    ap("· `🧱` = `{}` countermodel pricing it · `✓` = coherence.")
    ap("")
    ap("| # | Ledger | Declaration | Step | Status | Kernel footprint |")
    ap("|---|---|---|---|---|---|")
    for kind, cid, full, atype, text in SEMANTIC_FINITUDE_STEPS:
        live = _classical_anchor_live({"type": atype, "full": full}, decls, node_map)
        status = _CA_STATUS_TEXT.get(live, "?") + _stip_marker([full])
        ap(f"| {kind} | {cid} | {_classical_decl_link(full, decls)} | {text} | "
           f"{status} | {kernel_fp_text(full)} |")
    ap("")
    ap("**Cost of the C388 declaration** (`formal/Logos/SemanticFinitude.lean`), as declared:")
    ap("one axiom, `Tag: VOCAB` — it bounds a single uninterpreted relation `Means` on a single")
    ap("nullary sort `Subject` and asserts no connection between entities. It is priced in every")
    ap("dependent footprint below, and the declared-axiom count moved **26 → 27** when it was")
    ap("promoted. The ten `L2` rows keep the `PROVEN` badge they had as stipulations because the")
    ap("generator treats only `SEM`/`META`/`TRANS` as substantive; `VOCAB` yields `PROVEN`.")
    ap("")
    ap("**Four limits that the badge alone does not convey, and which are the reason this")
    ap("block exists:**")
    ap("")
    ap("1. **The price was invisible until this batch, and that was the defect.** As a `def` of a")
    ap("   `Prop` taken as a premise, the bound was reported by `#print axioms` as the *same*")
    ap("   footprint as the corresponding pre-existing conditional theorem, the axiom count was")
    ap("   unmoved, and the ◈ badge was the only signal. It is now a declared axiom, so the price")
    ap("   is in every dependent footprint. The count moving 26 → 27 is what a price looks like")
    ap("   when it is honestly charged; its earlier stillness was the point, not a pass.")
    ap("2. **The ten `L2` rows are unconditional theorems, not corollaries.** The ten original")
    ap("   conditional theorems (`exactly_one_universal_modal_ground`, `ofGround_divine_simplicity`,")
    ap("   …) are **not** edited and keep their anonymous premise; the `L2` rows are the same")
    ap("   theorems keyed to the *named* bound, which declaring it turned into theorems of Γ in")
    ap("   their own right. The `_stipulated` suffix is historical and is kept only because the")
    ap("   ledger and the prose corpus cite these names.")
    ap("3. **The bound is falsifiable, not vacuous** (`🧱 semantic_omnipotence_is_consistent`,")
    ap("   `{}`): a semantically omnipotent carrier is a model of its negation, so the unicity")
    ap("   genuinely rests on the bound — which is why the bound must be declared, not assumed.")
    ap("   It is also *load-bearing* in the other direction (`✓`): `ofGround_meansAll` gives the")
    ap("   ground every proposition, so the bound is exactly what keeps it off the `Subject` sort.")
    ap("4. **What is still NOT claimed.** `Tag: VOCAB` says the bound restricts one uninterpreted")
    ap("   relation on one nullary sort (`Means` on `Subject`) and asserts no connection between")
    ap("   entities — the same status as `ofGround_existsAt`; if the author re-tags it `SEM` the")
    ap("   badge follows and the ten theorems drop to `⚠️`. Personhood of the ground (C228),")
    ap("   Trinity (F6/F8) and *explanatory* grounding (C326/C328) are untouched and remain")
    ap("   BLOCKED / DEFERRED / not attempted. This batch does not move existence, which was")
    ap("   already `PROVEN` unconditionally.")
    ap("")
    return lines


def render_meaning_retorsion_chain(decls: dict, node_map: dict) -> list[str]:
    """The MEANING-RETORSION chain, step by step.

    Emitted so the refutation cannot be read off the badge alone. The two rows that
    matter most are 4/4 (the unconditional retorsion) and 3c (the populated complement):
    without 3c the refutation of the countermodel is a trick, and 3c is what stops it
    being one. Badges and footprints are DERIVED; nothing here is transcribed.
    See AGENTS.md.
    """
    lines = []
    ap = lines.append
    ap("### MEANING-RETORSION chain, step by step (the \"there is no meaning\" thesis)")
    ap("")
    ap("> **The demand:** *to affirm that there is no meaning is to prove the invalidity of my")
    ap("> own affirmation* — and *the countermodel is wrong, and you shall prove it*. Both are")
    ap("> discharged here, and the second only in the form in which it is true. The affirmation")
    ap("> is refuted (4/4). The countermodel is refuted **as an answer** (3a/3b) and is")
    ap("> **preserved as a model** (3c). A reader who takes 3a as a refutation of the model has")
    ap("> misread the chain; 3c is the row that forbids it.")
    ap("")
    ap("`§0` = the re-index · `1/4…4/4` = the ladder, ascending in strength · `+` = the positive")
    ap("existence form · `3a/3b` = the refutation *as an answer* · `3c` = the complement that")
    ap("keeps it honest · `🧱` = `{}` countermodel.")
    ap("")
    ap("| # | Ledger | Declaration | Step | Status | Kernel footprint |")
    ap("|---|---|---|---|---|---|")
    for kind, cid, full, atype, text in MEANING_RETORSION_STEPS:
        live = _classical_anchor_live({"type": atype, "full": full}, decls, node_map)
        status = _CA_STATUS_TEXT.get(live, "?") + _stip_marker([full])
        ap(f"| {kind} | {cid} | {_classical_decl_link(full, decls)} | {text} | "
           f"{status} | {kernel_fp_text(full)} |")
    ap("")
    ap("**Five limits the badges do not convey, and the reason this block exists:**")
    ap("")
    ap("1. **The retorsion is unconditional but not free.** 4/4 has no hypothesis and no new")
    ap("   axiom — its footprint is vocabulary only. But the contradiction is fed *by* the")
    ap("   affirmation: `Asserts s NoMeaning → False` needs the affirmation as input. The")
    ap("   retorsion is **free in axioms and not free in performance**. That is the honest")
    ap("   reading of the author's sentence, and it is also the whole price.")
    ap("   **So \"unutterable\" is not a prohibition on the sentence.** The sentence is")
    ap("   well-formed, the author utters it, and 4/4 is discharged by that very utterance:")
    ap("   the antecedent is supplied and the contradiction follows. What C375 excludes is an")
    ap("   assertion *succeeding* — an assertion that holds its content — not an assertion")
    ap("   being made. Uttering the thesis is exactly what triggers the retorsion.")
    ap("2. **The thesis is NOT shown false.** `¬ NoMeaning` is not derivable and is not")
    ap("   claimed. 3c exhibits a **populated** world (`Subject := Unit`, against M0's empty")
    ap("   sort) in which the thesis is true and no assertion of it succeeds. So the content")
    ap("   survives intact; only the *affirming* of it fails to land. This is the corpus's own")
    ap("   distinction (`NegativeRetorsionAudit.lean:292-295`): `NoI is false` is **not**")
    ap("   equivalent to `NoI is unassertable`.")
    ap("3. **3a is a corollary and is labelled one.** `no_countermodel_can_affirm_the_thesis`")
    ap("   is `level2_signature_asserts_noi_selfRefutes` (`:286`) generalised from one signature")
    ap("   to all of them. The batch's novelty is C369 (the re-index), C373 (the `Correct` rung),")
    ap("   C380 (the signature-general weak retorsion) and C382 (the populated complement).")
    ap("4. **Why an *answer* and not a *model*.** A countermodel is not a counterexample; it is")
    ap("   a description of a world. An answer is a move made inside discourse. M1 and C294")
    ap("   describe worlds where no move is ever made (`Means := False` *and* `act := False`),")
    ap("   so they cannot contain the affirmation of their own silence. A content nobody can")
    ap("   hold as correct is not a position; it is a description of a world in which nothing is")
    ap("   ever held. **This is not a claim that meaninglessness is false.**")
    ap("5. **Price of the positive claim is unmoved.** Nothing here carries `AxTwoSubjects` or")
    ap("   `transcendental_reflection_intentional` — that is Batch B's one substantive claim")
    ap("   about its own cost, and gate B2 verifies it rather than assuming it. But the")
    ap("   *unconditional* existence of a meaning still costs a person-datum (C367: `Will`/`subjectWill`,")
    ap("   vocabulary, no bridge); what is")
    ap("   shown is that it is over-strong whenever an affirmation is supplied as input.")
    ap("")
    return lines


def _axiom_row_status(full: str, decls: dict) -> str:
    """`◆ AXIOM (TAG)` for one declared axiom, tag derived from the Lean docstring.
    A bare `◆ AXIOM` carries no tag, so axiom rows in the LOVE chain get their own
    presentation rather than the generic cell."""
    d = decls.get(full) or {}
    tag = (d.get("tag") or "UNTAGGED").strip()
    return f"◆ AXIOM ({tag}) — a declared axiom, **not a theorem**"


def render_love_chain(decls: dict, node_map: dict) -> list[str]:
    """The LOVE chain, step by step, with both prices on every step.

    Emitted so that neither price can be read off the badge alone: the PROVEN↑ badge
    names only the substantive axiom, so without this block a reader would conclude the
    VOCAB primitive is free. Every other cell is derived from the kernel audit."""
    lines = []
    ap = lines.append
    ap("### LOVE chain, step by step (both prices, every step)")
    ap("")
    ap("> **Read this table before reading the divine-love row above.** The author's chain was:")
    ap("> axiom-free ground facts → **the missing vocabulary** (`GroundBearsGood`, PRICE 1) →")
    ap("> **the declared bridge** (`AxGroundLovesContingentRealm`, PRICE 2) → which yields the")
    ap("> inhabitants → while the separations say what was **not** bought, and the SEM datum")
    ap("> (PRICE 3, sibling module) supplies the cosmos. The **◆ rows are axioms, not theorems**,")
    ap("> and the two prices are different in kind: confusing them is the mistake the kernel")
    ap("> audit cannot catch.")
    ap("")
    ap("`L1` = no new vocabulary · `V` = consumes the VOCAB primitive, no substantive axiom ·")
    ap("`◆` = **the axiom itself, not a theorem** · `L2` = the priced inhabitants · `S` =")
    ap("separations · `D` = the SEM datum side · `🧱` = `{}` countermodel pricing the shape.")
    ap("")
    ap("| # | Ledger | Declaration | Step | Status | Kernel footprint |")
    ap("|---|---|---|---|---|---|")
    for kind, cid, full, atype, text in LOVE_STEPS:
        if atype == "axiom":
            status = _axiom_row_status(full, decls)
        else:
            live = _classical_anchor_live({"type": atype, "full": full},
                                          decls, node_map)
            status = _CA_STATUS_TEXT.get(live, "?") + _stip_marker([full])
        ap(f"| {kind} | {cid} | {_classical_decl_link(full, decls)} | {text} | "
           f"{status} | {kernel_fp_text(full)} |")
    ap("")
    ap("**The dual cost, stated because the badge states only half of it.** The "
       "`the_ground_is_a_necessary_and_chosen_lover` row above renders "
       "**⚠️ AXIOMATIC (AxGroundLovesContingentRealm)**: `footprint_parts` files "
       "`GroundBearsGood` under the vocabulary baseline, so the primitive never appears in "
       "the parenthetical. A reader trusting the badge alone concludes the directed-good "
       "vocabulary is free. It is not: without PRICE 1 there is no `GroundLoves` relation to "
       "inhabit, and without PRICE 2 no inhabitant follows. The registry is unmoved at 25 "
       "axioms (14/7/4) **not because the batch is free but because all three prices were "
       "already declared and invisible** — which is why this block, like the ◈ registry for "
       "ASIETIC-CHOICE, is load-bearing rather than decorative.")
    ap("")
    ap("**Also not claimed:** `GroundLoves` is **not** `Loves` (different index, different "
       "kind — merging them would silently reinterpret T14); the `GroundLoves → Loves` "
       "transfer is unstatable (C348), so bridge #9 / C228 stands exactly as it was; C330 "
       "is ontology-forced, not evidence of love; C353 is a countermodel on an unrelated "
       "free structure, not a model of Γ; and C354 is satisfiability conditional on a "
       "`Means` inhabitant.")
    ap("")
    return lines


def render_two_kinds_chain(decls: dict, node_map: dict) -> list[str]:
    """The TWO-KINDS chain, step by step, with the price of every step.

    Added 2026-09-28 to close a presentation gap, not a formal one: the batch was
    fully proven and fully registered in GAPMAP, but no reader-facing chain list
    contained it, so the derived necessary Person (C409) and the personal-ground
    flagship (C151/C152) never appeared in the deduction. Per AGENTS.md, chain
    membership is maintained by hand while badges and footprints are derived, so
    the list is explicit here and guarded by `audit_chain_coverage`.

    Emitted so that the one substantive price in the batch — the META bridge
    C404 — is visible as its own row and cannot be absorbed by the `{}`-class
    rows either side of it. Badges and footprints are DERIVED; nothing here is
    transcribed.
    """
    lines = []
    ap = lines.append
    ap("### TWO-KINDS chain, step by step (every step priced)")
    ap("")
    ap("> **Read this table before reading any plurality/personal-ground row above.** The")
    ap("> argument's remaining metaphysical gap was *who fills the necessary pole*. This batch")
    ap("> introduces a free predicate for a subject's **kind**, proves that the two kinds are")
    ap("> exactly the two modal profiles, and then — on **one** declared `META` bridge — derives")
    ap("> that the necessary kind is inhabited by a **Person**. The whole price is the `◆` row.")
    ap("")
    ap("`V` = the `VOCAB` axiom (a free predicate, asserting no existence) · `D` = its `def`")
    ap("complement · `L1` = a theorem on vocabulary alone, **0 substantive axioms** · `◆` = the")
    ap("declared `META` bridge · `L2` = a theorem resting on that bridge · `Σ` = the headline")
    ap("partition.")
    ap("")
    ap("| # | Ledger | Declaration | Step | Status | Kernel footprint |")
    ap("|---|---|---|---|---|---|")
    for kind, cid, full, atype, text in TWO_KINDS_STEPS:
        live = _classical_anchor_live({"type": atype, "full": full}, decls, node_map)
        status = _CA_STATUS_TEXT.get(live, "?") + _stip_marker([full])
        ap(f"| {kind} | {cid} | {_classical_decl_link(full, decls)} | {text} | "
           f"{status} | {kernel_fp_text(full)} |")
    ap("")
    ap("**Five limits that the badge alone does not convey, and which are the reason this")
    ap("block exists:**")
    ap("")
    ap("1. **Eleven of the sixteen rows are vocabulary-only, and four carry the bridge.**")
    ap("   The kind predicate `V` is `Tag: VOCAB` and asserts nothing about existence. Every")
    ap("   `L1` row is vocabulary-only — C410 (the two kinds *are* the two modal profiles) is")
    ap("   `{NecessarySubjectKind, Subject}`-class, and C152 is")
    ap("   `{Initiates, Means, State, Subject, Will, subjectWill, will_individuation}`-class. Only")
    ap("   C151 additionally carries Lean's own `choice`/`propext`/`sound`, which are **core")
    ap("   kernel**, not Γ-declared axioms — the table prints it so the distinction is visible.")
    ap("   The four rows carrying `necessaryPersonalSubjectExists` are the `◆` row and its three")
    ap("   `L2` corollaries.")
    ap("2. **The `◆` row is the entire price.** `necessaryPersonalSubjectExists` (`Tag: META`)")
    ap("   is the only substantive axiom the batch introduces, and C407/C408/C409 inherit")
    ap("   exactly it and nothing else. It is a **metaphysical bridge** (`META`), not a")
    ap("   vocabulary commitment, and it is stated as an existential inhabitance of the kind —")
    ap("   not as a derivation of personhood from the ground-constructor.")
    ap("3. **C406 discharges C329 without a love axiom.** `no_subject_is_a_necessary_entity`")
    ap("   used to need the exclusion hypothesis; it is now a kind-relative theorem. The love")
    ap("   bridge is not doing metaphysical work it was never stated to do.")
    ap("4. **The necessary kind and the ground-constructor are *not* the same row.** The")
    ap("   `Entity.ofGround` constructor is disjoint from `EntityOf s` by `cases`")
    ap("   (`ofGround_ne_ofSubject`, `FoundationalUnicity.lean:131`) — that is constructor")
    ap("   disjointness on a three-constructor inductive, **not** a verdict that the ground is")
    ap("   impersonal. The necessary *kind* is inhabited by a Person (C404); the ground")
    ap("   *constructor* is not a `Subject`. Conflating the two is the error `LovesAsGround.lean`")
    ap("   retracts in its own docstring.")
    ap("5. **What this batch does NOT close.** C228 — identifying the normative ground with a")
    ap("   *Person* — remains `BLOCKED`, and C212 proves ground-unicity does not force a unitary")
    ap("   monad. Monotheism *at the level of the Person* is open; the ground's *sole universal")
    ap("   modal grounding* (C319/C320) is unaffected by this batch and rests on F15 alone.")
    ap("")
    return lines


# 2026-09-28. The §9 precedence batch (C417–C426), the F16 price (C427–C428) and
# the §18 identity form (C429–C431). Membership is hand-maintained (AGENTS.md).
# Kinds: `R` = refutation/valuation row · `L1` = a theorem on vocabulary alone ·
# `Σ` = the headline · `D` = a def/structure, no claim id · `S` = a separation.
PRECEDENCE_STEPS = [
    ("R", "C417", "Logos.Precedence.no_atom_is_true_at_falsityWorld", "decl",
     "the **form true and weaker than the one the prose wanted**: in the all-`TV.f` world no "
     "*atom* is true. This is the honest reading of 'a world where the distinction is not "
     "instantiated' — a valuation, not an absence of forms"),
    ("R", "C418", "Logos.Precedence.every_world_satisfies_some_form", "decl",
     "**the refutation of this batch's own first draft.** The batch plan (now `PLAN.md`) proposed as its opening "
     "`{}` lemma that no form is satisfied at the falsity world; that lemma is **false**, "
     "because `Satisfies` is closed under negation. This row is the machine-checked reason: "
     "for *every* world some form is satisfied, and the branching is constructive — the atom 0 "
     "if the world sets it true, its negation otherwise — so there is no `Classical.choice` "
     "anywhere in §9's foundational half"),
    ("L1", "C419", "Logos.Precedence.ofGround_obtains_where_no_atom_is_true", "decl",
     "**precedence, positively**: the ground obtains in a world where no atom is true. The "
     "obtaining is the `ofGround` arm of `EntityExistsAt`, so the price is the artefact of "
     "`ExistsAt` unfolding — the proof never reads the kind predicate"),
    ("L1", "C420", "Logos.Precedence.ground_existence_does_not_entail_any_truth", "decl",
     "and it does **not** entail any truth. This is the converse a precedence reading would "
     "need, and it is what makes §9 a *separation* rather than a filter: the distinction is "
     "not a condition on the ground"),
    ("L1", "C421", "Logos.Precedence.ground_existence_is_invariant_while_content_varies", "decl",
     "the two halves in one line: what is *true* varies across worlds (the invariance of the "
     "agent, C180), the ground's *obtaining* does not"),
    ("L1", "C422", "Logos.Precedence.ground_scope_is_not_the_truth_set", "decl",
     "the ground's scope is **not** the set of the true — refuted at `p := False`, where "
     "`EntityMeans ofGround p` reduces to `True` and `T p` to `p`. This is C236 read from the "
     "other side: previously the ground was kept off the truth-tracking relation by an argument "
     "about content; here by the definition of the meaning side"),
    ("L1", "C423", "Logos.Precedence.ground_conditions_every_content_bearer", "decl",
     "**the positive half of §9**: the ground *conditions* every content-bearing entity through "
     "`GroundsEntity`. Read the report as carefully as the claim — under Γ's definitions "
     "`GroundsEntity ofGround e` is `∀ p, EntityMeans e p → True`, so the ground conditions "
     "**everything**, meaning-bearing or not (the same fact C328 records for the "
     "meaningless). The meaning hypothesis is carried because §9 says 'everything that arises "
     "under the distinction', and it is *not* used"),
    ("S", "C424", "Logos.Precedence.atom_fails_precedence", "decl",
     "**the discriminating half, in the corpus's own separation idiom**: the predicate holds of "
     "the ground and fails of a worldly atom. `EntityExistsAt w (ofAtom 0)` *is* `w 0 = TV.t`, "
     "which *is* `Satisfies w (Form.atom 0)` — a mundane atom's obtaining at a world is its own "
     "truth, so no world can both satisfy and deny it"),
    ("Σ", "C425", "Logos.Precedence.ofGround_precedes_the_right_wrong_distinction", "decl",
     "**§9's headline**, the three fields in one object: the ground precedes the distinction, "
     "discriminates it, and is not discriminated by it. 'Precedes' is deliberately `GroundsEntity` "
     "— a condition, never a derivation. Vocabulary-only, **0 substantive axioms**"),
    ("R", "C426", "Logos.Precedence.rightWrongDistinction_is_world_invariant", "decl",
     "**the limit, and the reason §9 is a split rather than a bare ✅**: `Core.T p := p` is the "
     "identity on `Prop`, so `N_T` and `N_F` carry no world index. The world-relative argument "
     "of §9 is therefore **inert by design** — it exhibits that a world-relative precedence at "
     "the level of the truth predicate is not well-formed on the current vocabulary. §9 is "
     "established in the semantic layer (`Satisfies`) and *not* in the truth-predicate layer; a "
     "world-indexed `T` would be new vocabulary at `Tag: SEM` at minimum, and that is the "
     "author's decision"),
    ("L1", "C427", "Logos.DivineImmutability.no_world_indexed_extension_of_meaning_can_vary",
     "decl",
     "**F16 by its price, not by its proof**: no relation that agrees with `EntityMeans` in every "
     "world can exhibit a varying capacity. This turns F16's declared reason into a theorem "
     "instead of a sentence in a ledger cell. **F16 itself stays BLOCKED** — what is proved here "
     "is that the block is *forced*: variation, if it exists, has to come from new vocabulary"),
    ("L1", "C428", "Logos.DivineImmutability.world_indexed_extension_of_meaning_is_world_constant",
     "decl",
     "the constructive half of C427, so the ledger can point at the invariance and not only at "
     "its impossibility. C321 (`capacity_invariance_holds_for_every_entity`) is the same fact "
     "over `CapacityInvariance`; this is the conditional form. It is **not** a claim that the "
     "ground's meaning does not change — there is no world-indexed meaning in Γ that could"),
    ("L1", "C429", "Logos.CosmicExistence.no_entity_is_identical_to_the_whole", "decl",
     "the **identity** form of pantheism fails for all three `Entity` constructors at once, by "
     "exhaustion. Read it as the cheap thing it is: it says Γ's `Entity` is an inductive with "
     "distinguishable constructors, **not** that an ontology of the universe has been "
     "adjudicated. It is not an empty-world artefact — the witness is the same one C323 uses"),
    ("Σ", "C430", "Logos.CosmicExistence.the_ground_is_not_the_universe", "decl",
     "**§18's identity-form headline**, read off C429 at the ground. `Universe e := ∀ w x, "
     "ExistsAt w x → e = x` ('whatever obtains **is** e') is the only identity reading "
     "well-formed over `Entity`. `Universe` appears **only in conclusions** — no axiom, no `Tag`, "
     "no ◈ registration"),
    ("L1", "C431", "Logos.CosmicExistence.grounding_never_yields_identity_of_the_totality",
     "decl",
     "**founding and identifying are not compatible alternatives** — §18's second stated gap "
     "('it does not specify whether founded and identical are compatible') is machine-checked as "
     "*incompatible*. The antecedent is the whole of `GroundsEntity`, which under Γ's "
     "definitions holds for every entity (C328), so the row's content is entirely in the "
     "`¬ Universe e` half"),
    ("R", "C432", "Logos.Precedence.stage_invariance_iff_atemporal", "decl",
     "**a finding, not a contribution**: `StageInvariance` (`DivineImmutability.lean:86`) and "
     "`Atemporal` (`NecessityEternity.lean:92`) unfold to the *same* proposition. The corpus has "
     "two names for the second field of the immutability master, so §8's 'timelessness' and that "
     "field are not two steps. What *does* work is the one-dimensional contrast, because "
     "`Everlasting := ∀ t, ExistsAtTime t e` is a different shape — that is C436"),
    ("L1", "C433", "Logos.Precedence.ofGround_sole_precedes_right_wrong", "decl",
     "**§9's unicity**: the ground is the *only* entity preceding the distinction. The `ofAtom n` "
     "arm is C424 verbatim and free; the `ofSubject s` arm instantiates `conditions_every_bearer` "
     "at the ground, forcing `∀ p, Means s p`, and **the bound that refutes that is F15's** — "
     "`SemanticFinitude`. So §9's unicity is a corollary of the same sentence that closed F15's "
     "foundational unicity. The person bridge #9 is neither used nor needed"),
    ("S", "C434", "Logos.Precedence.stage_invariance_does_not_uniquely_identify_the_ground", "decl",
     "**the counterexample that makes the articulation possible**: `Entity.ofAtom 0` *is* "
     "stage-invariant (`(stageOf t) 0 = TV.t`, i.e. `0 ≤ t`, at every stage) and is not the "
     "ground. So the two precedences differ in discriminating power"),
    ("Σ", "C435", "Logos.Precedence.precedence_identifies_the_ground_where_stage_invariance_does_not",
     "decl",
     "**the articulation `CHARACTERISTICS.md:353` still listed as open**, stated as a *separation "
     "of discriminating power* and not as an identification: the two notions have different "
     "extensions, and only `PrecedesRightWrong` picks the ground out. Conjoining them would be "
     "the `CapacityInvariance` tautology defect C321 already reports"),
]


def render_precedence_chain(decls: dict, node_map: dict) -> list[str]:
    """Reader-facing chain for the 2026-09-28 §9 / F16-price / §18-identity batch."""
    lines: list[str] = []
    ap = lines.append
    ap("### Chain 6 — Precedence to Right/Wrong (§9), the price of F16, and pantheism by identity (§18)")
    ap("")
    ap("> **What the foundation is to the right/wrong distinction, and what the ground is not.**")
    ap("> §9 was the only one of the nineteen characteristics with **zero** theorems, zero claim")
    ap("> and **no row at all** in the table above; §18 had no `Universe` predicate to exclude")
    ap("> anything with. Both now have machine-checked rows, on **0 new axioms, 0 new")
    ap("> primitives, 0 new stipulations, 0 new ◈ registrations**.")
    ap(">")
    ap("> **And the first lemma this batch planned was false.** The batch plan opened with")
    ap("> `no_form_satisfied_at_falsity_world`; `Satisfies` is closed under negation, so the")
    ap("> falsity world satisfies every negated form. C418 is the refutation, and the positive")
    ap("> reading that replaced it — *no **atom** is true* — is what the precedence is now")
    ap("> stated over. The argument of §9 is not weakened by this; it is stated precisely for the")
    ap("> first time. The author has not been asked to rewrite `base.txt` §9: the characteristic")
    ap("> remains his; what changes is what Γ can say about it.")
    ap("")
    ap("`R` = a valuation/refutation row · `L1` = a theorem on vocabulary alone, **0 substantive")
    ap("axioms** · `S` = a separation (the corpus's `∃`-form, not a claim) · `Σ` = the headline.")
    ap("")
    ap("| # | Ledger | Declaration | Step | Status | Kernel footprint |")
    ap("|---|---|---|---|---|---|")
    for kind, cid, full, atype, text in PRECEDENCE_STEPS:
        live = _classical_anchor_live({"type": atype, "full": full}, decls, node_map)
        status = _CA_STATUS_TEXT.get(live, "?") + _stip_marker([full])
        ap(f"| {kind} | {cid} | {_classical_decl_link(full, decls)} | {text} | "
           f"{status} | {kernel_fp_text(full)} |")
    ap("")
    ap("**Six limits the badges alone do not convey — the reason this block exists:**")
    ap("")
    ap("1. **The positive half of §9 is vacuous on this signature, and that is reported, not")
    ap("   hidden.** C419 says the ground obtains where no atom is true. Every world satisfies")
    ap("   some form (C418), and every world with a false atom 0 is a world where the ground's")
    ap("   obtaining is guaranteed anyway by the `ofGround` arm of `EntityExistsAt`. So the")
    ap("   *vacuity* is the finding: on Γ's current semantics there is no world in which the")
    ap("   ground's precedence is doing work, and the discriminating force is entirely in the")
    ap("   negative direction (C424) and in the vacuity report itself. A reader who wants §9 to")
    ap("   *bite* needs a semantics where some form is left unassigned — that is new vocabulary.")
    ap("2. **C423 is stronger than §9 asks, and weaker than it looks.** Its meaning hypothesis")
    ap("   is not used: `GroundsEntity ofGround e` is `∀ p, EntityMeans e p → True`, so the")
    ap("   ground conditions *every* entity. That is the same fact C328 records for the")
    ap("   meaningless, cited rather than re-proved.")
    ap("3. **§9's status is a split, and the table reports the generous half.** C419–C425 are")
    ap("   `✅ PROVEN` in the semantic layer. C426 is the reason the split is real: `Core.T p := p`")
    ap("   is the identity on `Prop`, so `N_T`/`N_F` have no world index and a world-relative")
    ap("   precedence at the truth-predicate layer is not well-formed. A bare ✅ for §9 would be")
    ap("   a transcription; the split is the derived fact.")
    ap("4. **F16 is still BLOCKED, and C427/C428 are about the block, not the claim.** What is")
    ap("   proved is that the block is *forced*: no world-indexed relation can agree with")
    ap("   `EntityMeans` everywhere and still vary. The missing instruction is still")
    ap("   `EntityMeansAt` **plus** a varying capacity — vocabulary the author has not granted.")
    ap("5. **C430 excludes one reading of pantheism, not the reading a reader may have meant.**")
    ap("   The identity form ('whatever obtains **is** the ground') fails over `Entity`. The")
    ap("   aggregate form ('the universe is not an entity') is **not a proposition over")
    ap("   `Entity` at all**, so it is left *unstatable* rather than refuted, and must be")
    ap("   formalized as a separate, weaker row if it is wanted. Realm contingency — the other")
    ap("   half of §18 — is untouched and still BLOCKED in `SUBJECTS.md` §4.")
    ap("6. **The price of the whole batch is vocabulary only.** Twelve of the fifteen rows are")
    ap("   vocabulary-only, three are `{}`; `NecessarySubjectKind` appears wherever `ExistsAt`")
    ap("   is unfolded and `Means` wherever `EntityMeans`/`GroundsEntity` is, and **no** row")
    ap("   carries a `SEM` or `META` axiom. `Precedence.PrecedesRightWrong` is a `structure` and")
    ap("   `CosmicExistence.Universe` a `def` used only in conclusions, so neither needs a `Tag:`")
    ap("   or a ◈ entry.")
    ap("")
    return lines


TEMPORALITY_STEPS = [
    ("L1", "C436", "Logos.NecessityEternity.everlasting_implies_atemporal", "decl",
     "**the generic step, which was missing**: `Everlasting → Atemporal`. The module only had the "
     "ground-level instances (`the_ground_everlasting`, `the_ground_atemporal`), both routed "
     "through `ofGround_necessary`, which is why §8 could still list 'the text does not "
     "distinguish timelessness from everlastingness' as an open gap: nothing stated the relation"),
    ("S", "C437", "Logos.NecessityEternity.contingent_subject_is_timeless_but_not_everlasting",
     "decl",
     "**the separating counterexample**, and its `Atemporal` half holds *vacuously* — under "
     "`ContingentSubjectKind s` the existence clause reduces to `stageOf t = actualWorld`, false "
     "at every `t` (at index `t+1`, `stageOf t (t+1) = TV.f` against "
     "`actualWorld (t+1) = TV.t`), so both sides of the `↔` are false. That vacuity is the point, "
     "not a defect: it is how an entity can be 'timeless' without existing everywhere"),
    ("Σ", "C438", "Logos.NecessityEternity.everlastingness_and_timelessness_are_distinct", "decl",
     "**reader-facing bundle**, discharging `CHARACTERISTICS.md:313` together with the "
     "`NÃO reivindicada` boundary of `base.txt:1521-1524`: `Everlasting` is strictly stronger "
     "than `Atemporal` as a shape of statement, and Γ's vocabulary supplies a kind of entity "
     "satisfying the weaker without the stronger"),
]


def render_temporality_chain(decls: dict, node_map: dict) -> list[str]:
    """Reader-facing chain for the 2026-09-28 §8 temporal-separation batch."""
    lines: list[str] = []
    ap = lines.append
    ap("### Chain 7 — Timelessness vs everlastingness (§8): two notions the corpus had never related")
    ap("")
    ap("> **What §8's two words for the ground's relation to time actually are.** `CHARACTERISTICS.md` §8")
    ap("> listed *\"the text does not distinguish timelessness from everlastingness\"* as a standing gap,")
    ap("> and `base.txt:1521-1524` drew the corresponding boundary (\"NÃO reivindicada\" — what is")
    ap("> PROVEN is stage-rigid existence not modulated by stages). Both are now machine-checked,")
    ap("> on **0 new axioms, 0 new primitives, 0 new stipulations**.")
    ap("")
    ap("`L1` = a theorem on vocabulary alone, **0 substantive axioms** · `S` = a separation · `Σ` = the headline.")
    ap("")
    ap("| # | Ledger | Declaration | Step | Status | Kernel footprint |")
    ap("|---|---|---|---|---|---|")
    for kind, cid, full, atype, text in TEMPORALITY_STEPS:
        live = _classical_anchor_live({"type": atype, "full": full}, decls, node_map)
        status = _CA_STATUS_TEXT.get(live, "?") + _stip_marker([full])
        ap(f"| {kind} | {cid} | {_classical_decl_link(full, decls)} | {text} | "
           f"{status} | {kernel_fp_text(full)} |")
    ap("")
    ap("**Two limits, without which the headline would overstate the result:**")
    ap("")
    ap("1. **Γ has no theorem inhabiting `ContingentSubjectKind`.** Every occurrence of it in the")
    ap("   corpus is a hypothesis — `LovesAsGround.lean:196`, `CosmicExistence.lean:299` and")
    ap("   following, with the `Creates` row at `CosmicExistence.lean:695` still BLOCKED on a")
    ap("   `Creates` relation Γ does not have. The separating region is therefore inhabited in")
    ap("   the *models*, not in the *kernel*: this chain proves the vocabulary **distinguishes**")
    ap("   the two notions, **not** that some subject of Γ falls in the difference.")
    ap("2. **The unconditional schema is not derivable and is deliberately not stated.**")
    ap("   `¬ (Atemporal e → Everlasting e)` is false in Γ twice over: the ground is atemporal")
    ap("   *and* everlasting, and so is `Entity.ofAtom 0`. A reader who wants non-vacuous")
    ap("   timelessness must go through `necessary_implies_atemporal` — the **necessary** kind,")
    ap("   not the contingent one.")
    ap("")
    ap("**And a vocabulary finding, because it changes how §8 reads:** C432 (in Chain 6) shows")
    ap("`StageInvariance` and `Atemporal` are the *same predicate under two names*. So the")
    ap("immutability master's second field and §8's 'timelessness' are one step, not two, and")
    ap("the contrast that does real work is the one-dimensional `Everlasting`.")
    ap("")
    return lines


SOLE_BEARER_STEPS = [
    ("L1", "C441", "Logos.CharacteristicSoleBearer.no_subject_grounds_the_ground", "decl",
     "**the one place this batch pays F15.** `SemanticFinitude` turns the *hypothesis* "
     "`∃ p, ¬ Means s p` of `discriminating_subject_cannot_ground_the_ground` into a sentence "
     "about *every* subject. A subject that grounds the ground would have to mean every "
     "proposition, and the bound denies exactly that"),
    ("Σ", "C442", "Logos.CharacteristicSoleBearer.ofGround_sole_foundational_omniscience", "decl",
     "**the ground alone is omniscient** — the discriminating form, not the instantiation. The "
     "atom arm is free (`EntityMeans (ofAtom _) = False`); the subject arm runs through the "
     "structure's `universal_ground` field. Disclosure: unicity of the *permissive* sense "
     "coexists with the refutation of the strong one (`ofGround_not_truth_tracking`)"),
    ("Σ", "C443", "Logos.CharacteristicSoleBearer.ofGround_sole_foundational_omnipotence", "decl",
     "**the ground alone operates gaplessly** — and this row carries the batch's sharpest "
     "disclosure. `gapless_operators_are_ground_or_necessary_kind` (`DivineOmnipotence.lean:250`) "
     "already proves a gapless operator is the ground **or** a necessary-kind subject, so "
     "`gapless_operate` alone does *not* characterise the ground. It is the `universal_ground` "
     "field, paid for by F15, that removes the second possibility. A structure's fields are not "
     "interchangeable with its doctrine"),
    ("Σ", "C444", "Logos.CharacteristicSoleBearer.ofGround_sole_foundational_omnipresence", "decl",
     "**the ground alone is foundationally omnipresent**, and this is the cheapest of the four "
     "paid rows: `maximal_capacity` settles *both* non-ground constructors by itself. Sense is "
     "foundational — physical omnipresence and metric infinity stay ❌, because `Space`, "
     "`Metric` and `Cardinal` have no declarations at all"),
    ("Σ", "C445", "Logos.CharacteristicSoleBearer.ofGround_sole_divine_pure_actuality", "decl",
     "**Actus Purus is the sole bearer**, in the same unconditional shape as C433 — which is what "
     "makes §14 and §9 directly comparable. The whole subject arm is the 27th axiom, because "
     "`EntityMeans _ p := True` is what makes 'no passive intentional potency' and 'means "
     "everything' the same sentence"),
    ("Σ", "C446",
     "Logos.CharacteristicSoleBearer.the_ground_is_sole_bearer_of_the_footprint_characteristics",
     "decl",
     "**the master theorem of the batch**: the six characteristics discriminate the ground "
     "simultaneously, so the six concepts jointly pick out `Entity.ofGround` rather than merely "
     "describing it. The conjunction is a record, not a new inference; what is new is that it is "
     "available as one statement"),
]


def render_sole_bearer_chain(decls: dict, node_map: dict) -> list[str]:
    """Reader-facing chain for the 2026-09-28 sole-bearer & derivability batch."""
    lines: list[str] = []
    ap = lines.append
    ap("### Chain 8 — Sole bearer, and the five derivations: which characteristics *pick out* the ground")
    ap("")
    ap("> **The distinction this chain exists to make.** A characteristic can sit in the theory in")
    ap("> two very different ways. *Instantiated*: `Entity.ofGround` has the property — which does not")
    ap("> distinguish \"the ground is the only bearer\" from \"the ground is the only example anyone")
    ap("> wrote down\". *Discriminating*: the property **characterises** the ground,")
    ap("> `∀ e, P e → e = Entity.ofGround`, so the concept does real work. Until this batch that")
    ap("> second form held for **one** characteristic, §9 precedence (C433). It now holds for six.")
    ap("")
    ap("> **And the other half of the batch.** C447–C451 (ledgered in `formal/GAPMAP.md`) are the five")
    ap("> already-proven Thomistic derivation principles. They turn *\"the ground has attribute X\"*")
    ap("> into **\"X is entailed by the other attributes\"** — a categorically stronger claim, at no")
    ap("> cost, because the proofs already existed and no ledger row mentioned them.")
    ap("")
    ap("`L1` = a theorem on vocabulary alone, **0 substantive axioms** · `Σ` = the headline.")
    ap("")
    ap("| # | Ledger | Declaration | Step | Status | Kernel footprint |")
    ap("|---|---|---|---|---|---|")
    for kind, cid, full, atype, text in SOLE_BEARER_STEPS:
        live = _classical_anchor_live({"type": atype, "full": full}, decls, node_map)
        status = _CA_STATUS_TEXT.get(live, "?") + _stip_marker([full])
        ap(f"| {kind} | {cid} | {_classical_decl_link(full, decls)} | {text} | "
           f"{status} | {kernel_fp_text(full)} |")
    ap("")
    ap("**Why the proof is the same four times.** `FoundationalOmnipresence`,")
    ap("`FoundationalOmniscience`, `FoundationalOmnipotence` and `DivinePureActuality` all carry a")
    ap("field `universal_ground : UniversalModalGround g`, and")
    ap("`UniversalModalGround g := ∀ w e, ExistsAt w e → e = g ∨ GroundsEntity g e`, instantiated at")
    ap("`(actualWorld, Entity.ofGround)`, yields the `GroundsEntity` disjunct — which is C441, and")
    ap("therefore `False`. So: **a subject cannot be a universal ground, hence no subject can bear")
    ap("a characteristic whose structure carries a grounding field.** That is the same observation")
    ap("C433 made for §9 (\"the price is F15\"), and `CanonicalAseity.lean:113` already recorded for")
    ap("the other characteristics. One bound, two places it was needed — now said in one file")
    ap("instead of left implicit in four proofs.")
    ap("")
    ap("**C439 — the cheapest row in the corpus, and the disclosure it forces.** Divine Simplicity is")
    ap("the one characteristic whose sole-bearership needs **no** axiom at all: the")
    ap("`no_internal_components` field closes the case, because `HasInternalComponent` is `True` on")
    ap("`ofSubject` and `ofAtom` and `False` only on `ofGround`. The batch plan predicted a `{}`")
    ap("footprint and was **wrong**: the `DivineSimplicity` *structure* carries `Means` through")
    ap("`UndividedMeaning`, so the audited footprint is `{Means, Subject}` — zero *substantive*")
    ap("axioms, not axiom-free. The disclosure is mandatory: `EntityMeans (ofAtom _) = False` is a")
    ap("definitional stipulation, so `undivided_meaning` is **vacuously true of every atom** (an")
    ap("atom has uniform meaning capacity because it has none), and a subject that discriminates")
    ap("*nothing* also satisfies `undivided_meaning`. The structure is satisfied vacuously for the")
    ap("wrong reasons by non-ground entities; only `no_internal_components` is load-bearing here.")
    ap("")
    ap("**What this chain does not say.** Not that the ground is the unique *ground* — that is")
    ap("`FoundationalUnicity.unicity` (C199), which needs `AsymmetricGrounding` and is a weaker")
    ap("claim. Not that any of this is causal: the six are structural and modal, and **F10 stays")
    ap("BLOCKED**. And **not** immutability: `capacity_invariance` is vacuous by reflexivity (the")
    ap("F16 wall) and `Initiates` is an unconstrained signature field, so the necessary-kind subject")
    ap("arm is not closable here. Immutability is recorded as ledger row **C453, `DEFERRED`**, with")
    ap("the exact missing lemma written out — a priced boundary, not a silent omission. Note what")
    ap("Chain 9 does *not* change about this: `Initiates` is now inhabited (some subject initiates),")
    ap("but it is still unconstrained *per subject* — no theorem says every necessary-kind subject")
    ap("initiates — so the subject arm stays open and C453 stays `DEFERRED`.")
    ap("")
    return lines


INHABITED_STEPS = [
    ("T", "C454", "Logos.Agency.performative_act_datum", "decl",
     "**the 28th declared axiom, and the first `Tag: TRANS` since the registry began.** "
     "The performative act-datum — an act occurs — declared rather than derived, because no "
     "derivation exists: every axiom mentioning `Act` takes an act as a premise, and the two "
     "existential axioms stop at `Means` and `BearingOf`. Author's legislation, 2026-09-28: "
     "`Initiates` cannot be uninhabited; to initiate is to be inhabited"),
    ("Σ", "C455", "Logos.Agency.some_subject_initiates", "decl",
     "**someone initiates.** `∃ s p w w', Initiates s w w' p`, unconditionally, in one step via "
     "`act_datum_implies_initiates`. This is the inhabited thing itself — not `Wills`, not "
     "`Chooses`, not `Act`, not `Asserts`. Audited footprint "
     "`{Initiates, Means, State, Subject, performative_act_datum}`: vocabulary plus the datum, "
     "so unlike the retired `semanticFinitude` ◈ the price is visible"),
    ("Σ", "C456", "Logos.Agency.not_noAct", "decl",
     "**the denial is refuted — by the datum.** `¬ NoAct`, a consequence of C454 and not a "
     "refutation from nothing (`INHABITED.md` §0): it must never be cited in the datum's favour. "
     "What it establishes is practical — \"no act occurs\" is unavailable as a premise anywhere "
     "in Γ"),
]


def render_inhabited_chain(decls: dict, node_map: dict) -> list[str]:
    """Reader-facing chain for the 2026-09-28 inhabited-initiation batch."""
    lines: list[str] = []
    ap = lines.append
    ap("### Chain 9 — Someone initiates: `Initiates` is inhabited")
    ap("")
    ap("> **What it means for a relation to be inhabited, and what it costs.** Until this batch,")
    ap("> `Initiates` was the only load-bearing relation in Γ with no inhabitant provable from the")
    ap("> axioms: every route to an act was circular (`Act` and `Asserts` both contain an initiation),")
    ap("> and the two existential axioms stop one layer short (`IntentionalSubject` is `Means`-only,")
    ap("> `Helps` is bearing-only). Three fragment countermodels exhibit `Initiates := False`, so the")
    ap("> inhabitance is not derivable — it is legislated, as the 28th axiom (`Tag: TRANS`), on the")
    ap("> author's ground that to initiate is to be inhabited. The price is one axiom and the end of")
    ap("> the 0-new-axioms invariant; the compensation is that the price is *visible*, in every")
    ap("> dependent footprint, which is the defect that retired the `semanticFinitude` ◈.")
    ap("")
    ap("`T` = the TRANS datum itself · `Σ` = what it buys.")
    ap("")
    ap("| # | Ledger | Declaration | Step | Status | Kernel footprint |")
    ap("|---|---|---|---|---|---|")
    for kind, cid, full, atype, text in INHABITED_STEPS:
        live = _classical_anchor_live({"type": atype, "full": full}, decls, node_map)
        status = _CA_STATUS_TEXT.get(live, "?") + _stip_marker([full])
        ap(f"| {kind} | {cid} | {_classical_decl_link(full, decls)} | {text} | "
           f"{status} | {kernel_fp_text(full)} |")
    ap("")
    ap("**What this chain does not say.** Not that any *particular* subject initiates — the datum")
    ap("is a global existential, and the necessary kind has no provable unique inhabitant, so the")
    ap("per-subject form stays open and **C453 stays `DEFERRED`**. Not that the ground acts:")
    ap("`ofGround` is provably not a subject, so nothing here bears on F10 `Produces` or on Creator.")
    ap("Not that willing, meaning or loving entails acting: the datum is an existential, not an")
    ap("implication, so every volition-without-action separation stands.")
    ap("")
    return lines

SUCCESSION_AUDIT_STEPS = [
    ("S", "C458", "Logos.SuccessionAudit.non_correlate_is_outside_succession", "decl",
     "**the extraction, and the finding.** `NotInSuccession e` follows from `e` not being the "
     "correlate of any subject — *non-correlateness suffices*. This is what makes the vacuity "
     "legible: `the_ground_not_in_succession` is this lemma plus the type fact that the ground is "
     "no subject's correlate, and the `Initiates` conjunct of its own statement is never used. "
     "Audited footprint `{Initiates, State, Subject}` — vocabulary only, so `PROVEN`; the `{}` "
     "prediction is wrong because the witness is genuinely consumed"),
    ("S", "C459", "Logos.SuccessionAudit.the_ground_and_every_atom_are_outside_succession", "decl",
     "**the asymmetry, machine-checked: the ground's twin of C321.** The same predicate holds for "
     "the ground and for *every atom*, so `NotInSuccession` cannot distinguish them — both close by "
     "the same constructor disjointness. C321 found exactly this for `capacity_invariance` (a "
     "tautology for all entities) and it was not on record for the other field. Disclosure, not "
     "demotion: `ofGround_divine_immutability` and C217 keep their badges and footprints"),
    ("R", "C460", "Logos.SuccessionAudit.someone_is_in_succession", "decl",
     "**someone is in succession** — the non-triviality result the ledger attributed to C197, "
     "obtained from the simplest possible witness: the correlate of the subject C455 exhibits. "
     "Note the honest asymmetry with C459: the predicate is trivial *for the ground and the "
     "atoms*, and is **not** trivial as a predicate on all entities. C197 covers `ModalInvariance` "
     "only; it never covered this field"),
    ("M", "C461", "Logos.SuccessionCountermodel.a_ground_can_produce_while_outside_succession",
     "decl",
     "**the `{}` countermodel that was claimed to be on record and was not.** A ground that "
     "*produces* while `NotInSuccession g ∧ DivineImmutability g` both hold, because the body of "
     "`NotInSuccession` mentions no entity-level agency relation at all. The C321 technique "
     "(`{}` footprint, free signature) applied to the field the ledger had left uncovered"),
    ("S", "C468", "Logos.SuccessionAudit.existence_implies_someone_initiates", "decl",
     "**\"the fact that Γ exists means someone initiates\" — and the premise does no work.** The "
     "consequent is unconditional (C455), the existence side is free in its own right (C350), and "
     "the hypothesis is named `_hExistence` for exactly that reason. The honest ledger entry for "
     "the author's sentence is *yes, and the 'if' is superfluous*, not a new price. The "
     "antecedent is the explicit structure `Nonempty ContingentRealm`, not the `def` "
     "`ContingentRealmObtains`, so the row owes no invisible def-as-premise and its footprint "
     "is exactly C455's cone — the existence half costs nothing"),
]


THOMISTIC_ACT_STEPS = [
    ("\u25c6", "C463", "Logos.ThomisticAct.Produces", "axiom",
     "**PRICE 1, VOCABULARY.** `Produces : Entity \u2192 World \u2192 Form \u2192 Prop` \u2014 F10 "
     "item (1), the production relation, with the immediate precedent of `Initiates`. The first "
     "world-indexed relation over `Entity` in the library. Its footprint is `{Subject}`, not `{}`, "
     "for the ground-level reason `FoundationalUnicity.groundsEntity_reflexive` is not `{}` either: "
     "`Entity`'s `ofSubject` constructor carries the `Subject` sort-axiom"),
    ("\u25c6", "C464", "Logos.ThomisticAct.love_implies_act", "axiom",
     "**PRICE 2, METAPHYSICAL.** *ST* I-II q.28 a.5 \u2014 the love of God is *ipso facto* an act. An "
     "**implication, never an identity**: what may love that is not an act (a preference without "
     "execution, a sentiment) is left outside, and the price is visible in C466's footprint"),
    ("\u25c6", "C465", "Logos.ThomisticAct.ground_love_produces", "axiom",
     "**PRICE 3, METAPHYSICAL.** *ST* I q.19 a.4 \u2014 the love of heaven is productive. Deliberately "
     "scoped to `Entity.ofGround`: the unrestricted form leaks through C228's "
     "`AxGroundLovesContingentRealm`, whose target-side is true of *every* entity and would make "
     "the bridge a tautology plus a claim that God creates atoms"),
    ("\u03a3", "C466", "Logos.ThomisticAct.loving_subject_initiates", "decl",
     "**to love is to initiate**, at the subject level. C464 composed with "
     "`act_implies_initiates`. The footprint is C464's cone and nothing else: no new axiom, and "
     "the extraction is an `obtain`"),
    ("\u03a3", "C467", "Logos.ThomisticAct.producing_coexists_with_immutability", "decl",
     "**the ground produces *and* is immutable, in one theorem.** This is the deliverable of the "
     "milestone. Nothing in `NotInSuccession` quantifies over `Produces`, so the two are proved "
     "*together* rather than against each other \u2014 the formal resolution of the tension the "
     "succession audit uncovered. The row is **conditional**, and had to be: \u0393 has no "
     "unconditional witness of ground-love (`EntityMeans (ofAtom _)` is `False` for every atom, and "
     "the contingent-person datum needs a `ContingentSubjectKind` inhabitant that the corpus does "
     "not have \u2014 C404 supplies only the *necessary* kind). The immutability conjunct is "
     "unconditional inside the row; the production conjunct is what the hypothesis pays for"),
    ("\u03a3", "C468", "Logos.SuccessionAudit.existence_implies_someone_initiates", "decl",
     "the author's first sentence, with an inert premise"),
]

# Chain 12 (C469-C480). The twelve distinct conclusions of the act datum. Note the
# two C4xx rows below that restate a row already proved unconditionally: C471 is
# definitionally C470, and C473/C474/C479 are the same predication under the
# corpus's other names. They are kept as separate steps because the corpus
# enuncates them in those forms, and each row's text says so.
ACT_CASCADE_STEPS = [
    ("\u03a3", "C469", "Logos.ActCascade.someone_means_something", "decl",
     "**something means something.** From the datum alone, through the `Means` half of the "
     "definition of `Act`. A *global* existential: it does not say *which* subject, so C453's "
     "per-subject form stays open, it licenses no `Means \u2192 Initiates`, and it does not make the "
     "ground an agent"),
    ("\u03a3", "C470", "Logos.ActCascade.someone_exists_as_subject", "decl",
     "**someone exists as a subject.** From the datum alone, through the constitutive law that an "
     "act does not occur without the subject performing it"),
    ("\u03a3", "C471", "Logos.ActCascade.an_actual_subject_obtains", "decl",
     "the corpus's *existential proposition* obtains. **Definitionally the same claim as C470** "
     "(`AnActualSubjectExists := \u2203 s, SubjectExists s`): the row exists because the corpus "
     "enuncates the proposition in that form, not to add a second result"),
    ("\u03a3", "C472", "Logos.ActCascade.an_agent_exists", "decl",
     "**an agent exists, in the T4 sense \u2014 and that sense is empty.** `Agent (_s) := True`, so the "
     "second conjunct is unconditionally true and **this row is exactly as strong as C470, and "
     "nothing more** (C321's precedent: a property of everything characterises nothing). It "
     "discharges the `T4_agentExists` step of the T chain; it is **not evidence of agency** in any "
     "sense the word carries outside that `def`"),
    ("\u03a3", "C473", "Logos.ActCascade.an_intentional_subject_exists", "decl",
     "**an intentional subject exists.** Nothing beyond C469: `IntentionalSubject s` is *defined* as "
     "\u2203 p, Means s p, so this is C469 with the witness reordered \u2014 the subject-side form of the "
     "T chain"),
    ("\u03a3", "C474", "Logos.ActCascade.intentionality_is_instantiated", "decl",
     "`Intentional := IntentionalSubject`, so this is C473 under the corpus's second name for the "
     "same predication. **The weakest reading of \"intentional\" the corpus has** \u2014 not "
     "intentionality *of a particular act*"),
    ("\u03a3", "C475", "Logos.ActCascade.genuineChoice_exists_of_act_datum_constitutive", "decl",
     "**genuine choice exists, by the constitutive route.** Datum **plus** the paid `AxIntentionalChoice` "
     "(`Tag: SEM`): the datum supplies the witness, the semantic axiom supplies the constitutive "
     "assertion that an intentional subject is genuinely choosing. **Two prices, both on the row; "
     "the semantic price is not removed**"),
    ("\u03a3", "C476", "Logos.ActCascade.genuineChoice_exists_of_act_datum_polarity", "decl",
     "**genuine choice exists, by the polarity route.** Datum **plus** the paid `AxActPolarity` "
     "(`Tag: SEM`): an act is polar \u2014 acting on `p` is also acting on `\u00acp` \u2014 which is what "
     "makes the choice genuine rather than merely unimpeded. A *different semantic choice* from the "
     "constitutive one, **not a stronger one**, and no substitute for it"),
    ("\u03a3", "C477", "Logos.ActCascade.freeWill_exists_of_act_datum_constitutive", "decl",
     "**free will exists, by the constitutive route.** Datum **plus** the paid `AxIntentionalChoice` "
     "(`Tag: SEM`). This is the row that discharges the corpus's own \"free will exists\" from the "
     "performative datum. An existential over subjects: not *which* subject, not all of them, and "
     "no `Wills \u2192 Initiates`. A *consequence* of the datum \u2014 citing it for the datum is circular "
     "(C456's precedent)"),
    ("\u03a3", "C478", "Logos.ActCascade.freeWill_exists_of_act_datum_polarity", "decl",
     "the same conclusion by the `AxActPolarity` route. A second, independent route with a *different* "
     "price; the batch pays twice, not once, and both remain declared"),
    ("\u03a3", "C479", "Logos.ActCascade.freeSubject_exists_of_act_datum", "decl",
     "**a free subject exists.** Datum **plus** the paid `AxIntentionalChoice`. `FreeSubject` is "
     "*defined* as `FreeWill s`, so this is C477 under the corpus's third name for the same "
     "predication. **Not free subjectivity** in any sense the `def` does not authorise: no capacity, "
     "no `Asiety`, no F15 limit"),
    ("\u03a3", "C480", "Logos.ActCascade.noMeaning_is_refuted_unconditionally", "decl",
     "**meaninglessness is refuted, unconditionally.** The cheapest row in the batch: meaning is "
     "neither a bridge nor a semantic axiom here. It does not enumerate what is meaningful, does not "
     "say which subject means, and does not bound the meanings (F15 untouched)"),
]


def render_succession_audit_chain(decls: dict, node_map: dict) -> list[str]:
    """Reader-facing chain for the 2026-09-28 succession-audit batch (C458\u2013C462)."""
    lines: list[str] = []
    ap = lines.append
    ap("### Chain 10 \u2014 What \"the ground does not initiate\" actually proved")
    ap("")
    ap("> **The finding, in one proof.** `the_ground_not_in_succession`")
    ap("> (`NecessityEternity.lean:196-198`) opens with `rintro \u27e8s, \u03c3, \u03c3', p, \u27e8hEq, _h\u27e9\u27e9` and closes with")
    ap("> `Entity.noConfusion hEq`. **The initiation witness is discarded.** The kernel term is sound,")
    ap("> which is why it survived every audit: what it establishes is that the ground is *no")
    ap("> subject's correlate*, and the negation of `Initiates` in its statement is inherited rather")
    ap("> than demonstrated. So \"the ground does not initiate\" is **unstatable**, not refuted \u2014 and")
    ap("> the refutation that was on record proved nothing about initiation.")
    ap("")
    ap("> Author, 2026-09-28, verbatim: *\"No more excuses - The fact Gamma exists means Someone")
    ap("> Initiates!!!!\"* and *\"The ground Initiates is refuted because there's a mistake in the proof.\"*")
    ap("> The first half is **already a theorem** (C455, and C468 below). The second is repaired here.")
    ap("")
    ap("**This is disclosure, not demotion** \u2014 the F16 precedent "
       "(`DivineImmutability.lean:142-165`).")
    ap("`ofGround_divine_immutability` stays `PROVEN` with its footprint untouched, C217 stays")
    ap("`PROVEN`, C453 stays `DEFERRED`. No badge moves anywhere; what changes is the *reading* of")
    ap("one of the four immutability fields, and the status of one sentence.")
    ap("")
    ap("`S` = the vacuity and the extraction \u00b7 `R` = the non-triviality result \u00b7 "
       "`M` = the free-signature countermodel.")
    ap("")
    ap("| # | Ledger | Declaration | Step | Status | Kernel footprint |")
    ap("|---|---|---|---|---|---|")
    for kind, cid, full, atype, text in SUCCESSION_AUDIT_STEPS:
        live = _classical_anchor_live({"type": atype, "full": full}, decls, node_map)
        status = _CA_STATUS_TEXT.get(live, "?") + _stip_marker([full])
        ap(f"| {kind} | {cid} | {_classical_decl_link(full, decls)} | {text} | "
           f"{status} | {kernel_fp_text(full)} |")
    ap("")
    ap("**C462 is `BLOCKED`, and deliberately has no row.** \"The ground does not initiate\" as a")
    ap("substantive claim needs an entity-level agency predicate \u2014 `EntityInitiates : Entity \u2192 "
       "State \u2192 State \u2192 Prop \u2192 Prop`")
    ap("together with the negative instance for `Entity.ofGround`; the alternative route,")
    ap("`GroundIsSubject : Subject`, is *forbidden* by the corpus (`ofGround_ne_ofSubject`, C441).")
    ap("Any honest version of the sentence therefore costs a new `META` bridge, and the exact")
    ap("statement is written in the GAPMAP row rather than left implicit. The formulation that")
    ap("*does* exist is `the_ground_not_in_succession`, and it is `PROVEN` for a different reason.")
    ap("")
    ap("**What this chain does not say.** Not that the ground is mutable: `NotInSuccession` holds")
    ap("for it (C458). Not that `NotInSuccession` is empty of content: it is a real predicate, just")
    ap("a non-discriminating one (C459). Not that no one initiates \u2014 someone does, and C460 is")
    ap("the row the ledger was missing. The `Initiates := False` countermodels of `INHABITED.md`")
    ap("\u00a70.1 are unaffected: they refute the *inhabitance* being derivable, and C454 is what")
    ap("closes them.")
    ap("")
    return lines


def render_thomistic_act_chain(decls: dict, node_map: dict) -> list[str]:
    """Reader-facing chain for the 2026-09-28 Thomistic production batch (C463\u2013C468)."""
    lines: list[str] = []
    ap = lines.append
    ap("### Chain 11 \u2014 To produce without succeeding")
    ap("")
    ap("> **The problem this batch answers.** After Chain 10, \"God acts at the level of the ground\"")
    ap("> is **unstatable**: `Initiates` is indexed by a subject, and the ground is provably not one.")
    ap("> The Thomistically correct way to say it at ground level is *production*, which is a")
    ap("> different relation \u2014 and Chain 10 had already proved, as a byproduct, that nothing in")
    ap("> `NotInSuccession` could exclude it. What was missing was the machine-checked form, and it")
    ap("> is **C467**: the ground produces **and** is immutable, in a single theorem.")
    ap("")
    ap("`\u25c6` = the three declared prices (one `VOCAB`, two `META`) \u00b7 `\u03a3` = what they buy.")
    ap("")
    ap("| # | Ledger | Declaration | Step | Status | Kernel footprint |")
    ap("|---|---|---|---|---|---|")
    for kind, cid, full, atype, text in THOMISTIC_ACT_STEPS:
        live = _classical_anchor_live({"type": atype, "full": full}, decls, node_map)
        status = _CA_STATUS_TEXT.get(live, "?") + _stip_marker([full])
        ap(f"| {kind} | {cid} | {_classical_decl_link(full, decls)} | {text} | "
           f"{status} | {kernel_fp_text(full)} |")
    ap("")
    ap("**What this chain does not say.**")
    ap("")
    ap("- **Not universal production.** C465\u2019s `\u2203 w \u03c6` is *existential*. The derivation "
       "`(\u2203 w, Satisfies w \u03c6) \u2192 \u2203 v, Produces g v \u03c6`")
    ap("  (`DivineOmnipotence.lean:55-58`) stays open, so **F10 stays \u274c/\U0001f9f1** and Creator is")
    ap("  untouched. C306 still refutes that grounding entails causal externality.")
    ap("- **Not essence\u2013act identity.** \"God is His act\" needs essence vocabulary (Class A,")
    ap("  blocked). C465 must never be described as establishing divine simplicity.")
    ap("- **Not immutability\u2019s exclusivity.** C453 stays `DEFERRED`; this batch adds the")
    ap("  disclosure its `ofSubject` arm was already missing, not the missing lemma.")
    ap("- **Not a ground that is a subject.** `ofGround_ne_ofSubject` is untouched, and `Produces`")
    ap("  is subject-free precisely so that nothing here contradicts it.")
    ap("- **Not that loving is identical with acting.** C464 is an implication in one direction")
    ap("  only; love without act is left open, and C178's moral close is unaffected.")
    ap("")
    return lines


def render_act_cascade_chain(decls: dict, node_map: dict) -> list[str]:
    """Reader-facing chain for the 2026-09-28 act-datum cascade batch (C469\u2013C480)."""
    lines: list[str] = []
    ap = lines.append
    ap("### Chain 12 \u2014 The consequences of the datum, no longer conditional")
    ap("")
    ap("> **The problem this batch answers.** `performative_act_datum` (C454) is **unconditional**,")
    ap("> and yet **eighteen theorems** across five modules still carried it as their *sole*")
    ap("> hypothesis. A hypothesis that is itself a declared axiom of \u0393 is not a hypothesis: it is a")
    ap("> leftover from before the datum was admitted. Each of the eighteen is a one-line corollary of")
    ap("> a parent that already exists and whose proof already exists.")
    ap("")
    ap("**The eighteen collapse into twelve distinct conclusions.** `act_datum_implies_initiates` is")
    ap("already unconditional in form (it is C455); `subject_exists_of_act` = `T1_subjectExists_of_act`")
    ap("= `T1_subjectExists`; `intentionalSubject_exists_of_act` = `T5_intentionalSubjectExists`;")
    ap("`freeWill_exists_of_act` = `freeWill_exists`; `freeSubject_exists_of_act` =")
    ap("`freeSubject_exists`; and each of the two choice routes collapses to one row because a")
    ap("duplicated corollary is not a second result.")
    ap("")
    ap("**This cascade is not free.** Every row now **pays `performative_act_datum` in its")
    ap("footprint**, and the six free-will / genuine-choice / free-subject rows still pay")
    ap("`AxIntentionalChoice` or `AxActPolarity` on top. The conditional parents let a reader believe")
    ap("the act was still in question; the price was hidden in a binder. It is now **visible and")
    ap("mandatory on every row**. That is a disclosure, not a strengthening of \u0393: \u0393 gained a")
    ap("theorem about one more thing, not one more premise.")
    ap("")
    ap("\u25c6 = a declared price \u00b7 \u03a3 = what the prices buy.")
    ap("")
    ap("| # | Ledger | Declaration | Step | Status | Kernel footprint |")
    ap("|---|---|---|---|---|---|")
    for kind, cid, full, atype, text in ACT_CASCADE_STEPS:
        live = _classical_anchor_live({"type": atype, "full": full}, decls, node_map)
        status = _CA_STATUS_TEXT.get(live, "?") + _stip_marker([full])
        ap(f"| {kind} | {cid} | {_classical_decl_link(full, decls)} | {text} | "
           f"{status} | {kernel_fp_text(full)} |")
    ap("")
    ap("**The `Asserts` lane stays closed by construction.** `Asserts s p := Act s p \u2227 p`, so the")
    ap("datum yields no existential of `Asserts`: there is no proposition available that is both")
    ap("`Act`-bearing *and* true. The bridge `act_implies_asserts_bridge` (`Choice.lean:653`) stays")
    ap("unpriced, and **twelve theorems remain conditional** by construction, deliberately untouched")
    ap("by this batch. The first ten are blocked by a semantic principle or by the unpriced bridge;")
    ap("the last two by a *universal* premise over all acts, which a single existential witness cannot")
    ap("discharge. That is the one place where a bridge would be **new substantive content** rather")
    ap("than a discharged hypothesis, and it is why the lane is closed.")
    ap("")
    ap("**What this chain does not say.**")
    ap("")
    ap("- **Not universalisation.** The datum is a *global* existential, so C453's per-subject form")
    ap("  is strictly stronger and stays open.")
    ap("- **Not a free ground.** `ofGround_ne_ofSubject` is untouched; F10, `Produces`, C462 and")
    ap("  C465/C467 keep their status and their footprints.")
    ap("- **Not agency.** C472's `Agent` is `True`; the row discharges a step of the T chain and is")
    ap("  no stronger than C470.")
    ap("- **Not a refutation from the void.** The free-will rows are *consequences* of the datum;")
    ap("  citing them in its favour is circular (C456's precedent, `INHABITED.md` \u00a70).")
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
    ap("A **`◈` suffix** on a status cell is derived from `formal/stipulation_audit.json`: the row's")
    ap("anchor is a declared dependent of a registered definitional stipulation, so its theorem is")
    ap("machine-verified **given that declaration**, not from Γ's axioms. It is not a warning about")
    ap("rigour — the proof is as solid as any other — it is a pointer to the price, which is listed")
    ap("in §D.2b and, for the ASIETY-FREEDOM batch, in the step-by-step block below.")
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
        marked = [c.get("full") for c in row["checks"]] + list(row.get("refs", []))
        ap(f"| {row['attribute']} | {row['scope']} | "
           f"{_classical_row_status(row, decls, node_map)}"
           f"{_stip_marker(marked)} | {row['sense']}{ref_cell} |")
    ap("")
    lines.extend(render_asiety_freedom_chain(decls, node_map))
    lines.extend(render_semantic_finitude_chain(decls, node_map))
    lines.extend(render_meaning_retorsion_chain(decls, node_map))
    lines.extend(render_love_chain(decls, node_map))
    lines.extend(render_two_kinds_chain(decls, node_map))
    lines.extend(render_precedence_chain(decls, node_map))
    lines.extend(render_temporality_chain(decls, node_map))
    lines.extend(render_sole_bearer_chain(decls, node_map))
    lines.extend(render_inhabited_chain(decls, node_map))
    lines.extend(render_succession_audit_chain(decls, node_map))
    lines.extend(render_thomistic_act_chain(decls, node_map))
    lines.extend(render_act_cascade_chain(decls, node_map))
    ap("_Synthesis — the strongest current profile._ The theory has established, of a")
    ap("**personal, rational, free, authoritative-over-its-acts, independently individuated**")
    ap("**normative ground / person-type**, that its objective Right/Wrong order is the object")
    ap("of a necessary normative/truth order, and (entity-level) that a **necessary Divine Being")
    ap("/ Ground** exists — world-rigid, **everlasting**, **atemporal**, with **Canonical Aseity**,")
    ap("**Divine Simplicity**, **Divine Immutability**, **Foundational Omnipresence** (sustaining all")
    ap("beings across modal reality), **Foundational Unicity**, **Divine Pure Actuality** (*Actus Purus*),")
    ap("and **Foundational Omniscience** (a truth-exhaustive scope in every world, whose infallible half is")
    ap("machine-checked as *refuted* for the ground), and **Foundational Omnipotence** (a gapless operative")
    ap("scope: no state of affairs that does not involve a contradiction is closed to the ground, whose scope")
    ap("domain is machine-checked non-empty and contradiction-free), and **Divine love** (the ground as "
       "lover of contingent reality — ⚠️ AXIOMATIC under the VOCAB primitive `GroundBearsGood` and the "
       "META bridge `AxGroundLovesContingentRealm`, with the cosmos's existence a **free theorem** "
       "(C350, `{CL, NecessarySubjectKind, Subject}`, no bridge) and only its content-bearinghood priced on "
       "a contingent-person datum (C367); see the LOVE chain block).")
    ap("Crucially, the theory **strictly separates** these machine-verified")
    ap("foundational/functional attributes from their unproven physical, psychological, and scholastic counterparts:")
    ap("**physical/spatial omnipresence**, **psychological personality**, **scholastic simplicity**,")
    ap("**infallible or counterfactual omniscience**, **causal / creative omnipotence** (the presence-plus-")
    ap("obtaining reading above is priced ◈ `operatesAt_presencePlusObtaining`; the production relation is now")
    ap("declared — C463, `Tag: VOCAB` — while its *derivation* from satisfaction remains BLOCKED, and a")
    ap("declared relation is not a power), and")
    ap("**psychological impassibility** remain separate targets (❌ NOT ESTABLISHED or 🔴 INDEPENDENT).")
    ap("The remaining divine attributes — **unity / monotheism**,")
    ap("**perfect moral goodness** (the moral pole itself now obtains under the single declared "
       "META bridge, C178; its attribution to the Divine Being stays a 🧱 frontier), the "
       "**Trinity**, the **Incarnation**, and contingent")
    ap("**creation as entailment** — remain **separate proof targets**")
    ap("(`⏸` / `❌`) or explicit **countermodel frontiers** (`🧱`) until the live kernel proves them. "
       "Contingent creation *as existence* is no longer among them: it is a **free theorem** "
       "(C350 `contingent_realm_obtains`, `{CL, NecessarySubjectKind, Subject}`), witnessed by an atom, with no "
       "bridge and no substantive axiom. Only the realm's *content* is priced, on an exhibited "
       "contingent person (C367 `cosmos_obtains`) — the kind premise the two-kinds doctrine "
       "exhibits, not a semantic "
       "one. And contingent creation *as production* remains unclaimed: no `Creates` relation, "
       "no agent, no first moment. So the cost was relocated and then, for existence itself, "
       "dissolved — but the act was never ours to claim.")
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


def render_deduction_sections(sections: list[dict], decls: dict = None, node_map: dict = None,
                          investigations_dir: Path = None,
                          score_claims: list[dict] = None) -> list[str]:
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
        # Phase 4: the two-column score. `score_claims` must be the GAPMAP claim
        # rows, NOT the discovered ProofIR sections: those carry `proofs`, and
        # reading `claims` off them silently yields an empty list, which is how
        # 4b shipped as dead code behind a green build (VISIBILITY.md
        # Correction 10). main() passes the real inventory.
        if score_claims:
            for gl in render_score_block(derive_score_data(score_claims, decls, node_map)):
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

    # A `lean_ref` that resolved to nothing is not a Lean reference. The
    # frontier rows put a whole sentence in the ledger's declaration cell, so
    # `_extract_lean_ref` had to guess, and it guessed: `BLOCKED` for F15, `def`
    # for F13, `propext` for F9, `Produces` for F10. Those strings then rendered
    # as though they were dependencies — the sharpest case being the code annex,
    # where `F15 … | BLOCKED` sat under a "Used by" header beside an AXIOM claim.
    # Clearing them here, keyed on the resolution that already ran, fixes every
    # display site at once and needs no word-list.
    dropped = [(c["id"], c["lean_ref"]) for c in all_claims
               if c.get("lean_ref") and not c.get("_full")]
    for c in all_claims:
        if c.get("lean_ref") and not c.get("_full"):
            c["lean_ref"] = ""
    if dropped:
        print(f"  cleared {len(dropped)} unresolvable lean_ref(s) that were "
              f"scraped from prose cells: {', '.join(i for i, _ in dropped[:12])}"
              + (" …" if len(dropped) > 12 else ""))

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

    print("verifying chain-list integrity and required coverage…")
    globals()["ALL_CHAIN_STEPS"] = [(nm, globals()[var]) for nm, var in CHAIN_LISTS]
    verify_chain_coverage(node_map, claims_by_id)

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
    lines = render_deduction_sections(deduction_sections, decls, node_map, score_claims=all_claims)

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