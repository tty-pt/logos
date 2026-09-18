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

Output: DEDUCTION.md at the repository root: the deduction chain, level by
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
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"
LEAN_DIR = FORMAL / "Logos"
GAPMAP_PATH = FORMAL / "GAPMAP.md"
DEPGRAPH_PATH = FORMAL / "depgraph.json"
OUT_PATH = ROOT / "DEDUCTION.md"

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
        # namespace tracking (files use a single `namespace Logos.X` block)
        namespaces: list[str] = []
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

            m = re.match(r"^namespace\s+([\w.]+)\s*$", stripped)
            if m:
                namespaces.append(m.group(1))
                i += 1
                continue
            m = re.match(r"^end(?:\s+([\w.]+))?\s*$", stripped)
            if m:
                if namespaces:
                    namespaces.pop()
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
            ns = ".".join(namespaces)
            full = f"{ns}.{name}" if ns else name
            stmt, end_line = _capture_statement(lines, ln, kind)
            string_value = ""
            if kind == "def":
                sv = re.match(r'^def\s+\S+\s*:\s*String\s*:=\s*"([^"]*)"\s*$', raw.strip())
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
    return para[:260]


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
    subst, vocab, cl = [], [], []
    for a in audit_footprint(full):
        if a.startswith("Logos."):
            base = a.rsplit(".", 1)[-1]
            r = _REGISTRY.get(base)
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


def render_index(sections, level_titles, claims_by_id, decls, node_map, graph):
    L = []
    ap = L.append
    ap("# Γ — Deduction Map (mapa da dedução)")
    ap("")
    ap("Versão derivada do estado formal atual. Este documento é **gerado** "
       "por `scripts/build_deduction.py` — não o edite à mão "
       "(regra de sincronização em `AGENTS.md`).")
    ap("")
    ap("- **Fonte Lean:** `formal/Logos/*.lean` (kernel-checked, `lake build` verde, sorryAx 0)")
    ap("- **Pegadas do kernel:** `formal/axiom_audit.json` (`#print axioms` por declaração — "
       "a pegada axiomática transitiva exata no kernel, meta-lógica incluída. Nota metodológica: "
       "a auditoria do kernel reporta dependências formais estritas; não certifica independentemente "
       "que as definições constitutivas não codifiquem compromissos substantivos)")
    ap("- **Tipos de axioma:** a linha `Tag:` (`VOCAB`/`SEM`/`META`) na docstring Lean de cada axioma")
    ap("- **Grafo de dependências:** `formal/depgraph.json` (LeanDepViz, kernel)")
    ap("- **Ledger GAPMAP:** [`formal/GAPMAP.md`](formal/GAPMAP.md) (IDs, refs de prosa, "
       "transcrição de estatuto/pegada — *verificada*, nunca usada como fonte)")
    ap("- **Prosa:** [`base.txt`](base.txt) (argumento §0–§29) · [`poem.txt`](poem.txt) (P1–P10) · [`theorems/`](theorems/)")
    ap("")
    ap("Regeneração: `python3 scripts/audit_footprints.py && python3 scripts/build_deduction.py`")
    ap("")
    ap("---")
    ap("")
    ap("## Legenda")
    ap("")
    ap("| Token | Significado |")
    ap("|---|---|")
    ap("| `✔` | teorema verificado pelo kernel, pegada sem axioma substantivo (vazia, `CL` ou só vocabulário) |")
    ap("| `⚠` | teorema verificado sob axiomas substantivos — quais, no próprio passo (`Segue de: … e do axioma …`) |")
    ap("| `◆` | declaração (`axiom`) — não derivada |")
    ap("| `✖` | em falta um lema nomeado (ver **Deferred / blocked**) |")
    ap("| `➖` | fora do âmbito deste marco |")
    ap("| `→` | dissolvido numa entrada já apresentada (`Vide …`) |")
    ap("| `CL` | meta-lógica clássica `{propext, Classical.choice, Quot.sound}` (D1, reportada pelo kernel) |")
    ap("| `✔` (só vocabulário) | teorema **axiom-free módulo o vocabulário primitivo declarado**: a pegada do kernel só contém vocábulos (`VOCAB`) que o próprio enunciado menciona, sem axioma substantivo (`SEM`/`META`/`TRANS`). Nota: `#print axioms` reporta apenas dependências formais do kernel; não certifica por si só que as definições não codifiquem compromissos constitutivos substantivos. Ex.: C25, C49, C51, C56, C62 (passos analíticos módulo vocabulário primitivo de agência/escolha). Inventário e justificação em [`VOCAB.md`](VOCAB.md); ver **Relatório de consistência** |")
    ap("| `An` | axioma exibido em bloco próprio (`### A1 ◆ …`) no 1.º passo que o usa; as linhas `Segue …` referenciam-no por `A#` |")
    ap("")
    ap("O estatuto de cada passo é **derivado** — função de (tipo do nó no kernel, "
       "pegada `#print axioms`, `Tag:` declarada dos axiomas) — e não transcrito do "
       "ledger. A transcrição GAPMAP é auto-verificada contra o derivado; o que "
       "diverge aparece como **erro de ledger** no **Relatório de consistência**.")
    ap("")
    ap("Etiquetas de axioma (o `Tag:` declarado na docstring Lean de cada axioma):")
    ap("")
    ap("| Tag | Significado |")
    ap("|---|---|")
    ap("| `SEM` | escolha semântica, com modelo de consistência registado |")
    ap("| `META` | ponte metafísica, com o preço tornado explícito |")
    ap("| `VOCAB` | vocabulário primitivo (relação que o próprio enunciado menciona) |")
    ap("")
    ap("Notação formal: cada passo mostra o *enunciado* em símbolos lógicos "
       "(traduzido do Lean), uma frase em inglês com o significado e a "
       "linha `Segue de:` — os teoremas-passo a partir dos quais decorre e "
       "o(s) axioma(s) do seu pé de kernel (`… e do axioma **A1** / … e dos "
       "axiomas **A1**, **A2**`, com `A#` definido no bloco do próprio axioma). "
       "As referências de código (ficheiro:linha, pegadas `#print axioms`, "
       "dependências e usos no grafo) ficam todas no **Anexo: código por passo**.")
    ap("")
    ap("---")
    ap("")
    ap("<details>")
    ap("<summary>Leitura da notação (símbolos ↔ Lean) →</summary>")
    ap("")
    ap("Cada passo é o teorema Lean real, escrito em símbolos. Os símbolos e "
       "os predicados-tipo usados:")
    ap("")
    ap("| Símbolo | Lean | Significado |")
    ap("|---|---|---|")
    ap("| `¬` · `∧` · `∨` · `→` | `Not` · `And` · `Or` · `Imp` | negação, conjunção, disjunção, implicação |")
    ap("| `φ ∨ ¬φ` | `Form.or φ (Form.not φ)` | fórmula da linguagem-objecto (não `Prop`) |")
    ap("| `□ τ` | `NecessarilyTrue τ` | verdade em todo o mundo (`∀ w, TrueAt w τ`) |")
    ap("| `¬◇ τ` | `NecessarilyFalse τ` | falso em todo o mundo (impossível: `∀ w, FalseAt w τ`) |")
    ap("| `□ p` | `Necessity p` | caixa ao nível de `Prop` (alias degenerado da identidade, `□p := p`) |")
    ap("| `□ₚ P` · `∀ w, P(w)` | `NecessityPH P` | caixa ao nível do mundo — a modalidade real |")
    ap("| `◇ p` | `Dia p` | possibilidade: `¬□(¬p)` |")
    ap("| `w ⊨ τ` | `TrueAt w τ` / `Satisfies w τ` | a fórmula τ é verdadeira no mundo w |")
    ap("| `w ⊭ τ` | `FalseAt w τ` | a fórmula τ é falsa no mundo w |")
    ap("| `atom n` | `Form.atom n` | proposição atómica n da linguagem-objecto |")
    ap("| `T p` | `T p` (`def T p := p`) | \"p é verdadeiro\" — a verdade é a identidade (E0) |")
    ap("| `IsFalse p` | `IsFalse p` | \"p é falso\" (`:= ¬ T p`) |")
    ap("| `N_T` ≡ `N_F` | `N_T` · `N_F` | absolutos: \"nada é verdadeiro\" · \"tudo é verdadeiro\" |")
    ap("| `A s p` · `Means s p` | `A s p` (`:= Means s p`) · `Means s p` (`:= ∃ w w', Initiates s w w' p`) | o acto de um sujeito s sobre um conteúdo p — a iniciação de um movimento |")
    ap("| `Subject` · `Person s` | `Subject` · `Person s` | sort de sujeitos · \"s é pessoa\" |")
    ap("| `Chooses s p q` | `Chooses s p q` | o sujeito s escolhe entre as alternativas p e q |")
    ap("| `Ground e τ` · `ExistsAt w e` | `Ground e τ` · `ExistsAt w e` | a entidade e fundamenta τ · e existe no mundo w |")
    ap("| `NecessaryEntity e` · `NecessarySubject s` | `NecessaryEntity e` · `NecessarySubject s` | e existe em todo o mundo · s persiste em todo o mundo |")
    ap("| `Correct s p` · `Incorrect s p` · `Fallible s p` | `Correct` · `Incorrect` · `Fallible` | juízo correto · incorreto · falível do sujeito s sobre p |")
    ap("| `Incompatible p q` · `Lovable s` · `Loves s₁ s₂` | `Incompatible` · `Lovable` · `Loves` | alternativas incompatíveis · s é amável · o amor de s₁ por s₂ |")
    ap("")
    ap("O **significado** de cada passo é dado em inglês a seguir ao seu "
       "enunciado (o original Lean está numa hiperligação).")
    ap("")
    ap("</details>")
    ap("")
    ap("---")
    ap("")
    ap("## Visão global do argumento")
    ap("")
    ap("```text")
    ap("§0  premissa arbitrária ≠ condição cuja negação destrói o ato de a negar")
    ap("      │")
    ap("§1  A(s,p)  (ato presente, EXIBIDO — teorema `Cogito`, sem axiomas)")
    ap("      │  T1 sujeito · T2 conteúdo · §4–§5 absolutos N_T/N_F refutam-se")
    ap("      │  T3 verdade-e-erro §6 · §7–§21 verdade/vontade/correção/consequência")
    ap("      ├──→ §22–§23 necessidade (excluded middle / não-contradição)")
    ap("      ├──→ §24a truthmaker atómico · T7 realidade necessária (AxGlobalGround)")
    ap("      ├──→ §24b pessoa · T8 fundamento pessoal (AxPersonalGround, META)")
    ap("      ├──→ §13–§15 escolha · T11 campo de escolha · T9 alternativas")
    ap("      └──→ P5/P7 pluralidade (derivada — par canónico C73, `{}`) · P7/P8 amor (T13·T14)")
    ap("                AxPersonStability (SEM) — 'de alguma forma'")
    ap("```")
    ap("")
    ap("Camadas de conclusão (base.txt §0): performativamente inegável → "
       "logicamente inegável → transcendentalmente necessário → "
       "metafisicamente necessário **se a ponte for demonstrada**.")
    ap("")
    ap("---")
    return L


def render_levels(sections, claims_by_id, decls, node_map, graph, already=None,
                  by_full=None, ax_id=None, ax_shown=None, axiom_full=None,
                  glosses=None):
    L = []
    ap = L.append
    for sec in sections:
        title = sec["title"]
        claims = sec["claims"]
        if not claims:
            continue
        if not title.startswith("Level"):
            continue
        ap(f"## {title}")
        ap("")
        for c in claims:
            full = c.get("_full")
            if full and full in decls:
                for line in axiom_intro(full, ax_id, ax_shown, decls, node_map,
                                        glosses, axiom_full):
                    ap(line)
            block = render_claim_detail(c, claims_by_id, decls, node_map, graph,
                                        by_full=by_full, already=already, ax_id=ax_id)
            ap("\n".join(block))
        ap("")
        ap("---")
        ap("")
    return L


def render_claim_detail(c, claims_by_id, decls, node_map, graph,
                        by_full=None, already=None, ax_id=None):
    """Philosopher-facing block: formal statement, EN meaning, claim-level
    provenance. No code references — those live in the code annex."""
    L = []
    ap = L.append
    full = c.get("_full")
    status = STATUS_BADGE.get(c["status"], c["status"])
    gloss = c.get("_gloss")
    italic = f"_{gloss}_" if gloss else ""

    if full and full in decls:
        d = decls[full]
        # repeated from an earlier section -> one-line cross-reference
        if already and full in already:
            ap(f"### {c['id']} · →")
            ap(f"*Vide **{already[full]}** (passo já apresentado).*")
            ap("")
            return L
        if already is not None:
            already[full] = c["id"]
        ap(f"### {c['id']} · {badge_for(c, decls, node_map)}")
        d = decls[full]
        raw = d["statement"]
        if d["kind"] == "theorem":
            raw = strip_theorem_head(raw)
        formal = f"`{short_stmt(humanise(trim_stmt(raw)))}`"
        if italic:
            ap(f"{formal} — {italic}")
        else:
            ap(formal)
        segs = []
        if full in graph["in"] and d["kind"] != "axiom":
            preds = []
            for fd in graph["in"][full]:
                if fd in decls and decls[fd]["kind"] == "axiom":
                    continue
                for i in (by_full or {}).get(fd, []):
                    if i not in preds:
                        preds.append(i)
            preds.sort()
            seg = segue_text(preds, axiom_refs_sorted(kernel_axiom_names(full, node_map), ax_id))
            if seg:
                if is_vocab_only(full):
                    seg += " (vocabulário do enunciado)"
                segs.append(seg)
        prose = c.get("prose")
        if prose:
            t_refs = " · ".join(f"[{t}](theorems/{t}.txt)" for t in find_t_refs(prose))
            segs.append(render_prose_link(prose) + (f" · {t_refs}" if t_refs else ""))
        if segs:
            ap(" — ".join(segs))
    else:
        ap(f"### {c['id']} · {badge_for(c, decls, node_map)}")
        if italic:
            ap(italic)
    ap("")
    return L


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


def render_axiom_inventory(node_map, claims_by_id, glosses, ax_id=None):
    L = []
    ap = L.append
    n_axioms = sum(1 for n in node_map.values() if n["kind"] == "axiom")
    ap(f"## Inventário de axiomas ({n_axioms} declarações)")
    ap("")
    ap("| Axioma | Nº | Tag | Significado (EN) / preço | Depende dele (claims) |")
    ap("|---|---|---|---|---|")
    axioms = sorted(node_map.values(), key=lambda n: n["fullName"])
    for n in axioms:
        if n["kind"] != "axiom":
            continue
        base = n["fullName"].rsplit(".", 1)[-1]
        r = _REGISTRY.get(base, {"tag": "?", "gloss": "—"})
        tag = r["tag"]
        why = r["gloss"] or "—"
        deps = [c["id"] for f, c in claims_by_id.items()
                if any(a.rsplit(".", 1)[-1] == base for a in audit_footprint(f))]
        deps_txt = ", ".join(sorted(set(deps))) if deps else "—"
        nid = ax_id.get(base, "—")
        ap(f"| `{base}` | {nid} | `{tag}` | {why} | {deps_txt} |")
    ap("")
    ap("Detalhe do kernel:")
    ap("")
    for n in sorted(node_map.values(), key=lambda n: n["fullName"]):
        if n["kind"] == "axiom":
            ap(f"- `{n['fullName']}`")
    ap("")
    ap("---")
    return L


def render_faith_deferred(sections, claims_by_id, decls, node_map, graph, already=None,
                          by_full=None, ax_id=None, ax_shown=None, axiom_full=None,
                          glosses=None):
    """Deferred / blocked / faith sections: summary table + detail blocks."""
    L = []
    ap = L.append
    for sec in sections:
        title = sec["title"]
        claims = sec["claims"]
        if not claims or title.startswith("Level"):
            continue
        if all(c["status"] in ("PROVEN", "PROVEN↑", "AXIOM") and not c["id"].startswith("F")
               for c in claims):
            continue
        ap(f"## {title}")
        ap("")
        ap("| ID | Prosa | Status | Nota / lema em falta |")
        ap("|---|---|---|---|")
        for c in claims:
            note = c.get("note") or ""
            ap(f"| {c['id']} | {c['prose']} | {STATUS_BADGE.get(c['status'], c['status'])} | {note} |")
        ap("")
        for c in claims:
            full = c.get("_full")
            if full and full in decls:
                for line in axiom_intro(full, ax_id, ax_shown, decls, node_map,
                                        glosses, axiom_full):
                    ap(line)
            block = render_claim_detail(c, claims_by_id, decls, node_map, graph,
                                        by_full=by_full, already=already, ax_id=ax_id)
            ap("\n".join(block))
        ap("")
        ap("---")
    return L


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
      declarations (e.g. C59 referencing Spike_M5.strongTruthExists).
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
    """Compute the displayed status badge for each claim as emitted in DEDUCTION.md."""
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
    ap("## Relatório de consistência (kernel ↔ GAPMAP)")
    ap("")
    all_claims = [c for s in sections for c in s["claims"]]

    # 3-way claim classification
    claims_class = classify_claims(all_claims, decls, node_map)
    found_claims = claims_class["FOUND"]
    retired_blocked = claims_class["RETIRED_BLOCKED"]
    missing_claims = claims_class["MISSING"]

    ap(f"- Claims do GAPMAP com teorema localizado no kernel (FOUND): "
       f"**{len(found_claims)}** / {len(all_claims)}")
    glossed = [c for c in all_claims if c.get("_gloss")]
    ap(f"- Steps com **significado em inglês**: **{len(glossed)}** / {len(all_claims)}"
       + ("" if len(glossed) == len(all_claims)
          else f" · **sem gloss:** {', '.join(c['id'] for c in all_claims if not c.get('_gloss'))}"))

    if missing_claims:
        ap(f"- **Claims com teorema em falta (MISSING — teorema referenciado não localizado no kernel) ({len(missing_claims)}):**")
        for c in missing_claims:
            ap(f"  - `{c['id']}` ref `{c['lean_ref']}` — {c['prose']}")

    if retired_blocked:
        ap(f"- **Claims retirados / bloqueados (RETIRED/BLOCKED — fora da dedução ativa) ({len(retired_blocked)}):**")
        for c in retired_blocked:
            ap(f"  - `{c['id']}` (`{c['status']}`) ref `{c['lean_ref'] or '—'}` — {c['prose']}")

    kern_theorems = {f for f, n in decls.items() if n["kind"] in ("theorem", "example")}
    covered = {c.get("_full") for c in all_claims if c.get("_full")}
    missing = sorted(f for f in kern_theorems - covered if f in node_map)
    if missing:
        ap(f"- Teoremas no kernel **sem claim** no GAPMAP ({len(missing)}): "
           + ", ".join(f.replace("Logos.", "") for f in missing))
    else:
        ap("- Todos os teoremas do kernel têm claim (ou ref mapeada).")

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

    ap(f"- **Estatuto derivado do kernel** (#print axioms + `Tag:` dos axiomas): "
       f"**{cnt_prov} ✔** · **{cnt_up} ⚠** · **{cnt_ax} ◆** (passos únicos detalhados no mapa)")
    ap(f"- **Inventário reconciliado de claims ({len(all_claims)} no total):** "
       f"{cnt_prov + cnt_up} passos únicos ativos ({cnt_prov} ✔ + {cnt_up} ⚠) · "
       f"{cnt_repeat} repetidos / dissolvidos (→) · "
       f"{cnt_blocked} bloqueados / em falta (✖) · "
       f"{cnt_deferred} diferidos (➖)"
       + (f" · {cnt_other} outros ({', '.join(b for b in detailed_badges.values() if b not in ('✔', '⚠', '◆', '→', '✖', '➖'))})" if cnt_other else ""))

    status_div = []
    for c in steps:
        st = _clean_status((c.get("status") or "").strip())
        dv = derived_for(c, node_map)
        if st != dv:
            status_div.append((c["id"], st, dv))
    if status_div:
        ap(f"- **Divergências de estatuto GAPMAP × derivado ({len(status_div)} — "
           f"corrigir o ledger GAPMAP):**")
        for cid, st, dv in status_div:
            ap(f"  - `{cid}` GAPMAP `{st}` vs derivado `{dv}`")
    else:
        ap("- Estatuto GAPMAP × derivado: **sem divergências** (transcrição verificada).")

    # --- footprint transcription check -------------------------------------
    subst_claims = [c for c in steps if derived_for(c, node_map) == "PROVEN↑"]
    if subst_claims:
        ap(f"- **Steps ⚠ sob axioma substantivo (SEM/META)** "
           f"({len(subst_claims)}): " + ", ".join(sorted(c["id"] for c in subst_claims)))
    vocab_only = [c for c in steps if is_vocab_only(c["_full"])]
    if vocab_only:
        ap(f"- **Exibidos ✔ por só-vocabulário (axiom-free módulo vocabulário declarado)** "
           f"(pegada do kernel só com vocábulos VOCAB do próprio enunciado — SEM/META/TRANS nenhum): "
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
        ap(f"- **Divergências de pegada kernel × GAPMAP** "
           f"({len(divs)} — corrigir o ledger GAPMAP):")
        for cid, ks, gs in divs:
            ap(f"  - `{cid}` kernel `{ks}` vs GAPMAP `{gs}`")
    else:
        ap("- Pegada kernel × GAPMAP: **sem divergências**.")
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
        ap(f"- **Grafo (closure) × audição (#print axioms) divergem em "
           f"{len(fid)} claims** (subconta transitiva do depviz — toolchain, "
           f"não ledger; a audição manda):")
        for cid, au, cl in fid:
            ap(f"  - `{cid}` audição `{{{', '.join(au)}}}` vs grafo `{{{', '.join(cl)}}}`")
    # --- axiom registry / coverage ------------------------------------------
    kern_axioms = {n["fullName"] for n in node_map.values() if n["kind"] == "axiom"}
    known = {r["full"] for r in _REGISTRY.values()}
    extra = kern_axioms - known
    ap(f"- Axiomas declarados no kernel: **{len(kern_axioms)}**"
       + (f" · **fora do registo (sem `Tag:`):** {', '.join(sorted(extra))}" if extra else "")
       + " — **todos com `Tag:` na docstring Lean**" if not extra else "")
    return L


def render_code_annex(sections, claims_by_id, decls, node_map, graph):
    """Per-claim code references: Lean decl, file:line, kernel footprint,
    GAPMAP footprint, Lean dependencies and usage. Everything technical the
    philosopher-facing map intentionally omits."""
    L = []
    ap = L.append
    ap("## Anexo: código por passo")
    ap("")
    ap("<details>")
    ap("<summary>Declaração Lean, ficheiro:linha, pegadas e dependências de código, por passo →</summary>")
    ap("")
    ap("| ID | Declaração Lean | Ficheiro#L | Axiomas (kernel) | Pegada GAPMAP | Depende (Lean) | Usado por |")
    ap("|---|---|---|---|---|---|---|")
    for sec in sections:
        for c in sec["claims"]:
            cid = c["id"]
            g = c.get("footprint") or "—"
            full = c.get("_full")
            if not full or full not in decls:
                lr = c.get("lean_ref") or "—"
                ap(f"| {cid} | — | — | — | {g} | {lr} | — |")
                continue
            d = decls[full]
            kern = kernel_fp_text(full)
            deps = dep_list(graph["in"].get(full, set()), claims_by_id, decls)
            rds = dep_list(graph["out"].get(full, set()), claims_by_id, decls)
            ap(f"| {cid} | `{full}` | {le_line(d['file'], d['line'])} | `{kern}` | {g} | {deps} | {rds} |")
    ap("")
    ap("</details>")
    ap("")
    ap("---")
    return L


def render_appendix(sections, decls, node_map, claims_by_id, graph, level_map):
    L = []
    ap = L.append
    ap("## Índice de declarações do kernel")
    ap("")
    ap("<details>")
    ap("<summary>Todos os teoremas/defs user-authored, por módulo (linha e axiomas de kernel) →</summary>")
    ap("")
    for mod in sorted(set(d["module"] for d in decls.values())):
        dcl = {f: d for f, d in decls.items() if d["module"] == mod}
        if not dcl:
            continue
        ap(f"### `{mod}`")
        ap("")
        ap("| Nome | Tipo | Linha | Statement (Lógica) | Axis |")
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


def axiom_intro(full, ax_id, ax_shown, decls, node_map, glosses, axiom_full):
    """Titled axiom block (`### A1 ◆ …`) immediately before the step that
    first uses it; each axiom appears exactly once in the whole doc. The
    title is the axiom's own docstring meaning; the tag is its declared type."""
    L = []
    base_new = []
    for base in kernel_axiom_names(full, node_map):
        if base in ax_id and base not in ax_shown:
            base_new.append(base)
            ax_shown.add(base)
    for base in sorted(base_new, key=lambda b: int(ax_id[b][1:])):
        r = _REGISTRY.get(base, {"tag": "?", "gloss": "", "full": base})
        fullname = r.get("full") or axiom_full.get(base) or base
        d = decls.get(fullname, {})
        stmt = short_stmt(humanise(trim_stmt(d["statement"] or ""))) if d.get("statement") else ""
        gloss = glosses.get(fullname, "") or r.get("gloss", "")
        title = gloss.split(".")[0] if gloss else base
        L.append(f"### {ax_id[base]} ◆ {title} · `{r.get('tag', '?')}`")
        if stmt:
            L.append(f"`{trim_stmt(stmt)}`" + (f" — _{gloss}_" if gloss and gloss != title else ""))
        elif gloss:
            L.append(f"_{gloss}_")
        L.append("")
    return L


def segue_text(claims: list, ax_refs: list) -> str:
    """"Segue de: **C16**, **C18** e do axioma **A3**" — the provenance
    line names the theorems and the kernel axiom footprint together."""
    cj = ", ".join(f"**{c}**" for c in claims)
    if len(ax_refs) == 1:
        ax = f"do axioma {ax_refs[0]}"
    elif len(ax_refs) > 1:
        ax = "dos axiomas " + ", ".join(ax_refs)
    else:
        ax = ""
    if cj and ax:
        return "Segue de: " + cj + " e " + ax
    if cj:
        return "Segue de: " + cj
    if ax:
        return "Segue " + ax
    return ""


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

    print("loading axiom registry (Tag: from Lean docstrings)…")
    _REGISTRY = load_axiom_registry(decls, node_map)
    print(f"  {len(_REGISTRY)} axioms tagged: "
          + ", ".join(f"{b}({r['tag']})" for b, r in sorted(_REGISTRY.items())))

    print("resolving meanings (EN) from declarations…")
    glosses = {f: info["doc"] for f, info in decls.items() if info.get("doc")}
    for f, info in decls.items():
        if info.get("stringValue"):
            glosses[f] = info["stringValue"]
    # claim-only meanings: mini stub module Logos/ClaimMeanings.lean
    claim_stub = {
        "C19": "Logos.ClaimMeanings.C19",
        "C59": "Logos.ClaimMeanings.C59",
        "F2": "Logos.ClaimMeanings.F2",
        "F3": "Logos.ClaimMeanings.F3",
        "F4": "Logos.ClaimMeanings.F4",
        "F5": "Logos.ClaimMeanings.F5",
        "F6": "Logos.ClaimMeanings.F6",
        "F1b": "Logos.ClaimMeanings.F1b",
        "F7": "Logos.ClaimMeanings.F7",
        "F8": "Logos.ClaimMeanings.F8",
        "F9": "Logos.ClaimMeanings.F9",
        "Q7.2": "Logos.ClaimMeanings.Q7_2",
        "C69": "Logos.ClaimMeanings.C69",
        "C70": "Logos.ClaimMeanings.C70",
        "C71": "Logos.ClaimMeanings.C71",
        "C72": "Logos.ClaimMeanings.C72",
    }
    for cid, full in claim_stub.items():
        info = decls.get(full)
        if info:
            glosses[cid] = info.get("stringValue") or info.get("doc") or ""
    print(f"  {len(glosses)} meanings resolved from code")

    print("resolving claims → kernel declarations…")
    claims_by_id = {}
    resolved = 0
    for c in all_claims:
        ref = c.get("lean_ref") or ""
        if not ref:
            c["_gloss"] = glosses.get(c["id"], "")
            continue
        r = resolve(ref, decls, node_map, c.get("level_key", ""))
        if r is None and "." not in ref:
            # bare name: try all modules, require unique match
            matches = [f for f in decls if f.rsplit(".", 1)[-1] == ref]
            if len(matches) == 1:
                r = matches[0]
        c["_full"] = r
        if r:
            c["_name"] = r.rsplit(".", 1)[-1]
            claims_by_id[r] = c
            resolved += 1
        c["_gloss"] = glosses.get(r or "", "") or glosses.get(c["id"], "")
    print(f"  {resolved} claims linked to a kernel declaration")

    for c in all_claims:
        if c.get("_full"):
            claims_by_id.setdefault(c["_full"], c)

    by_full = {}  # fullname -> step-claim ids that resolve to it (steps only:
    # curator cross-refs never name a deduction premise — those fall back to
    # the raw Lean declaration name in `Segue de:` lines)
    for c in all_claims:
        if c.get("_full") and derived_for(c, node_map) is not None:
            by_full.setdefault(c["_full"], []).append(c["id"])

    # curated footprints, `as/via Cxx` resolved to the concrete axiom set
    fp_by_id = {c["id"]: (c.get("footprint") or "") for c in all_claims}
    for c in all_claims:
        c["_curated_fp"] = expand_footprint(c["id"], fp_by_id)

    print("verifying gloss relation consistency…")
    verify_gloss_relations(all_claims, decls, graph)

    print("rendering DEDUCTION.md…")
    lines = []
    print("assigning axiom ids A1..An…")
    ax_id = build_ax_id(sections, graph["node_map"])
    axiom_full = axiom_full_map(graph["node_map"])
    ax_shown: set = set()
    print(f"  {len(ax_id)} axioms named in the flow")

    already = {}  # fullname -> first claim id that detailed it (dedupe repeats)
    lines += render_index(sections, None, claims_by_id, decls, node_map, graph)
    lines += render_levels(sections, claims_by_id, decls, node_map, graph,
                           already=already, by_full=by_full, ax_id=ax_id,
                           ax_shown=ax_shown, axiom_full=axiom_full,
                           glosses=glosses)
    lines += render_faith_deferred(sections, claims_by_id, decls, node_map, graph,
                                   already=already, by_full=by_full, ax_id=ax_id,
                                   ax_shown=ax_shown, axiom_full=axiom_full,
                                   glosses=glosses)
    lines += render_axiom_inventory(node_map, claims_by_id, glosses, ax_id=ax_id)
    lines += render_consistency(sections, decls, node_map, claims_by_id, graph, None, glosses)
    lines += render_code_annex(sections, claims_by_id, decls, node_map, graph)
    lines += render_appendix(sections, decls, node_map, claims_by_id, graph, None)

    body = "\n".join(lines).rstrip() + "\n"
    OUT_PATH.write_text(body, encoding="utf-8")
    print(f"wrote {OUT_PATH} ({len(body.splitlines())} lines)")


if __name__ == "__main__":
    raise SystemExit(main())