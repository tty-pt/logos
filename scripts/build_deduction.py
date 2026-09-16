#!/usr/bin/env python3
"""build_deduction.py — Γ / Logos deduction map generator.

Merges three sources of truth:

  1. formal/depgraph.json   — LeanDepViz kernel graph: every declaration
                              (theorem/def/axiom) with its transitive axioms
                              and its direct dependency edges.
  2. formal/GAPMAP.md       — the curated theorem ledger: claim IDs, prose
                              references, statuses, axiom footprints and tags.
  3. formal/Logos/*.lean    — the source: exact declaration line numbers and
                              formal statements (used for hyperlinks).

Output: DEDUCTION.md at the repository root: the deduction chain, level by
level, each claim with its formal notation, its status, its axiom footprint,
its dependencies and dependents, plus an axiom inventory and a consistency
report (GAPMAP vs. kernel graph).

Regenerate after any GAPMAP / Lean source change:

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
GLOSSES_PATH = ROOT / "scripts" / "glosses.json"

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

    info keys: kind, file (basename), line, statement, doc, module, name.
    """
    decls = {}

    for path in sorted(LEAN_DIR.glob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        # namespace tracking (files use a single `namespace Logos.X` block)
        namespaces: list[str] = []
        cur_doc = ""  # most recent /-- ... -/ doc block

        for ln, raw in enumerate(lines, start=1):
            text = strip_block_comments(raw)
            stripped = text.strip()

            m = re.match(r"^namespace\s+([\w.]+)\s*$", stripped)
            if m:
                namespaces.append(m.group(1))
                continue
            m = re.match(r"^end(?:\s+([\w.]+))?\s*$", stripped)
            if m:
                if namespaces:
                    namespaces.pop()
                continue

            # doc block? /-- <doc> -/ may span several lines
            if stripped.startswith("/--"):
                end = raw.find("-/", 6)
                if end >= 0:
                    cur_doc = raw[6:end].strip()
                else:  # multi-line doc: capture until -/ appears in closing line
                    collected = [raw[6:].strip()]
                    for ln2 in range(ln, len(lines)):
                        nxt = lines[ln2]
                        end2 = nxt.find("-/")
                        if end2 >= 0:
                            collected.append(nxt[:end2].strip())
                            break
                        collected.append(nxt.strip())
                    cur_doc = " ".join(c for c in collected if c)
                    # multi-line doc handled inline below (lines consumed)
                m2 = re.match(DECL_RE, stripped[6:] if False else "")
            elif stripped.startswith("--"):
                cur_doc = stripped[2:].strip()
                continue
            else:
                m2 = re.match(DECL_RE, stripped)
                if not m2:
                    continue
                kind, rest = m2.group(1), m2.group(2).strip()
                # name = first identifier token before ':'/'('/whitespace
                name_m = re.match(r"([\w.]+)", rest)
                if not name_m:
                    continue
                name = name_m.group(1)
                ns = ".".join(namespaces)
                full = f"{ns}.{name}" if ns else name
                stmt, end_line = _capture_statement(lines, ln, kind)
                # record with consumed end_line for doc association
                decls[full] = {
                    "kind": kind,
                    "name": name,
                    "module": ns,
                    "file": path.name,
                    "line": ln,
                    "end_line": end_line,
                    "statement": stmt,
                    "doc": _doc_for(cur_doc),
                }
                cur_doc = ""
        pass

    return decls


def _doc_for(doc: str) -> str:
    """First paragraph of a doc comment, trimmed to ~260 chars."""
    if not doc:
        return ""
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
    "PROVEN": "**PROVEN**",
    "PROVEN↑": "**PROVEN ↑**",
    "AXIOM": "**AXIOM**",
    "BLOCKED": "**BLOCKED**",
    "DEFERRED": "**DEFERRED**",
}

AXIOM_TAGS = {
    "Cogito": ("TRANS", "forced foundation — SUBJECT IS FORCED (M0)"),
    "Subject": ("VOCAB", "pure-sort postulate"),
    "Means": ("VOCAB", "intentional relation"),
    "Ground": ("VOCAB", "truthmaker relation"),
    "ExistsAt": ("VOCAB", "existence-in-world"),
    "AxGlobalGround": ("SEM", "T7 quantifier swap  ∀w∃r → ∃r∀w"),
    "AxTwoSubjects": ("META", "plurality bridge (right-and-wrong needs two persons)"),
    "AxPersonStability": ("SEM", "world-persistence of persons (T14)"),
    "GroundProp": ("VOCAB", "grounding between entity and proposition"),
    "GroundPrincipleProp": ("SEM", "reflection of the §24a principle at Prop"),
    "AxPersonalGround": ("META", "the 'personal' price of T8 (D9)"),
}


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
    ap("- **Ledger curado:** [`formal/GAPMAP.md`](formal/GAPMAP.md) (status, refs de prosa, tags de axioma)")
    ap("- **Grafo de dependências:** `formal/depgraph.json` (LeanDepViz, kernel)")
    ap("- **Prosa:** [`base.txt`](base.txt) (argumento §0–§29) · [`poem.txt`](poem.txt) (P1–P10) · [`theorems/`](theorems/)")
    ap("")
    ap("Regeneração: `python3 scripts/build_deduction.py`")
    ap("")
    ap("---")
    ap("")
    ap("## Legenda")
    ap("")
    ap("| Token | Significado |")
    ap("|---|---|")
    ap("| **PROVEN** | teorema verificado pelo kernel, footprint vazio (até `CL`) |")
    ap("| **PROVEN ↑** | teorema verificado sob axiomas assinalados |")
    ap("| **AXIOM** | declaração (`axiom`) — não derivada |")
    ap("| **BLOCKED** | em falta um lema nomeado (ver **Em aberto**) |")
    ap("| **DEFERRED** | fora do âmbito deste marco |")
    ap("| `CL` | meta-lógica clássica `{propext, Classical.choice, Quot.sound}` (D1) |")
    ap("")
    ap("Etiquetas de axioma (justificação / preço):")
    ap("")
    ap("| Tag | Significado |")
    ap("|---|---|")
    ap("| `TRANS` | axiom performativo/transcendental — a negação refuta-se a si mesma |")
    ap("| `SEM` | escolha semântica, com modelo de consistência registado |")
    ap("| `META` | ponte metafísica, com o preço tornado explícito |")
    ap("| `VOCAB` | vocabulário primitivo (postulado de sort pura / relação) |")
    ap("")
    ap("Notação formal: cada passo mostra o *enunciado* em símbolos lógicos "
       "(traduzido do Lean), uma frase em inglês com o significado, o "
       "ficheiro/hiperligação para a linha Lean exata, e a pegada de axiomas "
       "medida pelo kernel (`depgraph.json`) ao lado da pegada semântica "
       "curada no GAPMAP.")
    ap("")
    ap("---")
    ap("")
    ap("## Leitura da notação")
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
    ap("| `A s p` · `Means s p` | `A s p` (`:= Means s p`) | o acto de um sujeito s sobre um conteúdo p |")
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
    ap("---")
    ap("")
    ap("## Visão global do argumento")
    ap("")
    ap("```text")
    ap("§0  premissa arbitrária ≠ condição cuja negação destrói o ato de a negar")
    ap("      │")
    ap("§1  A(s,p)  (ato presente, DADO performativo — FORCED foundation `Cogito`)")
    ap("      │  T1 sujeito · T2 conteúdo · §4–§5 absolutos N_T/N_F refutam-se")
    ap("      │  T3 verdade-e-erro §6 · §7–§21 verdade/vontade/correção/consequência")
    ap("      ├──→ §22–§23 necessidade (excluded middle / não-contradição)")
    ap("      ├──→ §24a truthmaker atómico · T7 realidade necessária (AxGlobalGround)")
    ap("      ├──→ §24b pessoa · T8 fundamento pessoal (AxPersonalGround, META)")
    ap("      ├──→ §13–§15 escolha · T11 campo de escolha · T9 alternativas")
    ap("      └──→ P5/P7 pluralidade (AxTwoSubjects, META) · P7/P8 amor (T13·T14)")
    ap("                AxPersonStability (SEM) — 'de alguma forma'")
    ap("```")
    ap("")
    ap("Camadas de conclusão (base.txt §0): performativamente inegável → "
       "logicamente inegável → transcendentalmente necessário → "
       "metafisicamente necessário **se a ponte for demonstrada**.")
    ap("")
    ap("---")
    return L


def render_levels(sections, claims_by_id, decls, node_map, graph):
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
        # at-a-glance table
        ap("| ID | Prosa | Enunciado (Lógica) | Status | Axiomas (kernel) |")
        ap("|---|---|---|---|---|")
        for c in claims:
            name = c.get("_full") or "—"
            stmt = "—"
            if name and name in decls:
                stmt = short_stmt(humanise(decls[name]["statement"]))
            kern = "—"
            if name and name in node_map:
                ks = node_map[name].get("customAxioms", [])
                kern = ", ".join(k.rsplit(".", 1)[-1] for k in ks) if ks else "{}"
            ap(f"| {c['id']} | {c['prose']} | `{stmt[:90]}` | {STATUS_BADGE.get(c['status'], c['status'])} | {kern} |")
        ap("")
        ap("<details>")
        ap("<summary>Passos em detalhe →</summary>")
        ap("")
        for c in claims:
            block = render_claim_detail(c, claims_by_id, decls, node_map, graph)
            ap("\n".join(block))
        ap("</details>")
        ap("")
        ap("---")
        ap("")
    return L


def render_claim_detail(c, claims_by_id, decls, node_map, graph):
    """One compact block per claim: formal notation, source link, axioms, deps."""
    L = []
    ap = L.append
    full = c.get("_full")
    status = STATUS_BADGE.get(c["status"], c["status"])
    t_refs = ", ".join(f"[{t}](theorems/{t}.txt)" for t in find_t_refs(c["prose"]))
    prose_link = render_prose_link(c["prose"])

    ap(f"### {c['id']} · {status}")
    gloss = c.get("_gloss")
    if full and full in decls:
        d = decls[full]
        ap(f"`{humanise(trim_stmt(d['statement']))}`")
        if gloss:
            ap(f"*Significado (EN):* {gloss}")
        ap("")
        ap(f"- **Formal (Lean):** {le_line(d['file'], d['line'])} (`{full}`)")
        if c.get("prose"):
            ap(f"- **Prosa:** {prose_link}" + (f" · {t_refs}" if t_refs else ""))
        kern = node_map.get(full, {}).get("customAxioms", [])
        kern_s = ", ".join(k.rsplit(".", 1)[-1] for k in kern) if kern else "{}"
        g = c.get("footprint") or "—"
        ap(f"- **Axiomas — kernel:** `{kern_s}` · **GAPMAP:** `{g}`")
        if d.get("doc"):
            ap(f"- {first_sentence(d['doc'])}")
        deps = graph["in"].get(full, set())       # declarations this uses
        if deps:
            ap("- **Depende de:** " + dep_list(deps, claims_by_id, decls))
        rds = graph["out"].get(full, set())       # declarations that use this
        ap("- **Usado por:** " + dep_list(rds, claims_by_id, decls))
    else:
        ap(f"- **Prosa:** {prose_link}".rstrip("·"))
        ap(f"- **Estado:** {status}")
        if gloss:
            ap(f"*Significado (EN):* {gloss}")
        if c.get("footprint"):
            ap(f"- **Pegada GAPMAP:** `{c['footprint']}`")
        if c.get("note"):
            ap(f"- **Nota:** {first_sentence(c['note'])}")
    ap("")
    return L


def dep_list(fullnames, claims_by_id, decls):
    """Name the dependencies, preferring claim IDs, then axioms, then raw."""
    if not fullnames:
        return "—"
    pieces = []
    for f in sorted(fullnames):
        if f not in decls and f not in AXIOM_TAGS and f.rsplit(".", 1)[-1] not in AXIOM_TAGS:
            continue  # kernel-generated (recOn, injEq, ...)
        cl = claims_by_id.get(f)
        if cl:
            cln = cl.get("_name") or cl.get("lean_ref") or f.rsplit(".", 1)[-1]
            pieces.append(f"**{cl['id']}** `{cln}`")
            continue
        base = f.rsplit(".", 1)[-1]
        if base in AXIOM_TAGS and not f.startswith(("Logos.", "axion")):
            pass
        if not f.startswith("Logos.") and base:
            f = f"Logos.{f}" if "." not in f else f
        if base in AXIOM_TAGS:
            tag = AXIOM_TAGS[base][0]
            pieces.append(f"axiom `{base}` ({tag})")
        else:
            pieces.append(f"`{f.replace('Logos.', '') if f.startswith('Logos.') else f}`")
    return ", ".join(pieces) if pieces else "—"


def render_axiom_inventory(node_map, claims_by_id, glosses):
    L = []
    ap = L.append
    ap("## Inventário de axiomas (11 declarações)")
    ap("")
    ap("| Axioma | Tag | Justificação / preço | Significado (EN) | Depende dele (claims) |")
    ap("|---|---|---|---|---|")
    axioms = sorted(node_map.values(), key=lambda n: n["fullName"])
    for n in axioms:
        if n["kind"] != "axiom":
            continue
        base = n["fullName"].rsplit(".", 1)[-1]
        tag, why = AXIOM_TAGS.get(base, ("?", ""))
        gl = glosses.get(n["fullName"], "")
        deps = [c["id"] for f, c in claims_by_id.items()
                if n["fullName"] in node_map.get(f, {}).get("customAxioms", [])]
        deps_txt = ", ".join(sorted(set(deps))) if deps else "—"
        ap(f"| `{base}` | `{tag}` | {why} | {gl or '—'} | {deps_txt} |")
    ap("")
    ap("Detalhe do kernel:")
    ap("")
    for n in sorted(node_map.values(), key=lambda n: n["fullName"]):
        if n["kind"] == "axiom":
            ap(f"- `{n['fullName']}`")
    ap("")
    ap("---")
    return L


def render_faith_deferred(sections, claims_by_id, decls, node_map, graph):
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
        ap("<details>")
        ap("<summary>Passos em detalhe →</summary>")
        ap("")
        for c in claims:
            block = render_claim_detail(c, claims_by_id, decls, node_map, graph)
            ap("\n".join(block))
        ap("</details>")
        ap("")
        ap("---")
    return L


def render_consistency(sections, decls, node_map, claims_by_id, graph, resolved_info, glosses):
    L = []
    ap = L.append
    ap("## Relatório de consistência (GAPMAP ↔ kernel)")
    ap("")
    all_claims = [c for s in sections for c in s["claims"]]
    ap(f"- Claims do GAPMAP com teorema localizado no kernel: "
       f"**{len([c for c in all_claims if c.get('_full')])}** / {len(all_claims)}")
    glossed = [c for c in all_claims if c.get("_gloss")]
    ap(f"- Steps com **significado em inglês**: **{len(glossed)}** / {len(all_claims)}"
       + ("" if len(glossed) == len(all_claims)
          else f" · **sem gloss:** {', '.join(c['id'] for c in all_claims if not c.get('_gloss'))}"))
    unresolved = [c for c in all_claims if c.get("lean_ref") and not c.get("_full")]
    if unresolved:
        ap("- **Claims sem teorema localizado:**")
        for c in unresolved:
            ap(f"  - `{c['id']}` ref `{c['lean_ref']}` — {c['prose']} (sem ref Lean ou def/fórmula s/ nível kernel)")
    kern_theorems = {f for f, n in decls.items() if n["kind"] in ("theorem", "example")}
    covered = {c.get("_full") for c in all_claims if c.get("_full")}
    missing = sorted(f for f in kern_theorems - covered if f in node_map)
    if missing:
        ap(f"- Teoremas no kernel **sem claim** no GAPMAP ({len(missing)}): "
           + ", ".join(f.replace("Logos.", "") for f in missing))
    else:
        ap("- Todos os teoremas do kernel têm claim (ou ref mapeada).")
    kern_axioms = {n["fullName"] for n in node_map.values() if n["kind"] == "axiom"}
    known = {"Logos." + m + "." + a for m, a in [(x, a) for x, a in
             [("Agency", "Cogito"), ("Agency", "Subject"), ("Agency", "Means"),
              ("Truthmaker", "Ground"), ("Truthmaker", "ExistsAt"),
              ("Modal", "AxGlobalGround"), ("Value", "AxTwoSubjects"),
              ("Love", "AxPersonStability"), ("GroundPerson", "GroundProp"),
              ("GroundPerson", "GroundPrincipleProp"), ("GroundPerson", "AxPersonalGround")]]}
    extra = kern_axioms - known
    ap(f"- Axiomas declarados no kernel: **{len(kern_axioms)}**" +
       (f" · **fora do inventário esperado:** {', '.join(sorted(extra))}" if extra else ""))
    # kernel vs GAPMAP footprint divergences (informational; CL is kernel-blind)
    ax_vocab = ("Cogito", "Subject", "Means", "Ground", "ExistsAt", "AxGlobalGround",
                "AxTwoSubjects", "AxPersonStability", "GroundProp", "GroundPrincipleProp",
                "AxPersonalGround")
    divs = []
    for c in all_claims:
        full = c.get("_full")
        fp = c.get("footprint") or ""
        fps = fp.strip()
        if not full or full not in node_map or fps in ("—", ""):
            continue
        if fps.startswith("as ") or " as " in fps or fps.startswith("via "):
            continue  # footprint inherited from another claim; not comparable
        kern = {k.rsplit(".", 1)[-1] for k in node_map[full].get("customAxioms", [])}
        gap = {a for a in ax_vocab if re.search(r"\b" + re.escape(a) + r"\b", fp)}
        if kern != gap:
            ks = "{" + ", ".join(sorted(kern)) + "}"
            gs = "{" + ", ".join(sorted(gap)) + "}"
            divs.append((c["id"], ks, gs))
    if divs:
        ap(f"- **Divergências kernel × GAPMAP** (pegada medida vs. curada, {len(divs)} — a verificar na próxima sincronização):")
        for cid, ks, gs in divs:
            ap(f"  - `{cid}` kernel `{ks}` vs GAPMAP `{gs}`")
    return L


def render_appendix(sections, decls, node_map, claims_by_id, graph, level_map):
    L = []
    ap = L.append
    ap("## Índice de declarações do kernel")
    ap("")
    ap("Todos os teoremas/defs user-authored, por módulo, com linha e axiomas de kernel.")
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
            ax = ", ".join(k.rsplit(".", 1)[-1] for k in node_map.get(full, {}).get("customAxioms", [])) if node_map.get(full) else "—"
            cl = claims_by_id.get(full)
            cid = f"→ {cl['id']}" if cl else ""
            ap(f"| `{d['name']}` | {d['kind']} | [L{d['line']}](formal/Logos/{d['file']}#L{d['line']}) | `{humanise(trim_stmt(d['statement']))[:80]}` | {ax} {cid} |")
        ap("")
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
    if not DEPGRAPH_PATH.exists():
        print(f"ERROR: {DEPGRAPH_PATH} missing. Run:\n"
              "  cd formal && lake exe depviz --roots Logos --json-out depgraph.json --dot-out depgraph.dot",
              file=sys.stderr)
        return 1

    print("parsing Lean sources…")
    decls = parse_lean_sources()
    print(f"  {len(decls)} declarations in {len(set(d['file'] for d in decls.values()))} files")

    print("parsing GAPMAP…")
    sections = parse_gapmap()
    all_claims = [c for s in sections for c in s["claims"]]
    print(f"  {len(all_claims)} claim rows across {len(sections)} sections")

    print("loading depgraph…")
    graph = load_depgraph()
    node_map = graph["node_map"]
    print(f"  {len(node_map)} kernel nodes, {sum(len(v) for v in graph['out'].values())} edges")

    print("loading glosses (EN)…")
    glosses = {}
    if GLOSSES_PATH.exists():
        glosses = json.loads(GLOSSES_PATH.read_text(encoding="utf-8"))
    print(f"  {len(glosses)} Entradas de significado carregadas")

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

    print("rendering DEDUCTION.md…")
    lines = []
    lines += render_index(sections, None, claims_by_id, decls, node_map, graph)
    lines += render_levels(sections, claims_by_id, decls, node_map, graph)
    lines += render_faith_deferred(sections, claims_by_id, decls, node_map, graph)
    lines += render_axiom_inventory(node_map, claims_by_id, glosses)
    lines += render_consistency(sections, decls, node_map, claims_by_id, graph, None, glosses)
    lines += render_appendix(sections, decls, node_map, claims_by_id, graph, None)

    body = "\n".join(lines).rstrip() + "\n"
    OUT_PATH.write_text(body, encoding="utf-8")
    print(f"wrote {OUT_PATH} ({len(body.splitlines())} lines)")


if __name__ == "__main__":
    raise SystemExit(main())