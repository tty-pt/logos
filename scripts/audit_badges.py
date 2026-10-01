#!/usr/bin/env python3
"""audit_badges.py — generate formal/badge_census.json for all badge slots.

Enumerates every badge slot across the generated surfaces (classical attributes,
seven pillars, characteristic sections, and glance steps), computes the strongest
admissible route and rendered badge, records rejected routes and reasons, and
emits formal/badge_census.json.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import scripts.build_deduction as bd

CENSUS_PATH = ROOT / "formal" / "badge_census.json"


def generate_badge_census() -> dict:
    decls = bd.parse_lean_sources()
    secs = bd.parse_gapmap()
    graph = bd.load_depgraph()
    nm = graph["node_map"]

    bd._AUDIT = bd.load_audit()
    bd._REGISTRY = bd.load_axiom_registry(decls, nm)
    bd._CTX.clear()
    bd._CTX.update({
        "decls": decls, "node_map": nm, "graph": graph, "compiled": {},
        "def_registry": {}, "by_id": {}, "claims_by_id": {},
    })

    for s in secs:
        for c in s.get("claims", []):
            ref = c.get("lean_ref") or ""
            if not ref:
                continue
            r = bd.resolve(ref, decls, nm, c.get("level_key", ""))
            if r is None and "." not in ref:
                m = [f for f in decls if f.rsplit(".", 1)[-1] == ref]
                if len(m) == 1:
                    r = m[0]
            c["_full"] = r
            if r:
                c["_name"] = r.rsplit(".", 1)[-1]

    bd.build_boundary_by_decl(secs, decls)
    bd._COMPILED_BY_FULL.clear()

    slots = []
    totals = {"slots": 0, "PROVEN": 0, "AXIOMATIC": 0, "CONTRADICTION": 0,
              "COUNTERMODEL": 0, "AXIOM": 0, "OPEN": 0}

    # 1. Classical Attributes (39 slots)
    for row in bd.CLASSICAL_ATTRIBUTES:
        attr = row.get("attribute", "").strip()
        cid = attr.split("—")[0].split("(")[0].split("/")[0].replace("*", "").strip()
        cls, tier = bd._classical_row_route(row)
        claim_full = bd._classical_claim_of(row)
        reasons = bd._RECORDED_REASONS.get(claim_full, {})

        routes_rejected = {
            "countermodel_namespace": sum(1 for w in reasons.values() if "countermodel" in w),
            "incomparable": sum(1 for w in reasons.values() if "does not assert" in w),
        }
        assert len(reasons) >= sum(routes_rejected.values()), (
            f"Census slot {cid} rejection categories must not exceed considered: "
            f"{len(reasons)} < {routes_rejected}"
        )

        verdict = cls if cls else (row.get("expected") or "OPEN")
        if verdict not in totals:
            totals[verdict] = 0
        totals[verdict] += 1
        totals["slots"] += 1

        winner_name = tier[0].full_name if tier else (row["checks"][0].get("full") if row.get("checks") else "")
        subst = list(bd._branch_substantive(tier[0])) if tier else []
        rendered_badge = bd.status_cell_of_route(tier, cls) if (cls and tier) else bd._classical_row_status(row, decls, nm)

        slot_entry = {
            "surface": "classical_attributes",
            "id": cid,
            "claims": [claim_full] if claim_full else [],
            "routes_considered": len(reasons),
            "routes_rejected": routes_rejected,
            "winner": winner_name,
            "verdict": verdict,
            "substantive": subst,
            "stipulated": bool(bd._stip_marker([winner_name])),
            "rendered_badge": rendered_badge,
        }
        slots.append(slot_entry)

    # 2. Seven Pillars of Formal Defense (7 slots)
    for p in bd.PILLAR_ROWS:
        num = p["num"]
        title = p["title"]
        proofs = [bd.compiled_proof(t) for t in p["targets"] if bd.compiled_proof(t)]
        winner_name = proofs[0].full_name if proofs else ""
        subst = list(bd._branch_substantive(proofs[0])) if proofs else []
        fp_cell = f"{bd._footprint_cell(proofs)}<br>**({bd._derived_price_cell(proofs)})**"
        verdict = "PROVEN" if not subst else "AXIOMATIC"
        totals[verdict] += 1
        totals["slots"] += 1

        slot_entry = {
            "surface": "seven_pillars",
            "id": f"Pillar_{num}_{title}",
            "claims": p["targets"],
            "routes_considered": len(proofs),
            "routes_rejected": {},
            "winner": winner_name,
            "verdict": verdict,
            "substantive": subst,
            "stipulated": False,
            "rendered_badge": fp_cell,
        }
        slots.append(slot_entry)

    # 3. Eighteen Characteristics (18 slots)
    for i, (title, target, _note) in enumerate(bd.CHARACTERISTIC_SECTIONS, start=1):
        proof = bd._resolve_block_proof(target, f"census characteristic '{title}'")
        cat, badge = bd.classify_proof_edge(proof)
        cls = "AXIOMATIC" if badge.startswith("AXIOMATIC") else ("COUNTERMODEL" if badge.startswith("COUNTERMODEL") else "PROVEN")
        subst = list(bd._branch_substantive(proof))
        totals[cls] += 1
        totals["slots"] += 1

        slot_entry = {
            "surface": "characteristic_sections",
            "id": f"Char_{i}_{title}",
            "claims": [proof.full_name],
            "routes_considered": 1,
            "routes_rejected": {},
            "winner": proof.full_name,
            "verdict": cls,
            "substantive": subst,
            "stipulated": bool(bd._stip_marker([proof.full_name])),
            "rendered_badge": bd._derived_status_cell(badge),
        }
        slots.append(slot_entry)

    census_data = {
        "slots": slots,
        "totals": totals,
    }
    return census_data


def main() -> int:
    data = generate_badge_census()
    body = json.dumps(data, indent=2) + "\n"
    CENSUS_PATH.write_text(body, encoding="utf-8")
    print(f"wrote {CENSUS_PATH} ({len(data['slots'])} slots, totals: {data['totals']})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
