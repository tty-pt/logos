#!/usr/bin/env python3
"""goal_audit_fingerprint.py — is `formal/goal_audit.json` current?

`audit_goals.py` costs minutes because it elaborates the whole `Logos` environment
and walks every declaration. Putting that on the regeneration path unconditionally
means every README/ledger rebuild pays for it, which is not acceptable — but
*removing* the freshness check is worse, because a stale goal shape silently
reaches a badge, and that is the `_GLANCE_RANK`/`ASIETY` laundering failure in a
different costume.

So: compute a fingerprint of exactly the two inputs that determine the artifact's
contents — the Lean reader in `audit_goals.py`, and the compiled environment it
reads — and let both the producer and the consumer derive the same value.

The fingerprint is a *staleness* device, not a cache key. It is deliberately coarse:
`mtime`+`size` of every `.olean` in the build tree, plus the reader's own source.
A touch of an unrelated file can make it mismatch, which costs a rerun and nothing
else. A false *match* would be the dangerous direction, and it requires both the
reader and every compiled environment file to be byte- and mtime-identical, which
is the same condition under which re-running would produce the same artifact.

The fingerprint lives in a sidecar (`formal/goal_audit.fingerprint.json`) rather
than inside `goal_audit.json`, so the artifact stays a flat `name -> record` map
that `test_goal_audit.py` and `build_deduction.py` can iterate without filtering
sentinel keys.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FORMAL = ROOT / "formal"
ARTIFACT = FORMAL / "goal_audit.json"
SIDECAR = FORMAL / "goal_audit.fingerprint.json"
READER = ROOT / "scripts" / "audit_goals.py"
OLEANS = FORMAL / ".lake" / "build" / "lib" / "lean"


def _reader_source() -> bytes:
    """The Lean half of the reader: the prologue is the program that runs."""
    text = READER.read_text(encoding="utf-8")
    start = text.index('LEAN_PROLOGUE = r"""')
    return text[start:].encode("utf-8")


def environment_inputs() -> list[str]:
    """Every compiled environment file, keyed by path and mtime/size.

    Missing `.olean` files contribute a `MISSING` marker rather than being skipped,
    so that deleting the build tree invalidates the fingerprint instead of
    silently reducing the input set.
    """
    out: list[str] = []
    if not OLEANS.exists():
        return ["<no build tree>"]
    for p in sorted(OLEANS.rglob("*.olean")):
        try:
            st = p.stat()
            rel = p.relative_to(FORMAL)
            out.append(f"{rel}:{st.st_mtime_ns}:{st.st_size}")
        except OSError:
            out.append(f"{p}:ERR")
    return out


def fingerprint() -> str:
    h = hashlib.sha256()
    h.update(_reader_source())
    h.update(b"\0")
    for line in environment_inputs():
        h.update(line.encode("utf-8"))
        h.update(b"\n")
    return h.hexdigest()


def write_sidecar(count: int) -> str:
    import datetime
    fp = fingerprint()
    SIDECAR.write_text(json.dumps({
        "fingerprint": fp,
        "declarations": count,
        "generated": datetime.datetime.now().isoformat(timespec="seconds"),
    }, indent=1) + "\n", encoding="utf-8")
    return fp


def read_sidecar() -> dict | None:
    if not SIDECAR.exists():
        return None
    try:
        return json.loads(SIDECAR.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None


def check() -> tuple[bool, str]:
    """`(ok, explanation)`. `ok` means the artifact may be trusted as current."""
    if not ARTIFACT.exists():
        return False, f"{ARTIFACT.relative_to(ROOT)} does not exist"
    side = read_sidecar()
    if side is None:
        return False, (f"{SIDECAR.relative_to(ROOT)} missing or unreadable — the "
                       f"artifact carries no provenance")
    want = fingerprint()
    have = side.get("fingerprint")
    if have != want:
        return False, (f"stale: recorded {str(have)[:12]}, current {want[:12]} — "
                       f"the Lean reader or the compiled environment changed")
    return True, f"current ({side.get('declarations')} declarations, {want[:12]})"


if __name__ == "__main__":
    ok, why = check()
    print(("OK: " if ok else "STALE: ") + why)
    raise SystemExit(0 if ok else 1)
