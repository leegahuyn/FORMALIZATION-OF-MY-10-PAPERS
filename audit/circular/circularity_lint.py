#!/usr/bin/env python3
"""Circularity lint for the PrimalitySheafVerification modules.

Flags theorems whose entire proof is "apply a hypothesis whose type is a named
`Prop`-valued definition" (e.g. `theorem t (h : P x) : Q := h x`, `:= h.1`,
`:= by exact (h x).mp`).  Such a theorem proves nothing beyond its hypothesis;
it is harmless when it is a destructor/API lemma for a genuine definition, but
it is circular when the hypothesis is a paper claim, gate or certificate that
is then reported as a "conditional certification" of that same claim.

Usage:
  python3 circularity_lint.py <path/to/PrimalitySheafVerification> \
      [--csv out.csv] [--allow allowlist.txt]

The allow-list holds one `Module:theorem_name` per line (lines starting with
`#` are comments); allow-listed hits are reported separately and do not count
towards the exit status.  Exit status 1 when non-allow-listed hits remain.
"""
import argparse
import csv
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "verification"))
from lean_scan import MODULES, analyse  # noqa: E402

BINDER_NAMES = re.compile(r"[({\[⦃]\s*([^:(){}\[\]⦃⦄]+?)\s*:")


def binders(sig: str) -> set:
    names = set()
    for m in BINDER_NAMES.finditer(sig):
        names |= {x for x in m.group(1).split() if re.match(r"^[\w'₀-₉]+$", x)}
    return names


def proof_kind(body: str, h: str) -> str:
    """FULL: the proof is the hypothesis itself, possibly applied to binders;
    PROJ: a projection / Iff direction of it."""
    rest = body[len(h):].strip() if body.startswith(h) else body
    if re.match(r"^(\.\d|\.\w|\)\.)", rest) or re.search(r"\)\s*\.(1|2|mp|mpr)\b", body) \
            or re.match(r"^\(?\s*[\w'₀-₉]+(\s+[\w'₀-₉]+)*\s*\)?\.(\d|mp|mpr|1|2)", body):
        return "PROJ"
    return "FULL"


def scan(root: Path):
    decls = []
    for mod in MODULES:
        recs, _, _ = analyse(root / f"{mod}.lean")
        decls += recs
    propdefs = {}
    for r in decls:
        if r["kw"] in ("def", "abbrev") and re.search(r":\s*Prop\s*$", r["sig"]):
            propdefs.setdefault(r["name"].split(".")[-1], []).append(r)
    hits = []
    for r in decls:
        if r["kw"] not in ("theorem", "lemma") or not r["body"].startswith(":="):
            continue
        body = re.sub(r"^by\s+(exact\s+)?", "", r["body"][2:].strip())
        m = re.match(r"^\(?\s*([\w'₀-₉]+)\b", body)
        if not m or len(body) >= 120:
            continue
        h = m.group(1)
        hm = re.search(r"\(\s*" + re.escape(h) + r"\s*:\s*([\w.'₀-₉]+)", r["sig"])
        if not hm:
            continue
        ty = hm.group(1).split(".")[-1]
        if ty not in propdefs:
            continue
        d = propdefs[ty][0]
        hits.append({
            "module": r["file"], "line": r["line"], "theorem": r["name"],
            "hyp": h, "hyp_type": ty, "def_module": d["file"], "def_line": d["line"],
            "kind": proof_kind(body.lstrip("("), h), "proof": body,
            "statement": r["sig"], "def_body": d["body"],
        })
    return hits


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("root", type=Path)
    ap.add_argument("--csv", type=Path)
    ap.add_argument("--allow", type=Path)
    a = ap.parse_args()
    hits = scan(a.root)
    allow = set()
    if a.allow and a.allow.exists():
        allow = {ln.strip() for ln in a.allow.read_text().splitlines()
                 if ln.strip() and not ln.startswith("#")}
    flagged = [h for h in hits if f"{h['module']}:{h['theorem']}" not in allow]
    if a.csv:
        with a.csv.open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(hits[0].keys()) if hits else ["module"])
            w.writeheader()
            w.writerows(hits)
    for h in flagged:
        print(f"{h['module']}:{h['line']}: {h['theorem']} := {h['proof']}  [{h['hyp_type']}, {h['kind']}]")
    print(f"total hits: {len(hits)}; allow-listed: {len(hits) - len(flagged)}; flagged: {len(flagged)}")
    sys.exit(1 if flagged else 0)


if __name__ == "__main__":
    main()
