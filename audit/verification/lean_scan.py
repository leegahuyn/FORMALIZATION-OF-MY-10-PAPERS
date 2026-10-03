#!/usr/bin/env python3
"""Lexical scanner for Lean 4 files: strips comments/strings, splits top-level
declarations, and records per-declaration metadata for auditing."""
import json
import re
import sys
from pathlib import Path

MODULES = ["Spt1", "Spt2", "Spt3", "Spt4", "Spt5", "Spt6", "Spt7", "Mock1",
           "Mock1_Advanced", "Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis", "QYM"]


def strip(src: str):
    """Return (code, comments) where code has comments/strings blanked (newlines kept)."""
    out = []
    comments = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1; j += 2
                elif src.startswith("-/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
            seg = src[i:j]
            comments.append(seg)
            out.append(re.sub(r"[^\n]", " ", seg))
            i = j
        elif src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            comments.append(src[i:j])
            out.append(" " * (j - i))
            i = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j += 1
            seg = src[i:j]
            out.append('"' + re.sub(r"[^\n]", " ", seg[1:-1]) + '"' if len(seg) >= 2 else seg)
            i = j
        elif c == "'" and i + 2 < n and src[i + 2] == "'" and src[i + 1] != "'":
            out.append("' '")
            i += 3
        else:
            out.append(c)
            i += 1
    return "".join(out), comments


DECL_KW = r"(theorem|lemma|def|abbrev|structure|class|instance|axiom|opaque|example|inductive|irreducible_def)"
MODS = r"(?:(?:@\[[^\]]*\]\s*)|(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
DECL_RE = re.compile(r"^" + MODS + r"(?:class\s+inductive|" + DECL_KW + r")\b(.*)$")
CMD_RE = re.compile(r"^(namespace|section|end|open|variable|universe|set_option|attribute|noncomputable section|#\w+|macro|syntax|elab|macro_rules|notation|infix|infixl|infixr|prefix|postfix|local|scoped|initialize|run_cmd|deriving|mutual|export|import|omit|include|suppress_compilation)\b")


def split_decls(code: str):
    lines = code.split("\n")
    starts = []
    for idx, ln in enumerate(lines):
        if ln and not ln[0].isspace():
            m = DECL_RE.match(ln)
            if m:
                kw = re.search(r"\b(class\s+inductive|" + DECL_KW + r")\b", ln).group(1)
                starts.append((idx, kw, "decl"))
            elif CMD_RE.match(ln):
                starts.append((idx, ln.split()[0], "cmd"))
    starts.append((len(lines), None, "eof"))
    decls = []
    for k in range(len(starts) - 1):
        a, kw, typ = starts[k]
        b = starts[k + 1][0]
        decls.append((a, b, kw, typ, "\n".join(lines[a:b])))
    return decls, lines


NAME_RE = re.compile(r"\b(?:theorem|lemma|def|abbrev|structure|class|instance|axiom|opaque|inductive|irreducible_def)\s+([^\s:(\[{]+)")


def analyse(path: Path):
    src = path.read_text()
    code, comments = strip(src)
    decls, lines = split_decls(code)
    recs = []
    for a, b, kw, typ, text in decls:
        if typ != "decl":
            continue
        m = NAME_RE.search(text.split("\n")[0] + " ")
        name = m.group(1) if m else ("<anon " + kw + ">")
        # signature: up to first ':=' at depth 0 or ' where' or '|'
        sig, body = text, ""
        mm = re.search(r":=|\bwhere\b", text)
        if mm:
            sig, body = text[: mm.start()], text[mm.start():]
        rec = {
            "file": path.stem, "line": a + 1, "end": b, "kw": kw, "name": name,
            "sig": re.sub(r"\s+", " ", sig).strip(),
            "body": re.sub(r"\s+", " ", body).strip(),
            "nlines": b - a,
        }
        recs.append(rec)
    stats = {
        "lines": src.count("\n") + 1,
        "comment_chars": sum(len(c) for c in comments),
        "code_chars": len(re.sub(r"\s", "", code)),
        "total_chars": len(src),
    }
    tok = lambda w: len(re.findall(r"(?<![\w.'])" + w + r"(?![\w'])", code))
    for w in ["sorry", "admit", "native_decide", "decide", "axiom", "opaque", "unsafe",
              "implemented_by", "extern", "Classical.choice", "Classical.choose", "trivial",
              "rfl", "simp", "omega", "linarith", "nlinarith", "positivity", "norm_num", "aesop",
              "exact?", "apply?", "polyrith", "ring", "field_simp", "nonlinarith", "maxHeartbeats",
              "set_option", "macro", "elab", "syntax", "run_cmd", "#eval", "#print", "#check",
              "debug.skipKernelTC", "Lean.ofReduceBool", "False.elim", "absurd", "Subsingleton.elim",
              "Inhabited", "Nonempty"]:
        stats["tok_" + w] = tok(re.escape(w))
    return recs, stats, code


def main():
    root = Path(sys.argv[1])
    out = Path(sys.argv[2])
    allrecs, allstats = [], {}
    for mname in MODULES:
        recs, stats, code = analyse(root / f"{mname}.lean")
        allrecs += recs
        allstats[mname] = stats
        (out / f"{mname}.code.lean").write_text(code)
    (out / "decls.json").write_text(json.dumps(allrecs, ensure_ascii=False))
    (out / "stats.json").write_text(json.dumps(allstats, indent=1))
    print(len(allrecs), "declarations")


if __name__ == "__main__":
    main()
