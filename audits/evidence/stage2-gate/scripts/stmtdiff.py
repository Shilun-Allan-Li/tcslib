"""Statement correspondence between the drafts and the proposed files (read-only; stdlib only).

Usage: python3 -I stmtdiff.py <draft> <proposed> [<old>=<new> ...]

For every declaration of the draft, find the declaration of the proposed file with the same last
name component (after the renames given as old=new), strip comments and the `:= by sorry` proof,
apply the textual normalizations below to both, collapse whitespace, and report: identical,
changed (with both texts), or missing. Declarations of the proposed file with no draft
counterpart are listed as added.
"""
import re
import sys

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(theorem|lemma|def|structure|abbrev|"
                  r"inductive)\s+([A-Za-z0-9_.']+)", re.M)
STOP = re.compile(r"^(?:end|section|namespace|variable|open|/-!|@\[|theorem|lemma|def|structure|"
                  r"abbrev|inductive|noncomputable)\b", re.M)
NORM = [  # applied to both sides: names qualified in one file and opened in the other
    (r"\bWordRAM\.(wd|Cfg|Steps|step|effect|effects|CodeAt|Straight|AgreeOutside|StepsIn|"
     r"HaltsWithin)\b", r"\1"),
    (r"\bLight\.(Stmt|Program|Exec|Ends|Limits|Expr|Cond|State|frame)\b", r"\1"),
    (r"\bLight\.Compiler\.(Fits|cARG1)\b", r"\1"),
    (r"\blim\.toLimits\.Addr\b", "lim.Addr"),
    (r"\bCompiler\.Fits\b", "Fits"),
]


def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if src.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(src[i])
        i += 1
    return "\n".join(l.split("--")[0].rstrip() for l in "".join(out).splitlines())


def decls(path):
    src = strip(open(path, encoding="utf-8").read())
    res = {}
    for m in DECL.finditer(src):
        start = m.start()
        nxt = STOP.search(src, m.end())
        body = src[start:nxt.start() if nxt else len(src)]
        body = re.sub(r":=\s*by\s+sorry\s*$", "", body.strip())
        for a, b in NORM:
            body = re.sub(a, b, body)
        res[m.group(2).split(".")[-1] if m.group(1) != "structure" else m.group(2)] = \
            " ".join(body.split())
    return res


def main():
    draft, prop = decls(sys.argv[1]), decls(sys.argv[2])
    ren = dict(a.split("=", 1) for a in sys.argv[3:])
    same = changed = missing = 0
    for name, text in draft.items():
        new = ren.get(name, name)
        t2 = prop.get(new) or prop.get(new.split(".")[-1])
        if t2 is None:
            print(f"MISSING  {name}")
            missing += 1
            continue
        for a, b in ren.items():
            text = re.sub(rf"\b{re.escape(a)}\b", b, text)
        if text == t2:
            same += 1
        else:
            changed += 1
            print(f"CHANGED  {name}" + (f" -> {new}" if new != name else ""))
            print(f"   draft:    {text}")
            print(f"   proposed: {t2}")
    used = {ren.get(n, n) for n in draft} | {ren.get(n, n).split('.')[-1] for n in draft}
    added = [n for n in prop if n not in used]
    print(f"identical {same}, changed {changed}, missing {missing}; added in the proposed file: "
          f"{len(added)}: {', '.join(added)}")


if __name__ == "__main__":
    main()
