"""Census of declarations whose (comment-stripped) body contains the word `sorry`, every .lean file
under <wt>/TCSlib. Also lists `admit`, `sorryAx`, and `axiom` declarations. Usage: sorrycensus.py <wt>"""
import os, re, sys
wt = sys.argv[1]
def strip(src):
    out, i, d = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i): d += 1; i += 2; continue
        if src.startswith("-/", i) and d: d -= 1; i += 2; continue
        if d == 0: out.append(src[i])
        else: out.append("\n" if src[i] == "\n" else " ")
        i += 1
    return "".join(out)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|example|axiom|opaque)\s+([^\s(:{\[]*)", re.M)
tot = 0
for dp, dn, fn in sorted(os.walk(os.path.join(wt, "TCSlib"))):
    for f in sorted(fn):
        if not f.endswith(".lean"): continue
        p = os.path.join(dp, f); rel = os.path.relpath(p, wt)
        code = strip(open(p, encoding="utf-8").read()).split("\n")
        cur, names, axioms = None, [], []
        for ln, l in enumerate(code, 1):
            d = DECL.match(l)
            if d:
                cur = (d.group(1) or "(anonymous)") + (" [private]" if re.match(r"^(?:@\[[^\]]*\]\s*)*private\b", l) else "")
                if re.match(r"^(?:@\[[^\]]*\]\s*)*axiom\b", l): axioms.append(cur)
            elif re.match(r"^(end|namespace|section)\b", l): cur = None
            body = l.split("--")[0]
            if cur and re.search(r"\b(sorry|admit|sorryAx)\b", body) and (not names or names[-1][0] != cur):
                names.append((cur, ln))
        if names or axioms:
            tot += len(names)
            print(f"{rel}: {len(names)}: " + ", ".join(f"{n}@{ln}" for n, ln in names) + (f" AXIOMS: {axioms}" if axioms else ""))
print("TOTAL", tot)
