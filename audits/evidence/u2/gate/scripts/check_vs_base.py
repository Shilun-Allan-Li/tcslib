"""Compare an importer's cut check with its baseline (read-only; standard library only).

Usage: python3 -I check_vs_base.py <base .lean> <base out> <cut .lean> <cut out> <extra sorried>
The axiom prints must be identical; the `declaration uses 'sorry'` warnings of the cut must be
the baseline's plus exactly the listed extra declarations (comma-separated, those of the landed
bodies in the chain); no error or other warning in either. Exit 1 otherwise.
"""
import re
import sys

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure)\s+(\S+)")


def read(src_p, out_p):
    lines = open(src_p, encoding="utf-8").read().split("\n")
    out = open(out_p, encoding="utf-8").read()

    def decl_at(n):
        for i in range(n - 1, -1, -1):
            m = DECL.match(lines[i])
            if m:
                return m.group(1).split(".")[-1]
        return "?"
    sorry, other = [], []
    for m in re.finditer(r"^\S+\.lean:(\d+):\d+: (warning|error)[^:]*: (.*)$", out, re.M):
        if m.group(2) == "warning" and m.group(3).startswith("declaration uses 'sorry'"):
            sorry.append(decl_at(int(m.group(1))))
        else:
            other.append(m.group(0))
    ax = re.findall(r"^'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",
                    out.replace("\n ", " "), re.M)
    return sorted(sorry), other, ax


bs, bo, ba = read(sys.argv[1], sys.argv[2])
cs, co, ca = read(sys.argv[3], sys.argv[4])
extra = sorted(x for x in sys.argv[5].split(",") if x)
ok = (cs == sorted(bs + extra)) and not bo and not co and ba == ca
print(f"baseline: {len(bs)} sorry warnings {bs}, {len(ba)} axiom prints, other {len(bo)}")
print(f"cut:      {len(cs)} sorry warnings {cs}, {len(ca)} axiom prints, other {len(co)}")
print(f"expected extra sorry warnings: {extra}; axiom prints identical: {ba == ca}")
print("CHECK: PASS" if ok else "CHECK: FAIL")
sys.exit(0 if ok else 1)
