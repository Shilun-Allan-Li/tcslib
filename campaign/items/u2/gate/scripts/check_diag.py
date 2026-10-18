"""Check one elaboration's diagnostics and axiom prints against expectations (read-only).

Usage: python3 -I check_diag.py <checked .lean> <lean output> <spec>
  <spec> is `sorried=NAME,NAME;std=NAME,...;sorryAx=NAME,...` (any part may be empty):
  sorried   the declarations whose own `sorry` must be reported, and no other `sorry` warning;
  std       declarations whose axioms must be within propext, Classical.choice, Quot.sound;
  sorryAx   declarations whose axioms must include sorryAx (they depend on a sorried contract).
Any error, or any warning other than an expected `declaration uses 'sorry'`, fails. Every printed
declaration must be classified. Exit 1 on failure.
"""
import re
import sys

STD = {"propext", "Classical.choice", "Quot.sound"}
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|example)\s+(\S+)")


def main():
    src_p, out_p, spec = sys.argv[1:4]
    parts = dict(p.split("=", 1) for p in spec.split(";"))
    want = {k: set(v.split(",")) - {""} for k, v in parts.items()}
    lines = open(src_p, encoding="utf-8").read().split("\n")
    out = open(out_p, encoding="utf-8").read()
    fail = []

    def decl_at(n):
        for i in range(n - 1, -1, -1):
            m = DECL.match(lines[i])
            if m:
                return m.group(1)
        return "?"

    sorry_at, others = set(), []
    for m in re.finditer(r"^\S+\.lean:(\d+):\d+: (warning|error)[^:]*: (.*)$", out, re.M):
        ln, kind, msg = int(m.group(1)), m.group(2), m.group(3)
        if kind == "warning" and msg.startswith("declaration uses 'sorry'"):
            sorry_at.add(decl_at(ln).split(".")[-1])
        else:
            others.append(f"{kind} at line {ln} ({decl_at(ln)}): {msg}")
    exp_sorry = {n.split(".")[-1] for n in want.get("sorried", set())}
    print(f"sorry warnings at: {sorted(sorry_at)}; expected: {sorted(exp_sorry)}")
    if sorry_at != exp_sorry:
        fail.append("sorry warnings differ")
    print(f"other diagnostics: {len(others)}")
    for o in others:
        print("  " + o)
    if others:
        fail.append("other diagnostics")
    ax = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out.replace("\n ", " ")))
    for n in re.findall(r"'([^']+)' does not depend on any axioms", out):
        ax[n] = ""
    for n, a in ax.items():
        s = {x.strip() for x in a.split(",")} - {""}
        cls = "sorryAx" if "sorryAx" in s else ("std" if s <= STD else "OTHER")
        exp = "std" if n in want.get("std", set()) else (
            "sorryAx" if n in want.get("sorryAx", set()) else None)
        flag = "ok" if cls == exp else f"**expected {exp}**"
        print(f"  {n}: {cls} {flag}")
        if cls != exp:
            fail.append(f"axioms of {n}")
    missing = (want.get("std", set()) | want.get("sorryAx", set())) - set(ax)
    if missing:
        fail.append(f"no axiom print for {sorted(missing)}")
    print("CHECK: PASS" if not fail else "CHECK: FAIL — " + "; ".join(fail))
    sys.exit(0 if not fail else 1)


if __name__ == "__main__":
    main()
