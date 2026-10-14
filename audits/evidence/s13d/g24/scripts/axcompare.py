"""Compare two axiom-print logs by declaration (read-only). Usage: axcompare.py <before> <after>
Reports, for every declaration printed before, whether its axiom set is unchanged after; and
lists the declarations printed only after, with their axioms."""
import re
import sys
P = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")


def read(p):
    d = {}
    for l in open(p, encoding="utf-8"):
        m = P.search(l)
        if m:
            d[m.group(1)] = tuple(sorted(x.strip() for x in (m.group(2) or "").split(",") if x.strip()))
    return d


a, b = read(sys.argv[1]), read(sys.argv[2])
same = [n for n in a if b.get(n) == a[n]]
diff = [n for n in a if n in b and b[n] != a[n]]
gone = [n for n in a if n not in b]
print(f"before {len(a)} prints, after {len(b)}; unchanged {len(same)}, changed {len(diff)}, "
      f"missing after {len(gone)}")
for n in diff:
    print(f"  CHANGED {n}: {list(a[n])} -> {list(b[n])}")
for n in gone:
    print(f"  MISSING {n}")
gained = [n for n in a if n in b and "sorryAx" in b[n] and "sorryAx" not in a[n]]
print(f"declarations that gain sorryAx: {len(gained)}" + (": " + ", ".join(gained) if gained else ""))
print("printed only after:")
for n in b:
    if n not in a:
        print(f"  NEW {n}: {list(b[n])}")
