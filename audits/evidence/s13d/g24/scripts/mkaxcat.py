"""Write an axiom probe for a Catalog chain: the chain followed by `#print axioms` for every public
declaration of the given source files (names from names_c1.decls). Usage:
mkaxcat.py <chain.lean> <out.lean> <source.lean> [<source.lean> ...]"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from names_c1 import decls  # noqa: E402

chain, out, srcs = sys.argv[1], sys.argv[2], sys.argv[3:]
names = []
for s in srcs:
    for n, priv in decls(s):
        if not priv and n not in names:
            names.append(n)
with open(out, "w", encoding="utf-8") as f:
    f.write(open(chain, encoding="utf-8").read().rstrip("\n") + "\n\n-- Axiom probe (evidence only).\n")
    for n in names:
        f.write(f"#print axioms {n}\n")
print(f"{len(names)} `#print axioms` lines")
