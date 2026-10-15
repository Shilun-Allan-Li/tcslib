"""Write the axiom file of the landed Diagonal.lean: its text plus `#print axioms` for every
public declaration (read-only on its inputs; standard library only).

Usage: python3 -I axfile.py <landed Diagonal.lean> <out .lean>
"""
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
from decls import parse  # noqa: E402

src = open(sys.argv[1], encoding="utf-8").read()
names = [d["name"] for d in parse(src) if not d["private"]]
open(sys.argv[2], "w", encoding="utf-8").write(
    src.rstrip("\n") + f"\n\n-- ════ axioms of every public declaration ({len(names)}) ════\n"
    + "".join(f"#print axioms {n}\n" for n in names))
print(f"axiom prints: {len(names)}")
