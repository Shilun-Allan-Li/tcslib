"""Write the axiom probe: a copy of the unit followed by `#print axioms` for every public
theorem and definition of the unit (names from names_c1.decls). Read-only on the unit."""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from names_c1 import decls  # noqa: E402

unit, out = sys.argv[1], sys.argv[2]
src = open(unit, encoding="utf-8").read()
names = [n for n, p in decls(unit) if not p]
with open(out, "w", encoding="utf-8") as f:
    f.write(src.rstrip("\n") + "\n\n-- Axiom probe (evidence only).\n")
    for n in names:
        f.write(f"#print axioms {n}\n")
print(f"{len(names)} `#print axioms` lines")
