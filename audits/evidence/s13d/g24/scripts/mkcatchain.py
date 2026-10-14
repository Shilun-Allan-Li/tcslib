"""Write a Catalog chain: a Build/Catalog.lean with the import of the core contract module added,
followed by the body of a Build/Contract/Catalog.lean (everything after its options). With the
landed pair it checks the restructured Catalog and Contract/Catalog together; with the base pair
it is the baseline for the axiom comparison. Usage: mkcatchain.py <Catalog> <Contract/Catalog> <out>"""
import sys
cat, ccat, out = sys.argv[1:4]
c = open(cat, encoding="utf-8").read()
imp = "import TCSlib.Complexity.TuringMachine.Encoding\n"
assert c.count(imp) == 1
c = c.replace(imp, imp + "import TCSlib.Complexity.TuringMachine.Build.Contract.Basic\n")
d = open(ccat, encoding="utf-8").read()
marker = "set_option autoImplicit false\n"
assert d.count(marker) == 1
open(out, "w", encoding="utf-8").write(c.rstrip("\n") + "\n\n" + d.split(marker, 1)[1])
print(f"chain: {len((c + d).splitlines())} lines")
