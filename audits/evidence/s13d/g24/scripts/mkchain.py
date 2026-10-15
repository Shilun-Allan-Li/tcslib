"""Write the landed chain: the landed Build/Zone.lean (narrowed imports) with the imports of
ZoneTape and ZoneRebalance added, followed by those two landed modules' bodies. It checks that
the two new modules elaborate against the narrowed Zone closure (read-only on its inputs)."""
import sys
G = sys.argv[1]
L = f"{G}/landed/TCSlib/Complexity/TuringMachine/Build"
z = open(f"{L}/Zone.lean", encoding="utf-8").read()
imp = "import Mathlib.Data.List.FinRange\n"
assert z.count(imp) == 1
z = z.replace(imp, imp + "import TCSlib.Complexity.TuringMachine.Simulation\n"
              "import TCSlib.Complexity.TuringMachine.Build.Contract.Basic\n")


def body(path):
    s = open(path, encoding="utf-8").read()
    marker = "set_option autoImplicit false\n"
    assert s.count(marker) == 1
    return s.split(marker, 1)[1]


t = body(f"{L}/ZoneTape.lean")
r = body(f"{L}/ZoneRebalance.lean")
open(sys.argv[2], "w", encoding="utf-8").write(z + "\n" + t + "\n" + r)
print(f"chain: {len((z + t + r).splitlines())} lines")
