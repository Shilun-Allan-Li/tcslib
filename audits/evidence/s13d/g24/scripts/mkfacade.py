"""Write the landed `TuringMachine` facade: the base's (which has PR #92's additions) with the two
new modules imported after `Build.Zone` and the `## Contents` entry of `Build/Zone` revised and
followed by entries for the two new modules. Asserted, content-anchored edits; read-only on the
base. Usage: mkfacade.py <base tree> <out.lean>"""
import sys
base, out = sys.argv[1:3]
t = open(f"{base}/TCSlib/Complexity/TuringMachine.lean", encoding="utf-8").read()


def rep(s, a, b):
    assert s.count(a) == 1, a[:70]
    return s.replace(a, b)


t = rep(t, "import TCSlib.Complexity.TuringMachine.Build.Zone\n",
        "import TCSlib.Complexity.TuringMachine.Build.Zone\n"
        "import TCSlib.Complexity.TuringMachine.Build.ZoneTape\n"
        "import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance\n")
t = rep(t, "* `Build/Zone` — the zoned tape carrier (§13, Z2), under the §13d revision: its two\n"
        "  superseded shift rows are scheduled for retirement through the G3/G4 gate.\n",
        "* `Build/Zone` — the pure zone layer (§13, Z2, as revised by §13d): zone contents, the\n"
        "  guarded pairwise ops, the cascade and its mirror, the scanned index, the total rebalance,\n"
        "  the extension by one level, and the virtual tape a track represents.\n"
        "* `Build/ZoneTape` — the multi-track zoned carrier over `ZoneSym k` (§13d, G3): the layout\n"
        "  with blank separators, the inner-packed encoding `zonedTape` and its invariants.\n"
        "* `Build/ZoneRebalance` — the rebalance and extension rows (§13d, G4), as contracts;\n"
        "  sorried for the G4 fill.\n")
open(out, "w", encoding="utf-8").write(t)
print("facade written")
