"""Build the sanity probe from the current unit (one extra Mathlib import for the counter-value
example), and the negative controls from the probe. Read-only on the unit."""
import os
import sys
O = sys.argv[1]
w = os.path.join(O, "work")
pr = os.path.join(O, "probes")
os.makedirs(pr, exist_ok=True)
unit = open(os.path.join(O, "C1Hosts.lean"), encoding="utf-8").read()
tail = open(os.path.join(O, "scripts", "probe_tail.lean"), encoding="utf-8").read()
anchor = "import TCSlib.Complexity.ClassNP.NTIME\n"
assert unit.count(anchor) == 1
src = unit.replace(anchor, anchor + "import Mathlib.Data.Nat.Digits.Lemmas\n") + tail
open(os.path.join(pr, "C1HostsSanity.lean"), "w", encoding="utf-8").write(src)
negs = [
    ("neg1", "example : 3 * (workReadsK 3).length = 81 ∧ 2 * (3 * (workReadsK 2).length) = 54",
     "example : 3 * (workReadsK 3).length = 80 ∧ 2 * (3 * (workReadsK 2).length) = 54"),
    ("neg2", "    c.state = none ∧ c.workTapePos (Fin.last 0) = 2 := by",
     "    c.state = none ∧ c.workTapePos (Fin.last 0) = 3 := by"),
    ("neg3", "      some (.run ()) := by\n  intro w hw\n  match w, hw with\n  | [a, b], _",
     "      some .done := by\n  intro w hw\n  match w, hw with\n  | [a, b], _"),
]
for name, a, b in negs:
    assert src.count(a) == 1, name
    open(os.path.join(w, name + ".lean"), "w", encoding="utf-8").write(src.replace(a, b))
print("probe and negative controls rebuilt")
