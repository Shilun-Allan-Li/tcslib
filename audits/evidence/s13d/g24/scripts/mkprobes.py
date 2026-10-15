"""Write the two probe files: each is the unit with the extra imports its tail needs, followed
by the tail (read-only on the unit and the tails). Usage: mkprobes.py <G>."""
import sys
G = sys.argv[1]
unit = open(f"{G}/G24Statements.lean", encoding="utf-8").read()
last = "import TCSlib.Complexity.TuringMachine.Build.Contract.Basic\n"
assert unit.count(last) == 1
for name, extra, tail in [
    ("G24FitProbe", ["Mathlib.Algebra.BigOperators.Ring.Finset",
                     "TCSlib.Complexity.TuringMachine.Build.Contract.Seam"], "fit.tail"),
    ("G24Sanity", ["Mathlib.Tactic.FinCases"], "sanity.tail"),
]:
    u = unit.replace(last, last + "".join(f"import {m}\n" for m in extra))
    t = open(f"{G}/parts/{tail}", encoding="utf-8").read()
    open(f"{G}/probes/{name}.lean", "w", encoding="utf-8").write(u.rstrip("\n") + "\n\n" + t)
    print(f"probes/{name}.lean: unit + {len(extra)} import(s) + {tail}")
