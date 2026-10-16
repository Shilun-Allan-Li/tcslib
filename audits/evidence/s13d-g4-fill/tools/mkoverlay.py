"""Write the G4 fill brief's pre-ship overlay of `Build/ZoneRebalance.lean` (read-only).

Usage: python3 -I mkoverlay.py <base ZoneRebalance.lean> <home block> <out>
The two imports the user authorized (2026-10-15) after the file's imports, and the recommended
home block before the rows' section header. Each edit is asserted to match once; removing them
reproduces the input, and the two rows' statements are untouched.
"""
import sys
base, home, out = sys.argv[1:4]
t = open(base, encoding='utf-8').read(); h = open(home, encoding='utf-8').read()
IMP = "import TCSlib.Complexity.TuringMachine.Build.Contract.Basic\n"
NEW = ("import TCSlib.Complexity.TuringMachine.Build.Contract.Catalog\n"
       "import TCSlib.Complexity.TuringMachine.Build.Contract.Seam\n")
ROWS = "/-! ### The rows -/\n"
assert t.count(IMP) == 1 and t.count(ROWS) == 1
o = t.replace(IMP, IMP + NEW).replace(ROWS, h + ROWS)
assert o.replace(NEW, '', 1).replace(h, '', 1) == t
open(out, 'w', encoding='utf-8').write(o)
print('overlay written:', len(o.splitlines()), 'lines')
