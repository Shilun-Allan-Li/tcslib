"""Write the G4 continuation brief's pre-ship overlay of `Build/ZoneRebalance.lean` (read-only).

Usage: python3 -I mkoverlay.py <base ZoneRebalance.lean> <home block> <out>
The recommended home block (the two layout bridges) before the rows' section header. The two
imports are already in the file (the first round). The edit is asserted to match once; removing it
reproduces the input, and both rows' statements are pinned byte for byte.
"""
import sys
base, home, out = sys.argv[1:4]
t = open(base, encoding='utf-8').read(); h = open(home, encoding='utf-8').read()
ROWS = "/-! ### The rows -/\n"
assert t.count(ROWS) == 1
for row in ("theorem exists_zoneRebalanceTM (k : ℕ) :", "theorem exists_zoneExtendTM (k : ℕ) :"):
    assert t.count(row) == 1, row
o = t.replace(ROWS, h + ROWS)
assert o.replace(h, '', 1) == t
def stmt(s, row):
    i = s.index(row); return s[i:s.index(":= by", i)]
for row in ("theorem exists_zoneRebalanceTM (k : ℕ) :", "theorem exists_zoneExtendTM (k : ℕ) :"):
    assert stmt(o, row) == stmt(t, row)
open(out, 'w', encoding='utf-8').write(o)
print('overlay written:', len(o.splitlines()), 'lines')
