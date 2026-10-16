"""Write the B6 F3 brief's pre-ship overlay of `SpaceComplexity/WindowClock.lean` (read-only).

Usage: python3 -I mkoverlay.py <base WindowClock.lean> <home block> <out>
Inserts the recommended home block (`tools/home.lean.txt`) at the home: before the target's
docstring, after `Turing.FinTM.configBound_le_two_pow`. Asserted to match once; the target's
statement is pinned byte for byte, and removing the block reproduces the input.
"""
import sys
base, home, out = sys.argv[1:4]
t = open(base, encoding='utf-8').read(); h = open(home, encoding='utf-8').read()
DOC = "/-- **H3 with the configuration-count clock** (what `Complexity.space_hierarchy`'s\n"
assert t.count(DOC) == 1
o = t.replace(DOC, h + DOC)
assert o.replace(h, '', 1) == t
open(out, 'w', encoding='utf-8').write(o)
print('overlay written:', len(o.splitlines()), 'lines')
