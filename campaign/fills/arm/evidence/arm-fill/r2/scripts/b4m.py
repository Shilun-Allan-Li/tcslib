"""Declarations (comment-stripped headers, by kind) in a line range of a Lean file, and the
references to b4m-named declarations from declarations outside that set.
usage: python3 -I b4m.py <file> <lo> <hi>"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore import strip_keep_lines
f, lo, hi = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
src = open(f, encoding='utf-8').read(); t = strip_keep_lines(src).split('\n')
H = re.compile(r'^[ \t]*(?:@\[[^\]]*\][ \t]*)*((?:(?:private|protected|noncomputable)\s+)*)(def|abbrev|theorem|lemma|inductive|structure|instance)\s+(\S+)')
allds = [(i + 1, m.group(2), m.group(3), 'private' in m.group(1)) for i, l in enumerate(t) for m in [H.match(l)] if m]
d = [x for x in allds if lo <= x[0] <= hi]
kinds = {}
for x in d: kinds[x[1]] = kinds.get(x[1], 0) + 1
print(f'lines {lo}-{hi} ({hi - lo + 1} lines): {len(d)} declarations, kinds {dict(sorted(kinds.items()))}; '
      f'all private: {all(x[3] for x in d)}; b4m-named: {sum(1 for x in d if x[2].startswith("b4m"))}; first header line {d[0][0]}, last {d[-1][0]}')
print('outside the range, declarations whose name starts with b4m:', [x for x in allds if x[2].startswith('b4m') and not lo <= x[0] <= hi] or 'none')
starts = {x[0]: x for x in allds}; cur = None; refs = []
for i, l in enumerate(t, 1):
    if i in starts: cur = starts[i]
    if cur and not (lo <= cur[0] <= hi):
        refs += [(i, cur[2], n) for n in re.findall(r'\bb4m\w*', l)]
print('code references to b4m names from declarations outside the range:', refs or 'none')
print('first raw line of the range:', src.split('\n')[lo - 1][:90])
print('last raw line of the range:', src.split('\n')[hi - 1][:90], '| next:', src.split('\n')[hi][:60])
