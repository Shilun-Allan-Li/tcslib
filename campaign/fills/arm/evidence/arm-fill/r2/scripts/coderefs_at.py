"""Code-only (comment-stripped) references to names in files given as (path, local copy) pairs,
excluding each name's own declaration header line. usage: python3 -I coderefs_at.py name1,name2 <path>=<copy> ..."""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore import strip_keep_lines
names = sys.argv[1].split(','); n = 0
H = re.compile(r'^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev|theorem|lemma)\s+(\S+)')
for arg in sys.argv[2:]:
    path, copy = arg.split('=', 1)
    for i, l in enumerate(strip_keep_lines(open(copy, encoding='utf-8').read()).split('\n'), 1):
        m = H.match(l)
        for nm in names:
            if re.search(r'(?<![\w.])(?:[\w.]*\.)?' + re.escape(nm) + r'\b', l) and not (m and m.group(1).split('.')[-1] == nm):
                n += 1; print(f'{path}:{i}: {l.strip()[:120]}')
print(f'code references outside the declaring headers: {n}')
