"""Classify every non-blank, non-comment line of a probe file by its leading command (python3 -I).
usage: python3 -I probescan.py <file>..."""
import re, sys
from collections import Counter
for f in sys.argv[1:]:
    c = Counter(); odd = []
    depth = 0
    for n, l in enumerate(open(f, encoding='utf-8'), 1):
        s = l.strip()
        if depth or s.startswith('/-'):
            depth += s.count('/-') - s.count('-/')
            if depth < 0: depth = 0
            continue
        if not s or s.startswith('--'): continue
        m = re.match(r'(import|#check|#print|open|set_option|namespace|end|section|attribute|example)\b', s)
        if m: c[m.group(1)] += 1
        else: c['other'] += 1; odd.append((n, s[:100]))
    bad = [o for o in odd if re.search(r'#eval|run_cmd|run_elab|run_meta|elab|macro|IO\.|initialize|unsafe|extern', o[1])]
    print(f, dict(c), 'risky:', bad, 'other lines:', len(odd))
