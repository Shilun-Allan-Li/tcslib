"""rewrap_sketch.py <file>: rewrap T4's Proof sketch paragraph to width 100 without breaking inside
backtick code spans (spaces in spans are kept atomic)."""
import sys, textwrap, re
F = sys.argv[1]; s = open(F, encoding='utf-8').read()
t4 = s.index('theorem exists_bb1_distinguisher')
i = s.rfind('**Proof sketch.**', 0, t4); j = s.index('-/\n', i)
para = ' '.join(s[i:j + 2].split())
P = '\x00'
para = re.sub(r'`[^`]*`', lambda m: m.group(0).replace(' ', P), para)
new = textwrap.fill(para, width=100, break_long_words=False, break_on_hyphens=False).replace(P, ' ')
s = s[:i] + new + '\n' + s[j + 3:]
open(F, 'w', encoding='utf-8').write(s)
