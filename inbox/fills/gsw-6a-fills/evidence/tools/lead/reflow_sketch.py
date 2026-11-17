"""reflow_sketch.py <file> <line> (gsw-6a-fills, new): re-wrap the `**Proof sketch.**` paragraph that contains
<line> (1-based) to width 100 (Python len), breaking only at spaces; the paragraph runs from the line that starts
with `**Proof sketch.**` to the line ending in `-/` (kept at the end). Only text after **Proof sketch.** changes."""
import sys, textwrap
p, ln = sys.argv[1], int(sys.argv[2]) - 1
L = open(p, encoding='utf-8').read().split('\n')
a = ln
while not L[a].startswith('**Proof sketch.**'): a -= 1
b = ln
while not L[b].rstrip().endswith('-/'): b += 1
text = ' '.join(x.strip() for x in L[a:b + 1])
assert text.endswith('-/'); text = text[:-2].rstrip()
w = textwrap.TextWrapper(width=100, break_long_words=False, break_on_hyphens=False)
out = w.wrap(text)
if len(out[-1]) + 3 <= 100: out[-1] += ' -/'
else: out.append('-/')
L[a:b + 1] = out
open(p, 'w', encoding='utf-8').write('\n'.join(L))
