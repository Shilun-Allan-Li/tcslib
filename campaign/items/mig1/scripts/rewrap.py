import sys, textwrap, re
p = sys.argv[1]; L = open(p, encoding='utf-8').read().split('\n')
out = []
for l in L:
    if len(l) <= 100 or l.startswith('|') or l.startswith('#'):
        out.append(l); continue
    m = re.match(r'^(\s*(?:\* |\d+\. )?)', l)
    lead = m.group(1)
    sub = ' ' * len(lead)
    w = textwrap.wrap(l[len(lead):], width=100 - len(lead), break_long_words=False, break_on_hyphens=False)
    out.append(lead + w[0])
    out.extend(sub + x for x in w[1:])
open(p, 'w', encoding='utf-8').write('\n'.join(out))
for i, l in enumerate(out, 1):
    if len(l) > 100 and not l.startswith('|'): print('LONG', i, len(l))
