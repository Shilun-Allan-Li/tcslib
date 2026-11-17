"""wrapmd.py <file> <line>...: rewrap, at 100 columns, the Markdown paragraph or list item that
contains each given line (1-based), keeping backtick spans whole. A list item keeps its marker
and indents its continuation lines to the marker's text. Table rows and code blocks are left
alone. Prints each rewrapped block's line count."""
import re
import sys

p, lines = sys.argv[1], sorted({int(a) for a in sys.argv[2:]}, reverse=True)
if not p.endswith('.md'):
    sys.exit('wrapmd.py rewraps Markdown only (a .lean docstring ends at -/, which it does not see)')
L = open(p, encoding='utf-8').read().split('\n')
ITEM = re.compile(r'^(\s*)([-*]|\d+\.)\s+')


def block(i):
    """The [start, end) of the item or paragraph containing line index i."""
    s = i
    while s > 0 and L[s].strip() and not ITEM.match(L[s]) and L[s - 1].strip() \
            and not L[s - 1].lstrip().startswith(('|', '#', '```')):
        s -= 1
    e = i + 1
    while e < len(L) and L[e].strip() and not ITEM.match(L[e]) \
            and not L[e].lstrip().startswith(('|', '#', '```')):
        e += 1
    return s, e


def wrap(text, first, rest, width=100):
    toks = re.findall(r'`[^`]*`\S*|\S+', text)
    out, cur, empty = [], first, True
    for t in toks:
        if empty:
            cur, empty = cur + t, False
        elif len(cur) + 1 + len(t) > width:
            out.append(cur)
            cur = rest + t
        else:
            cur = cur + ' ' + t
    out.append(cur)
    return out


done = set()
for n in lines:
    i = n - 1
    if L[i].lstrip().startswith('|'):
        continue
    s, e = block(i)
    if s in done:
        continue
    done.add(s)
    m = ITEM.match(L[s])
    if m:
        first = m.group(0)
        rest = ' ' * len(first)
        body = ' '.join([L[s][len(first):].strip()] + [x.strip() for x in L[s + 1:e]])
    else:
        lead = L[s][:len(L[s]) - len(L[s].lstrip())]
        first, rest = lead, lead
        body = ' '.join(x.strip() for x in L[s:e])
    new = wrap(body, first, rest)
    L[s:e] = new
    print(n, '->', len(new), 'lines, max', max(len(x) for x in new))
open(p, 'w', encoding='utf-8').write('\n'.join(L))
