import re, sys
ITEM = re.compile(r'^(\s*)(- |\d+\. )')
def spaces_outside_ticks(s):
    out, inside = [], False
    for i, ch in enumerate(s):
        if ch == '`': inside = not inside
        elif ch == ' ' and not inside: out.append(i)
    return out
def wrap(text, first_prefix, cont_indent, width=100):
    words, cur, inside = [], '', False
    for ch in text:
        if ch == '`': inside = not inside
        if ch == ' ' and not inside:
            if cur: words.append(cur); cur = ''
        else: cur += ch
    if cur: words.append(cur)
    lines, line = [], first_prefix
    for w in words:
        cand = (line + ' ' + w) if line.strip() and not line.endswith(' ') else line + w
        if len(cand) > width and line.strip() and line != first_prefix:
            lines.append(line); line = cont_indent + w
        else: line = cand
    lines.append(line)
    return lines
def items(lines):
    i, n, fence = 0, len(lines), False
    while i < n:
        l = lines[i]
        if l.lstrip().startswith('```'): fence = not fence; i += 1; continue
        m = ITEM.match(l)
        if fence or not m: i += 1; continue
        ind = len(m.group(1)) + len(m.group(2)); j = i + 1
        while j < n and lines[j].strip() and not lines[j].lstrip().startswith('```') and not ITEM.match(lines[j]) \
              and len(lines[j]) - len(lines[j].lstrip()) >= ind and not lines[j].lstrip().startswith('|'):
            j += 1
        yield i, j, m.group(1) + m.group(2), ' ' * ind
        i = j
p = sys.argv[1]; targets = set(int(x) for x in sys.argv[2:])
lines = open(p, encoding='utf-8').read().split('\n')
spans = [(a, b, fp, ci) for a, b, fp, ci in items(lines) if any(a < t <= b for t in targets) or any(a + 1 == t for t in targets)]
for a, b, fp, ci in sorted(spans, reverse=True):
    body = ' '.join(x.strip() for x in lines[a:b])[len(fp.strip()):].strip()
    lines[a:b] = wrap(body, fp, ci)
open(p, 'w', encoding='utf-8').write('\n'.join(lines))
print('reflowed', len(spans), 'items; over 100:', [(i+1, len(l)) for i, l in enumerate(lines) if len(l) > 100 and not l.startswith(('#', '|'))])
