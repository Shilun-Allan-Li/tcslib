#!/usr/bin/env python3
"""Wrap lines longer than 100 columns that this fill added (cleanup-part2 style pass).

python3 -I wrap_long.py <base-rev> <file.lean>... [--apply]

Only lines absent from the base revision's version of the file are touched:
* a one-line docstring `/-- text -/` is re-flowed into a multi-line docstring at the same indent;
* a simp/rw list line is broken after the last comma before column 100 inside its brackets,
  continuing at the line's indent + 4 (other code lines are left and reported).
Lines with `--` comments or string literals are left alone and reported."""
import sys, subprocess, difflib, re
W = 100
base = sys.argv[1]; apply = '--apply' in sys.argv
files = [a for a in sys.argv[2:] if not a.startswith('--')]
left = []

def wrap_words(words, first_prefix, cont_prefix, width=W):
    lines = []; cur = first_prefix
    for w in words:
        cand = (cur + ' ' + w) if cur.strip() and not cur.endswith(' ') else cur + w
        if len(cand) > width and cur.strip() and cur not in (first_prefix, cont_prefix):
            lines.append(cur.rstrip()); cur = cont_prefix + w
        else:
            cur = cand
    lines.append(cur.rstrip())
    return lines

def split_code(span, limit=60):
    """Split a long code span at the spaces of least bracket depth, recursively."""
    if len(span) <= limit: return [span]
    depth = 0; spaces = []
    for i, ch in enumerate(span):
        if ch in '([{⟨': depth += 1
        elif ch in ')]}⟩': depth -= 1
        elif ch == ' ': spaces.append((depth, i))
    if not spaces: return [span]
    dmin = min(d for d, _ in spaces)
    cuts = [i for d, i in spaces if d == dmin]
    pieces = []; prev = 0
    for c in cuts:
        pieces.append(span[prev:c]); prev = c + 1
    pieces.append(span[prev:])
    out = []
    for pc in pieces:
        out += split_code(pc, 90) if len(pc) > 90 else [pc]
    return out

def atoms(text):
    """Split prose at spaces; keep a backtick code span whole when short, else split it at its
    outermost spaces."""
    words = text.split(' '); out = []; cur = None
    for w in words:
        if cur is not None:
            cur += ' ' + w
            if w.count('`') % 2 == 1:
                out.append(cur); cur = None
            continue
        if w.count('`') % 2 == 1:
            cur = w
        else:
            out.append(w)
    if cur is not None: out.append(cur)
    res = []
    for a in out:
        if len(a) > 60 and ' ' in a: res += split_code(a)
        else: res.append(a)
    return res

def wrap_doc(line):
    m = re.match(r'^(\s*)/-- (.*) -/\s*$', line)
    if not m: return None
    ind, text = m.group(1), m.group(2)
    out = wrap_words(atoms(text), ind + '/-- ', ind)
    if len(out[-1]) + 3 <= W: out[-1] += ' -/'
    else: out.append(ind + '-/')
    return out

def break_code(line, cont=False):
    """Break a simp/rw list after the last comma before column 100 inside its brackets."""
    if '--' in line or '"' in line: return None
    if not cont and not re.search(r"(simp_all|simp_rw|simpa|simp|dsimp|field_simp|rwa|rw|erw|nth_rw|norm_num)\b[^\[]*\[", line):
        return None
    ind = len(line) - len(line.lstrip())
    depth = 1 if cont else 0; best = None
    for i, ch in enumerate(line):
        if ch == '[': depth += 1
        elif ch == ']': depth -= 1
        if i >= W - 1: break
        if ch == ',' and depth >= 1 and i + 1 < len(line) and line[i + 1] == ' ': best = i + 1
    if best is None: return None
    a = line[:best].rstrip(); rest = ' ' * (ind + 4) + line[best:].lstrip()
    res = [a]
    if len(rest) > W:
        more = break_code(rest, cont=True)
        res += more if more else [rest]
    else: res.append(rest)
    return res

def break_term(line):
    """Break a long term line at the last space before column 100 of least positive bracket depth
    (relative to the line start), continuing at the line's indent + 4."""
    if '--' in line or '"' in line: return None
    t = line.lstrip()
    if t.startswith(('obtain', 'rcases', 'rintro', 'theorem', 'lemma', 'def ', 'private', '|', '·')):
        return None
    ind = len(line) - len(t)
    depth = 0; cands = []
    for i, ch in enumerate(line):
        if i >= W: break
        if ch in '([{⟨': depth += 1
        elif ch in ')]}⟩': depth -= 1
        elif ch == ' ' and i > ind + 12 and line[i - 1] not in '([{⟨' and depth >= 1:
            cands.append((depth, i))
    if not cands: return None
    dmin = min(d for d, _ in cands)
    cut = max(i for d, i in cands if d == dmin)
    a = line[:cut].rstrip(); rest = ' ' * (ind + 4) + line[cut:].lstrip()
    res = [a]
    if len(rest) > W:
        more = break_term(rest)
        res += more if more else [rest]
    else: res.append(rest)
    return res

def reflow(par):
    """Re-flow a docstring paragraph (list of lines, the last may end with `-/`)."""
    ind = par[0][:len(par[0]) - len(par[0].lstrip())]
    text = ' '.join(x.strip() for x in par)
    close = text.endswith('-/')
    if close: text = text[:-2].rstrip()
    first = ''
    if text.startswith('/-- '): first = '/-- '; text = text[4:]
    out = wrap_words(atoms(text), ind + first, ind)
    if close:
        if len(out[-1]) + 3 <= W: out[-1] += ' -/'
        else: out.append(ind + '-/')
    return out

for f in files:
    try:
        old = subprocess.run(['git', 'show', f'{base}:{f}'], capture_output=True, text=True, check=True).stdout.split('\n')
    except subprocess.CalledProcessError:
        old = []
    new = open(f).read().split('\n')
    oldset = set(old)
    # comment depth before each line
    depth = []; d = 0
    for l in new:
        depth.append(d)
        d += l.count('/-') - l.count('-/')
        if d < 0: d = 0
    out = []; changed = 0; i = 0
    while i < len(new):
        l = new[i]
        if len(l) > W and l not in oldset:
            w = wrap_doc(l)
            if w is None and depth[i] > 0 and '/-' not in l:
                # paragraph inside a docstring: from the previous blank/opening line to the next blank/closing
                a = i
                while a - 1 >= 0 and new[a - 1].strip() and depth[a - 1] > 0 and '/-' not in new[a - 1] \
                        and not new[a - 1].rstrip().endswith('-/'):
                    a -= 1
                b = i
                while b + 1 < len(new) and new[b + 1].strip() and not new[b].rstrip().endswith('-/') \
                        and '/-' not in new[b + 1]:
                    b += 1
                par = new[a:b + 1]
                if any(re.match(r'^\s*([*+-] |\d+\.|```|\|)', x) for x in par):
                    left.append(f'{f}: {len(l)}: {l[:120]}'); out.append(l); i += 1; continue
                # drop the already-emitted head of the paragraph
                del out[len(out) - (i - a):]
                out += reflow(par); changed += 1; i = b + 1; continue
            if w is None and depth[i] == 0 and not l.strip().startswith(('/-', '-/')):
                w = break_code(l)
                if w is None and '--terms' in sys.argv: w = break_term(l)
            if w:
                out += w; changed += 1
            else:
                left.append(f'{f}: {len(l)}: {l[:120]}'); out.append(l)
        else:
            out.append(l)
        i += 1
    if changed:
        print(f'{f}: {changed} wrapped')
        if apply: open(f, 'w').write('\n'.join(out))
print('LEFT', len(left))
for x in left: print('  ', x)
