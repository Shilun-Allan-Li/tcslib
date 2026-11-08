#!/usr/bin/env python3
"""Propose/apply reader substitutions for explicit foreign-definition entries (cleanup-part2).
python3 -I reader_subst.py <name-table.tsv> <scan.json> <root> [--apply] [--files f1,f2]
For each scan item of class FOREIGN_TCS_DEF (not reducible, not instance), look for an owner
reader theorem `<name>_def` then `<name>_eq` homed in the same module as the definition; propose
replacing the identifier occurrence in the tactic list by the reader's spelling (the identifier's
own qualification kept, with the reader suffix). `unfold X`/`delta X` become `simp only [X_def]`
(same `at` clause kept). Prints the proposals; with --apply edits the files in <root>."""
import sys, json, re, collections
table, scanf, root = sys.argv[1:4]
apply = '--apply' in sys.argv
only = None
if '--files' in sys.argv: only = set(sys.argv[sys.argv.index('--files') + 1].split(','))
names = {}
for line in open(table):
    if not line.startswith('NAME\t'): continue
    _, name, kind, status, home, flags = line.rstrip('\n').split('\t')
    names[name] = (kind, status, home, flags)
scan = json.load(open(scanf))
if '--extra' in sys.argv:
    for x in open(sys.argv[sys.argv.index('--extra') + 1]).read().split():
        base = x[:-4]
        if base in names: names[x] = ('thm', '', names[base][2], '')
props = collections.defaultdict(list)
missing = collections.Counter()
for it in scan['items']:
    if not it['class'].startswith('FOREIGN_TCS_DEF'): continue
    if only and it['file'] not in only: continue
    full = it['resolved']; kind, status, home, flags = names[full]
    if 'reducible' in status.lower() and 'semi' not in status.lower(): continue
    if 'instance' in flags: continue
    reader = None
    for suf in ('_def', '_eq'):
        r = names.get(full + suf)
        if r and r[0] == 'thm' and r[2] == home: reader = suf; break
    if not reader:
        missing[full] += 1
        continue
    props[it['file']].append((it['offset'], it['line'], it['tactic'], it['ident'], it['ident'] + reader))
for f, ps in sorted(props.items()):
    print('==', f)
    for p in ps: print('  ', p)
print('MISSING READERS:', missing.most_common())
if apply:
    for f, ps in props.items():
        text = open(f'{root}/{f}').read()
        unf = collections.defaultdict(dict)   # line -> {ident: new}
        other = []
        for off, ln, tac, ident, new in ps:
            if tac in ('unfold', 'delta'): unf[ln][ident] = new
            else: other.append((off, ident, new))
        # simp/rw entries: exact offsets, rightmost first
        for off, ident, new in sorted(other, reverse=True):
            assert text[off:off + len(ident)] == ident, (f, ident, text[off:off + 40])
            text = text[:off] + new + text[off + len(ident):]
        # unfold/delta tactics: rewrite the tactic once per line (offsets no longer needed)
        lines = text.split('\n')
        for ln, mp in unf.items():
            line = lines[ln - 1]
            m = re.search(r'\b(unfold|delta)\s+([^;]*?)(\s+at\s+[^;]*)?(;.*)?$', line)
            if not m: continue
            names = [mp.get(x, x) for x in m.group(2).split()]
            lines[ln - 1] = line[:m.start()] + 'simp only [' + ', '.join(names) + ']' + (m.group(3) or '') + (m.group(4) or '')
        open(f'{root}/{f}', 'w').write('\n'.join(lines))
