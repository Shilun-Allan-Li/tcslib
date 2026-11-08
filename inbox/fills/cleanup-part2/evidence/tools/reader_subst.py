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
    props[it['file']].append((it['line'], it['tactic'], it['ident'], it['ident'] + reader))
for f, ps in sorted(props.items()):
    print('==', f)
    for p in ps: print('  ', p)
print('MISSING READERS:', missing.most_common())
if apply:
    for f, ps in props.items():
        lines = open(f'{root}/{f}').read().split('\n')
        for ln, tac, ident, new in ps:
            l = lines[ln - 1]
            if tac in ('unfold', 'delta'):
                m = re.search(r'\b(unfold|delta)\s+(.*)$', l)
                if not m: continue
                rest = m.group(2)
                at = ''
                if ' at ' in rest: rest, at = rest.split(' at ', 1); at = ' at ' + at
                ids = rest.split()
                ids = [x + ('_def' if x == ident and new.endswith('_def') else '_eq' if x == ident else '') for x in ids]
                lines[ln - 1] = l[:m.start()] + 'simp only [' + ', '.join(ids) + ']' + at
            else:
                lines[ln - 1] = re.sub(r'(?<![\w.\'])' + re.escape(ident) + r'(?![\w.\'])', new, l, count=1)
        open(f'{root}/{f}', 'w').write('\n'.join(lines))
