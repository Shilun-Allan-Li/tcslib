#!/usr/bin/env python3
"""Route anonymous-constructor/rcases reads of foreign predicate definitions through their owner
`_iff` readers, from the sealed-probe diagnostics of a phase (cleanup-part2 J work).

python3 -I autofix_iff.py <phase> <root> [--apply] [modules...]

Handled diagnostics (position = probe line/column mapped back to the source):
* "Invalid `⟨...⟩` notation: The expected type `P …` is not an inductive type" → insert
  `(IFF _).2 ` before the `⟨` at that position;
* "Tactic `rcases` failed: `h : P …` is not an inductive datatype" where the position starts an
  `obtain pat := h` / `rcases h with pat` whose target is exactly the named hypothesis → replace
  the target by `(IFF _).1 h`.
P is matched by its head constant against IFF_MAP; other diagnostics are left for manual work."""
import sys, re, json, os
phase, root = sys.argv[1], sys.argv[2]
apply = '--apply' in sys.argv
only = [a for a in sys.argv[3:] if not a.startswith('--')]
EV = '/workspace/cp2/evidence/logs'
IFF_MAP = [
    (r'PolyTimeComputable\b', 'Complexity.polyTimeComputable_iff'),
    (r'\S+\.Efficient\b', 'TCSlib.Cryptography.Strategy.efficient_iff'),
]
seal = json.load(open(f'{EV}/seal-{phase}.json'))
todo = {}
for path, d in seal.items():
    if only and path not in only: continue
    rel = f'.lake/cleanup-part2-probes/seal/{phase}/{path}'
    probe = open(f'/workspace/cp2/src/{rel}.lean').read().split('\n')
    w = next(i for i, l in enumerate(probe) if l.startswith('-- CP2 WHOLE-FILE SEAL')) + 1
    b = next(i for i, l in enumerate(probe) if l == '-- CP2 END SEAL') + 1
    off = b - w + 2
    log = open(f'{EV}/seal-{phase}/modules/{rel}.log').read()
    for m in re.finditer(r'\.lean:(\d+):(\d+): error: (Invalid `⟨\.\.\.⟩` notation: The expected type\s+`?([^\n`]*)|Tactic `rcases` failed: `([^`]*?) : ([^`]*)` is not an inductive datatype)', log):
        ln, col = int(m.group(1)), int(m.group(2))
        if ln <= b: continue
        s = ln - off
        if m.group(4) is not None:
            ty = m.group(4).strip()
            if not ty:  # type printed on the next lines
                rest = log[m.end():m.end() + 400].split('\n')
                ty = next((x.strip() for x in rest if x.strip()), '')
            for pat, iff in IFF_MAP:
                if re.match(pat, ty):
                    todo.setdefault(path, []).append(('anon', s, col, iff, ty)); break
        else:
            hyp, ty = m.group(5), m.group(6)
            for pat, iff in IFF_MAP:
                if re.match(pat, ty):
                    todo.setdefault(path, []).append(('rcases', s, col, iff, hyp)); break
tot = 0; skipped = []
for path, items in todo.items():
    f = f'{root}/{path}.lean'
    L = open(f).read().split('\n')
    for kind, s, col, iff, info in sorted(items, key=lambda x: (-x[1], -x[2])):
        line = L[s - 1]
        if kind == 'anon':
            if col < len(line) and line[col] == '⟨':
                L[s - 1] = line[:col] + f'({iff} _).2 ' + line[col:]; tot += 1
            else:
                skipped.append((path, s, col, kind, line.strip()))
        else:
            hyp = info
            m1 = re.match(r'^(\s*(?:obtain|rcases)\b.*?:=\s*)(' + re.escape(hyp) + r')\s*$', line)
            m2 = re.match(r'^(\s*rcases\s+)(' + re.escape(hyp) + r')(\s+with\b.*)$', line)
            if m1 and line.find('obtain') >= 0:
                L[s - 1] = m1.group(1) + f'({iff} _).1 {hyp}'; tot += 1
            elif m2:
                L[s - 1] = m2.group(1) + f'({iff} _).1 {hyp}' + m2.group(3); tot += 1
            else:
                skipped.append((path, s, col, kind, line.strip()))
    if apply: open(f, 'w').write('\n'.join(L))
print('fixed', tot)
for x in skipped: print('SKIP', x)
