#!/usr/bin/env python3
"""Re-split converted `unfold` tactics: where an `unfold a b c [at h]` line was converted to
`simp only [a_def, b, c] [at h]`, keep the owner-local names in `unfold` (which also unfolds
partially applied constants) and only the readers in `simp only`:
    simp only [a_def] [at h]
    unfold b c [at h]
python3 -I fix_unfold_split.py <root> <base-rev> <file>..."""
import sys, re, subprocess
root, base = sys.argv[1], sys.argv[2]
for f in sys.argv[3:]:
    diff = subprocess.run(['git', '-C', root, 'diff', '-U0', base, '--', f], capture_output=True, text=True).stdout
    pairs = []
    old = None
    for l in diff.split('\n'):
        if l.startswith('-') and not l.startswith('---') and re.search(r'\b(unfold|delta)\b', l): old = l[1:]
        elif l.startswith('+') and not l.startswith('+++') and old is not None:
            pairs.append((old, l[1:])); old = None
        elif not l.startswith('+'): old = None
    if not pairs: continue
    s = open(f'{root}/{f}').read(); n = 0
    for o, new in pairs:
        mo = re.search(r'\b(unfold|delta)\s+([^;]*?)(\s+at\s+[^;]*)?$', o)
        mn = re.search(r'\bsimp only \[([^\]]*)\](\s+at\s+[^;]*)?$', new)
        if not mo or not mn: continue
        on = mo.group(2).split(); nn = [x.strip() for x in mn.group(1).split(',')]
        readers = [b for a, b in zip(on, nn) if a != b]
        own = [a for a, b in zip(on, nn) if a == b]
        if not own: continue
        ind = new[:len(new) - len(new.lstrip())]
        at = mn.group(2) or ''
        prefix = new[:mn.start()]
        repl = prefix + 'simp only [' + ', '.join(readers) + ']' + at + '\n' + ind + 'unfold ' + ' '.join(own) + at
        if s.count(new) >= 1:
            s = s.replace(new, repl, 1); n += 1
    open(f'{root}/{f}', 'w').write(s)
    if n: print(f, n)
