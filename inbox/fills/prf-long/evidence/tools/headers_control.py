#!/usr/bin/env python3
"""Control of the header check (brief: a copy with one header altered by one character must report
exactly one difference). Copies the working-tree FILE, changes one character inside the header of
the declaration DECL (the first `n` of its header becomes `m` after the colon of its type), runs
headers.py --pair on the base and the altered copy, and checks that it reports exactly one
difference.  usage: headers_control.py REPO BASE_REV FILE DECL OUTDIR"""
import os, subprocess, sys
repo, rev, f, decl, out = sys.argv[1:6]
os.makedirs(out, exist_ok=True)
base = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True, text=True,
                      check=True).stdout
cur = open(f'{repo}/{f}').read()
i = cur.index(f'theorem {decl} ')
j = cur.index(':=', i)
hdr = cur[i:j]
k = hdr.rindex('n')
altered = cur[:i] + hdr[:k] + 'm' + hdr[k + 1:] + cur[j:]
assert sum(a != b for a, b in zip(cur, altered)) == 1 and len(cur) == len(altered)
open(f'{out}/base.lean', 'w').write(base)
open(f'{out}/altered.lean', 'w').write(altered)
p = subprocess.run(['python3', '-I', '/workspace/pltools/headers.py', '--pair', f'{out}/base.lean',
                    f'{out}/altered.lean'], capture_output=True, text=True)
open(f'{out}/control-output.txt', 'w').write(p.stdout + p.stderr)
diffs = [l for l in p.stdout.splitlines() if l.startswith('DIFF')]
print(f'altered one character (position {i + k}) in the header of {decl}: '
      f'{len(diffs)} difference(s) reported -> {"PASS" if len(diffs) == 1 else "FAIL"}')
for d in diffs:
    print(' ', d)
