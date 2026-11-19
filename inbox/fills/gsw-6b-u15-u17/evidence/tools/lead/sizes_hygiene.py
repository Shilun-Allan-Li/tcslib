#!/usr/bin/env python3
"""C8 sizes and C9 hygiene (gsw-6b-u15-u17; the u12 tool for several owned files).
usage: sizes_hygiene.py REPO BASE HEAD OUTDIR TAG FILE...
Sizes: lines and maximum width (Python len) of each FILE at BASE and HEAD.
Hygiene: every new private helper (a private declaration absent at BASE) must have a docstring with
a backticked formula or the word "Glue."; every declaration whose block (keyword line to the next
column-0 line) has 20 lines or more must have `**Proof sketch.**` in its docstring."""
import re, subprocess, sys
repo, base, head, out, tag = sys.argv[1:6]
files = sys.argv[6:]
show = lambda r, f: subprocess.run(['git', '-C', repo, 'show', f'{r}:{f}'], capture_output=True,
                                   check=True).stdout.decode()
def size(t):
    L = t.split('\n')[:-1] if t.endswith('\n') else t.split('\n')
    return len(L), max(len(l) for l in L)
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private|protected|noncomputable)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure)\s+(\S+)')
srows, rows, bad, over100, over1000 = [], [], 0, 0, 0
for f in files:
    B, H = show(base, f), show(head, f)
    bl, bw = size(B); hl, hw = size(H)
    over100 += hw > 100; over1000 += hl > 1000
    srows.append(f'{f}\tbase {bl} lines, max width {bw}\thead {hl} lines, max width {hw}\tfill +{hl - bl}')
    L = H.split('\n')
    bpriv = {m.group(3) for l in B.split('\n') if (m := DECL.match(l)) and 'private' in (m.group(1) or '')}
    for i, l in enumerate(L):
        m = DECL.match(l)
        if not m:
            continue
        j = i + 1
        while j < len(L) and not (L[j] and not L[j][0].isspace()):
            j += 1
        doc = ''
        if i > 0 and L[i - 1].rstrip().endswith('-/'):
            k = i - 1
            while k >= 0 and not L[k].startswith('/--'):
                k -= 1
            doc = '\n'.join(L[k:i])
        n = j - i
        new_priv = 'private' in (m.group(1) or '') and m.group(3) not in bpriv
        fl = (new_priv and not ('`' in doc or 'Glue.' in doc))
        sk = n >= 20 and '**Proof sketch.**' not in doc
        bad += fl + sk
        rows.append(f'{f.split("/")[-1]}\t{m.group(3)}\tlines {n}\tnew private {new_priv}'
                    f'\tformula/Glue {"`" in doc or "Glue." in doc}'
                    f'\tsketch {"**Proof sketch.**" in doc}\t{"FLAG" if fl or sk else "ok"}')
srows.append(f'RESULT over100={over100} over1000={over1000}')
rows.append(f'RESULT flagged={bad}')
open(f'{out}/sizes-{tag}.txt', 'w').write('\n'.join(srows) + '\n')
open(f'{out}/hygiene-{tag}.txt', 'w').write('\n'.join(rows) + '\n')
print('\n'.join(srows) + '\n' + rows[-1])
