#!/usr/bin/env python3
"""C8 sizes and C9 hygiene (gsw-6b-u12; for gsw-6b-u18-u19: results are appended per file, and a new
public declaration is checked like a new private helper). usage: sizes_hygiene.py REPO BASE HEAD FILE OUTDIR TAG
Sizes: lines and maximum width (Python len) of FILE at BASE and HEAD.
Hygiene: every new private helper (a private declaration absent at BASE) must have a docstring with
a backticked formula or the word "Glue."; every declaration whose block (keyword line to the next
column-0 line) has 20 lines or more must have `**Proof sketch.**` in its docstring."""
import re, subprocess, sys
repo, base, head, f, out, tag = sys.argv[1:7]
show = lambda r: subprocess.run(['git', '-C', repo, 'show', f'{r}:{f}'], capture_output=True,
                                check=True).stdout.decode()
B, H = show(base), show(head)
def size(t):
    L = t.split('\n')[:-1] if t.endswith('\n') else t.split('\n')
    return len(L), max(len(l) for l in L)
bl, bw = size(B); hl, hw = size(H)
open(f'{out}/sizes-{tag}.txt', 'a').write(
    f'{f}\tbase {bl} lines, max width {bw}\thead {hl} lines, max width {hw}\tfill +{hl - bl}\n'
    f'RESULT {f} over100={int(hw > 100)} over1000={int(hl > 1000)}\n')
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private|protected|noncomputable)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure)\s+(\S+)')
L = H.split('\n')
bpriv = {m.group(3) for l in B.split('\n') if (m := DECL.match(l))}
rows, bad = [], 0
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
    new_priv = m.group(3) not in bpriv  # every declaration absent at BASE (private or public)
    fl = (new_priv and not ('`' in doc or 'Glue.' in doc))
    sk = n >= 20 and '**Proof sketch.**' not in doc
    bad += fl + sk
    rows.append(f'{m.group(3)}\tlines {n}\tnew {new_priv}\tformula/Glue {"`" in doc or "Glue." in doc}'
                f'\tsketch {"**Proof sketch.**" in doc}\t{"FLAG" if fl or sk else "ok"}')
rows.append(f'RESULT {f} flagged={bad}')
open(f'{out}/hygiene-{tag}.txt', 'a').write(f'# {f}\n' + '\n'.join(rows) + '\n')
print(rows[-1])
