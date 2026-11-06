"""classify.py <worktree> <rev_old> <rev_new> <files.txt> <sig_old.tsv> <sig_new.tsv> <out.tsv>

Declaration change classifier (gate 04 round 5). For every declaration of each file at <rev_new>
(extents from tools/declx.py), compare with <rev_old>:
* text: the declaration's statement-and-proof text, docstring excluded, whitespace-normalised;
* sig: the elaborated signature from tools/sigdump_body.lean at both revisions (type with binder
  names erased and universe parameters renamed by position; the number of universe parameters);
  `sig-strict` also distinguishes the universe arguments of referenced constants, `sig` erases them;
* value: for definitions, the normalised elaborated value.
* ambient: the scope commands in force at the declaration (`variable`, `universe`, `open`, `omit`,
  `include`, `namespace`, `section`, `end`, `set_option`, `attribute` at top level before it).
Status:
* ADDED: absent at <rev_old>;
* CHANGED: the text, the number of universe parameters or a definition's value differs, or the
  elaborated signature differs while the ambient scope commands differ too (an ambient `variable`
  binder changed, the case of gate 04 R4-01);
* INDUCED: text, universe parameters and ambient scope are unchanged, but the elaborated signature
  differs: the difference comes only from referenced constants whose own signatures #195 changed
  (e.g. `OracleAdversary`'s universe arity, `prfAdv`'s implicit-argument order);
* SAME: everything equal.
Declarations without a constant (examples, anonymous instances) are compared on text and ambient
scope only. Output columns:
file, name, kind, dstart-start-end, status, text, sig, sig-strict, levels, value, ambient."""
import re
AMB = re.compile(r'^(variable|universe|open|omit|include|namespace|section|noncomputable section|end|set_option|attribute)\b')
def ambient(src, upto):
    """The scope commands in force at line `upto`: a stack of namespace/section levels, each with
    the variable/universe/open/omit/include/attribute/set_option commands issued in it."""
    if src is None: return None
    stack = [['<file>']]
    depth = 0
    for l in src.split('\n')[:upto - 1]:
        if depth > 0 or l.startswith('/-'):
            depth += l.count('/-') - l.count('-/')
            continue
        w = ' '.join(l.split())
        if re.match(r'^(namespace|section|noncomputable section)\b', l):
            stack.append([w])
        elif re.match(r'^end\b', l):
            if len(stack) > 1: stack.pop()
        elif re.match(r'^(variable|universe|open|omit|include|attribute|set_option)\b', l) and \
                not l.rstrip().endswith(' in'):
            stack[-1].append(w)
    return '\n'.join('\n'.join(level) for level in stack)
import os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import declx

WT, R0, R1, FILES, S0, S1, OUT = sys.argv[1:8]

def sigs(p):
    d = {}
    for l in open(p, encoding='utf-8'):
        q = l.rstrip('\n').split('\t')
        if len(q) == 7:
            d[q[1]] = q[2:]          # kind, nlevels, strict, erased, value
    return d
sig0, sig1 = sigs(S0), sigs(S1)

def show(rev, path):
    r = subprocess.run(['git', '-C', WT, 'show', f'{rev}:{path}'], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None

rows = []
for path in [l.strip() for l in open(FILES) if l.strip()]:
    old, new = show(R0, path), show(R1, path)
    oe = {e['name']: e for e in declx.extents(old)} if old is not None else {}
    om = {n: declx.body_text(old, e) for n, e in oe.items()}
    for e in declx.extents(new):
        n = e['name']
        b = declx.body_text(new, e)
        t = 'ADDED' if n not in om else ('same' if om[n] == b else 'changed')
        am = 'n/a' if n not in oe else ('same' if ambient(old, oe[n]['dstart']) == ambient(new, e['dstart']) else 'changed')
        a, z = sig0.get(n), sig1.get(n)
        if z is None:
            sg = sgs = lv = va = 'n/a'
        elif a is None:
            sg = sgs = lv = va = 'ADDED'
        else:
            sg = 'same' if a[3] == z[3] else 'changed'
            sgs = 'same' if a[2] == z[2] else 'changed'
            lv = 'same' if a[1] == z[1] else f'{a[1]}->{z[1]}'
            va = '-' if z[4] == '-' else ('same' if a[4] == z[4] else 'changed')
        sigdiff = 'changed' in (sg, sgs)
        if t == 'ADDED' and sg in ('ADDED', 'n/a'):
            st = 'ADDED'
        elif t == 'changed' or va == 'changed' or '->' in lv or sg == 'ADDED' or \
                (sigdiff and am == 'changed') or (z is None and am == 'changed'):
            st = 'CHANGED'
        elif sigdiff:
            st = 'INDUCED'
        else:
            st = 'SAME'
        rows.append(f"{path}\t{n}\t{e['kind']}\t{e['dstart']}-{e['start']}-{e['end']}\t{st}\t{t}\t{sg}\t{sgs}\t{lv}\t{va}\t{am}")
open(OUT, 'w', encoding='utf-8').write('\n'.join(rows) + '\n')
from collections import Counter
print(Counter(r.split('\t')[4] for r in rows))
