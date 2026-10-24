"""sketches.py <base> <head> : per declaration of the head that is new or changed: docstring present,
'Proof sketch' present, proof length (lines from the declaration header to the next declaration/docstring/section
comment); and campaign-label / date / path scan of the added lines."""
import difflib, re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decls import decls
a = open(sys.argv[1], encoding='utf-8').read(); b = open(sys.argv[2], encoding='utf-8').read()
bl = b.split('\n'); al = a.split('\n')
added = set()
for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, al, bl, autojunk=False).get_opcodes():
    if tag in ('replace', 'insert'): added.update(range(j1 + 1, j2 + 1))
ds = decls(b)
starts = [ln for _, _, ln, _ in ds]
rows = []
for idx, (priv, name, ln, kind) in enumerate(ds):
    # docstring: the nearest '/--' block ending right before ln
    k = ln - 2
    doc = ''
    while k >= 0 and not bl[k].strip(): k -= 1
    if k >= 0 and bl[k].rstrip().endswith('-/'):
        j = k
        while j >= 0 and '/--' not in bl[j]: j -= 1
        doc = '\n'.join(bl[j:k + 1]) if j >= 0 else ''
    # end: next declaration's docstring start or header, or a section comment / end
    nxt = len(bl)
    for j in range(ln, len(bl)):
        s = bl[j]
        if s.startswith(('/--', '/-!', 'end ', 'private ', 'theorem ', 'lemma ', 'def ', 'instance ', 'noncomputable ')) or re.match(r'^(@\[|private|theorem|lemma|def)', s):
            nxt = j; break
    body = bl[ln - 1:nxt]
    m = next((i for i, l in enumerate(body) if l.rstrip().endswith((':= by', ':='))), None)
    if m is None: m = next((i for i, l in enumerate(body) if ':= by' in l), None)
    plen = len([l for l in body[m + 1:] if l.strip()]) if m is not None else 0
    new = any(x in added for x in range(ln, ln + len(body)))
    rows.append((name, ln, kind, priv, bool(doc), 'Proof sketch' in doc, plen, new))
print('declaration | line | kind | private | docstring | "Proof sketch" | proof lines (non-blank) | new/changed')
for r in rows:
    if r[7]: print(' | '.join(str(x) for x in r))
miss = [r for r in rows if r[7] and r[6] > 20 and not r[5]]
print('\nnew/changed proofs over 20 lines without a literal "Proof sketch":', [(r[0], r[6]) for r in miss])
nodoc = [r[0] for r in rows if r[7] and not r[4]]
print('new/changed declarations without a docstring:', nodoc)
# label scan over the added lines (all text, comments included)
PAT = re.compile(r'\b(F[0-9]\b|F3|cont[0-9]|continuation|checkpoint|ground rule|escalat|brief|gate|finding|batch|B6|E2\b|rule 1[01]|R3\b|MIG|Route B|campaign|REPORT|20[0-9]{2}-[0-9]{2}|maintainer|worker|TODO|FIXME|sorry)', re.I)
hits = [(i, bl[i - 1].strip()[:140]) for i in sorted(added) if PAT.search(bl[i - 1])]
print('\nadded lines matching campaign labels / dates / paths / sorry:')
for i, l in hits: print(f'  {i}: {l}')
wide = [(i, len(bl[i - 1])) for i in sorted(added) if len(bl[i - 1]) > 100]
print('\nadded lines over 100 characters:', wide, '; widest added line:', max(len(bl[i - 1]) for i in added))
print('trailing whitespace in added lines:', [i for i in sorted(added) if bl[i - 1] != bl[i - 1].rstrip()])
print('tabs in added lines:', [i for i in sorted(added) if '\t' in bl[i - 1]])
dbl = [i for i in range(1, len(bl)) if not bl[i - 1].strip() and not bl[i].strip() and (i in added or i + 1 in added)]
print('double blank lines touching added lines (head line numbers):', dbl)
