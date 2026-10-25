import sys, json, re
src_df = open(sys.argv[1], encoding='utf-8').read()
ns = {}; exec(compile(src_df.split("a = chunks(open(sys.argv[1]).read())")[0], 'df', 'exec'), ns)
chunks = ns['chunks']
text = open(sys.argv[2], encoding='utf-8').read()
nc = json.load(open(sys.argv[3]))
targets = set(nc['new']) | set(nc['changed'])
B = {n: (p, t) for n, p, t in chunks(text)}
KW = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b', re.M)
rows = []
for n in sorted(targets, key=lambda n: text.find(B[n][1])):
    t = B[n][1]
    doc = t.split('-/', 1)[0] if t.startswith('/--') else ''
    body = t.split('-/', 1)[1] if t.startswith('/--') else t
    kind = KW.search(body).group(1)
    bl = body.split('\n')
    k = next((i for i, l in enumerate(bl) if re.search(r':=\s*(by)?\s*$', l) or re.search(r':= by\b', l)), None)
    plen = len(bl) - k - 1 if k is not None else 0
    tac = sum(1 for l in bl[k+1:] if l.strip()) if k is not None else 0
    if plen > 20:
        rows.append((n, kind, plen, 'Proof sketch' in doc, 'sketch' in doc.lower()))
print(f'{"name":28} kind  lines  literal  any-sketch')
for r in rows: print(f'{r[0]:28} {r[1]:6} {r[2]:5}  {r[3]!s:7}  {r[4]}')
from collections import Counter
print('by kind (missing literal):', Counter(r[1] for r in rows if not r[3]), 'total missing', sum(1 for r in rows if not r[3]), 'of', len(rows))
print('missing literal but some "sketch" word:', [r[0] for r in rows if not r[3] and r[4]])
