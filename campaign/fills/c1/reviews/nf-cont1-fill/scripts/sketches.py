# sketches.py <file> <names.txt>: per new declaration: docstring?, proof lines, Proof sketch?
import re, sys
f, nf = sys.argv[1:3]
L = open(f, encoding='utf-8').read().split('\n')
names = [l.strip() for l in open(nf) if l.strip()] + ['exists_codeNDTM_accepts_linear']
DECL = re.compile(r'^(private )?(theorem|lemma|def|abbrev|instance|inductive|structure)\s+(\S+)')
starts = []
for i, l in enumerate(L):
    m = DECL.match(l)
    if m: starts.append((i, m.group(3)))
bound = [i for i, l in enumerate(L) if re.match(r'^(/--|/-!|end |section |namespace |attribute |example|-- )', l)]
out = []
for idx, (i, n) in enumerate(starts):
    if n not in names: continue
    # docstring: the nearest '/--' block ending right above
    j = i - 1
    doc = ''
    if j >= 0 and L[j].rstrip().endswith('-/'):
        k = j
        while k >= 0 and not L[k].startswith('/--'): k -= 1
        doc = '\n'.join(L[k:j + 1])
    # end of declaration: next decl start or boundary after i
    nxt = min([s for s, _ in starts if s > i] + [b for b in bound if b > i] + [len(L)])
    body = L[i:nxt]
    while body and body[-1].strip() == '': body.pop()
    # proof lines: from the line containing ':= by' (or ':=' for terms) to end
    pl = 0
    for k, l in enumerate(body):
        if ':= by' in l or l.rstrip().endswith(':=') or re.search(r':=\s*$', l) or l.strip().startswith('| '):
            pl = len(body) - k - 1 if ':= by' in l or l.rstrip().endswith(':=') else len(body) - k
            break
    out.append((n, i + 1, bool(doc), len(body), pl, '**Proof sketch.**' in doc, doc))
print(f'{"name":28s} line  doc  declLines proofLines sketch')
for n, ln, d, dl, pl, sk, _ in out:
    flag = ' <-- over 20 proof lines without a sketch' if pl > 20 and not sk else ''
    print(f'{n:28s} {ln:5d} {str(d):5s} {dl:5d} {pl:6d}     {sk}{flag}')
print('declarations:', len(out), '| with docstring:', sum(o[2] for o in out), '| with sketch:', sum(o[5] for o in out),
      '| proofs over 20 lines:', sum(o[4] > 20 for o in out), '| of those without sketch:', sum(o[4] > 20 and not o[5] for o in out))
