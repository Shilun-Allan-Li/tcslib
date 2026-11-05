"""Scan the new docstrings and comments for campaign vocabulary; check proof-sketch coverage.
usage: newtext.py <head.lean> <first new line> <last new line>"""
import re, sys
path, a, b = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
L = open(path, encoding='utf-8').read().split('\n')
# collect comment/docstring text with line numbers, over the whole file but report by region
def comments(lines):
    out = []; depth = 0
    for i, l in enumerate(lines, 1):
        j = 0; buf = ''
        while j < len(l):
            if l.startswith('/-', j): depth += 1; j += 2; continue
            if l.startswith('-/', j) and depth > 0: depth -= 1; j += 2; continue
            if depth > 0: buf += l[j]; j += 1; continue
            if l.startswith('--', j): buf += l[j+2:]; break
            j += 1
        if buf.strip(): out.append((i, buf))
    return out
C = [(i, t) for i, t in comments(L) if a <= i <= b or i in (73, ) or 8397 <= i <= 8457]
PAT = {
 'checkpoint': r'\bcheckpoints?\b|\bcp ?\d\b', 'gate/finding': r'\bgates?\b|\bfindings?\b|\bF\d+\b',
 'date': r'\b20\d\d-\d\d-\d\d\b', 'audits path': r'audits/', 'the brief': r'\bthe brief\b|\bbrief\b',
 'review': r'\bthe review\b|\breview\b', 'pinned': r'\bpinned\b', 'authorized': r'\bauthori[sz]ed\b',
 'route probe': r'route probe|\bprobe\b', 'published': r'\bpublished\b',
 'labels': r'\bE-[A-Z]+\b|\bC1-E\b|\bC1\b|\bP3\.3\b|\bBL-1\b|\bRO-1\b|\bNB-1\b|\bQF-1\b|\bRC-\d\b|\bLS-\d\b|\bFH-1\b',
 'rule N': r'\brule \d+\b', 'ledger/screen': r'\bledger\b|\bscreen\b', 'fill/landing': r'\bfill\b|\blanding\b|\bmaintainer\b|\bworker\b',
 'promotion': r'\bpromot', 'design §': r'design §|§\d', 'leaf label': r'\b[L]\d\b|\bleaf L', 'ruled': r'\bruled\b|\bruling\b',
}
hits = {k: [] for k in PAT}
for i, t in C:
    for k, p in PAT.items():
        if re.search(p, t, re.I if k in ('the brief','review','pinned','authorized','route probe','published','ledger/screen','fill/landing','promotion','ruled','checkpoint') else 0):
            hits[k].append((i, t.strip()[:140]))
for k, v in hits.items():
    print(f'{k}: {len(v)}')
    for i, t in v: print(f'   {i}: {t}')
# proof sketch coverage: for each declaration in [a, b] whose proof spans > 20 lines, does its docstring contain **Proof sketch.**?
DECL = re.compile(r'^(private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance|structure|inductive) (\S+)')
starts = [i for i in range(a, b + 1) if DECL.match(L[i-1])]
starts.append(b + 1)
print('\nproof-sketch coverage (declarations whose text after the header line exceeds 20 lines):')
miss = 0; cnt = 0
for k, s in enumerate(starts[:-1]):
    e = starts[k+1] - 1
    # back up over the next declaration's docstring
    j = e
    while j > s and not L[j-1].strip() == '': j -= 1
    # find this decl's docstring above
    d = s - 1
    doc = ''
    if L[d-1].rstrip().endswith('-/'):
        q = d
        while q > 0 and not L[q-1].lstrip().startswith('/--'): q -= 1
        doc = '\n'.join(L[q-1:d])
    n = j - s
    if n > 20:
        cnt += 1
        ok = '**Proof sketch.**' in doc
        if not ok: miss += 1
        print(f'  {"ok  " if ok else "MISS"} {DECL.match(L[s-1]).group(3)} ({n} lines)')
print(f'over 20 lines: {cnt}; without a proof sketch: {miss}')
# docstring presence
nodoc = [DECL.match(L[s-1]).group(3) for s in starts[:-1] if not L[s-2].rstrip().endswith('-/')]
print('declarations without a docstring:', nodoc)
