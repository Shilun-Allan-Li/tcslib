"""citecheck6b.py <worktree> <file>... (gsw-6b-statements, new): every bracketed citation
`[TAG, …]` in the given Lean files; each anchor `pNNN-bNNN` inside it must exist as
`<a id="<prefix>pNNN-bNNN">` in that tag's ingest under blueprint/src/references/. Tags allowed:
BV14, BV11, AP14, GSW13, Pei16, Bar89 (and the pre-existing Wu24, AB09 if present); `Gen09` must
not occur anywhere. Prints every citation with its anchors' status and a summary."""
import sys, re, os
wt, files = sys.argv[1], sys.argv[2:]
ING = {'Bar89': ('barrington-1989-bounded-width-bp', 'pdf-06fd3eeccecf-'),
       'BV14': ('brakerski-vaikuntanathan-2014-fhe', 'pdf-eab2d1667a8e-'),
       'BV11': ('brakerski-vaikuntanathan-2011-fhe', 'pdf-d3e95f9b9e01-'),
       'AP14': ('alperin-sheriff-peikert-2014-bootstrapping', 'pdf-cecd346d2e87-'),
       'GSW13': ('gentry-sahai-waters-2013-fhe', 'pdf-8edb94cfd852-'),
       'Pei16': ('peikert2016-lattice-survey', 'pdf-1a9802b66031-')}
ids = {t: set(re.findall(r'<a id="([^"]+)"', open(os.path.join(wt, 'blueprint/src/references', k + '.md'), encoding='utf8').read())) for t, (k, _) in ING.items()}
bad = n = nan = 0
for f in files:
    s = open(os.path.join(wt, f), encoding='utf8').read()
    if 'Gen09' in s: print('GEN09', f); bad += 1
    for m in re.finditer(r'\[([A-Z][A-Za-z]*\d\d)\b([^\]]*)\]', s.replace('\n', ' ')):
        tag, body = m.group(1), m.group(2); n += 1
        # a bracket may carry several `TAG, loc` groups separated by `;`
        for part in re.split(r';\s*', tag + body):
            t = re.match(r'([A-Z][A-Za-z]*\d\d)\b', part)
            if not t: continue
            t = t.group(1); anchors = re.findall(r'p\d{3}-b\d{3}', part)
            if t not in ING:
                print(f'{"PREEXISTING-TAG" if t in ("Wu24","AB09") else "UNKNOWN-TAG"}\t{f}\t{part[:80]}')
                bad += t not in ('Wu24', 'AB09'); continue
            for a in anchors:
                nan += 1
                ok = ING[t][1] + a in ids[t]
                if not ok: bad += 1
                print(f'{"OK" if ok else "MISSING"}\t{f}\t{t}\t{a}')
print(f'# citations {n}, anchors checked {nan}, problems {bad}')
