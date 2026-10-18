import json, re, sys, os, glob, collections
root = sys.argv[1]  # wt root
names = json.load(open(sys.argv[2]))  # list of [homefile, line, name]
out = sys.argv[3]
def strip(src):
    out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth:
            out.append('\n' if src[i] == '\n' else ' '); i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        out.append(src[i]); i += 1
    return ''.join(out)
files = sorted(glob.glob(root + '/TCSlib/**/*.lean', recursive=True)) + [root + '/TCSlib.lean']
code = {}; raw = {}
for f in files:
    s = open(f, encoding='utf-8').read(); raw[f] = s.split('\n'); code[f] = strip(s).split('\n')
res = []
for home, line, name in names:
    pat = re.compile(r'(?<![\w.\'])(?:[\w\']+\.)*' + re.escape(name) + r'(?![\w\'])')
    ext = collections.Counter(); internal = 0; doc = collections.Counter()
    for f in files:
        rel = f[len(root) + 1:]
        for i, (c, r) in enumerate(zip(code[f], raw[f])):
            nc = len(pat.findall(c))
            if rel == home and i + 1 == line: nc -= 1  # the declaration itself
            nd = len(pat.findall(r)) - len(pat.findall(c))
            if nc > 0:
                if rel == home: internal += nc
                else: ext[rel] += nc
            if nd > 0 and rel != home: doc[rel] += nd
    res.append(dict(home=home, line=line, name=name, internal=internal, ext_files=len(ext), ext_cites=sum(ext.values()), ext=dict(ext), doc_files=len(doc), doc=sum(doc.values())))
json.dump(res, open(out, 'w'), indent=0)
for r in res:
    print(f"{r['home'].split('/')[-1]}:{r['line']} {r['name']}: internal {r['internal']}, external {r['ext_cites']} in {r['ext_files']} files; doc mentions elsewhere {r['doc']} in {r['doc_files']}")
