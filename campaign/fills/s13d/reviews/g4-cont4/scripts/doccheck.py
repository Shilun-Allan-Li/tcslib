import sys, json, re
# usage: doccheck.py <declfreeze.py> <head file> <newchanged.json>
src_df = open(sys.argv[1], encoding='utf-8').read()
ns = {}; exec(compile(src_df.split("a = chunks(open(sys.argv[1]).read())")[0], 'df', 'exec'), ns)
chunks = ns['chunks']
text = open(sys.argv[2], encoding='utf-8').read()
lines = text.split('\n')
nc = json.load(open(sys.argv[3]))
targets = set(nc['new']) | set(nc['changed'])
B = {n: (p, t) for n, p, t in chunks(text)}
nodoc = []; long_nosketch = []; long = 0
LABELS = re.compile(r'\b(G4|G5|G2|cont[0-9]|continuation|checkpoint|zip|ground rule|escalat\w*|brief|gate\s*\d*|finding|F[0-9]\b|E-RES|cont1-E1|R3|MIG-[0-9]|§13d|campaign/|audits/|REPORT|worker|maintainer|round [0-9])', re.I)
DATE = re.compile(r'20[0-9]{2}-[01][0-9]-[0-3][0-9]')
labels = []
for n in sorted(targets, key=lambda n: text.find(B[n][1])):
    t = B[n][1]
    has_doc = t.startswith('/--')
    if not has_doc: nodoc.append(n)
    doc = t.split('-/', 1)[0] if has_doc else ''
    body = t.split('-/', 1)[1] if has_doc else t
    # proof length: lines after the first line containing ':= by' or ':=' at statement end
    bl = body.split('\n')
    k = next((i for i, l in enumerate(bl) if re.search(r':=\s*(by)?\s*$', l) or re.search(r':= by\b', l)), None)
    plen = len(bl) - k - 1 if k is not None else 0
    if plen > 20:
        long += 1
        if 'Proof sketch' not in doc: long_nosketch.append((n, plen))
    for m in LABELS.finditer(doc): labels.append((n, m.group(0)))
    for m in DATE.finditer(doc): labels.append((n, 'DATE ' + m.group(0)))
print('new/changed declarations', len(targets))
print('without a docstring:', nodoc)
print('proofs over 20 lines:', long, '; without a literal "Proof sketch":', len(long_nosketch))
for n, p in long_nosketch: print('   ', n, p)
print('label/date hits in docstrings of new/changed declarations:', len(labels))
for n, l in labels: print('   ', n, ':', l)
w = [(i + 1, len(l)) for i, l in enumerate(lines) if len(l) > 100]
print('lines over 100 chars:', w[:20], 'max width', max(len(l) for l in lines))
print('trailing whitespace lines:', [i + 1 for i, l in enumerate(lines) if l != l.rstrip()][:20])
print('tabs:', [i + 1 for i, l in enumerate(lines) if '\t' in l][:20])
dbl = [i + 1 for i in range(len(lines) - 1) if lines[i].strip() == '' and lines[i + 1].strip() == '']
print('double blank lines:', dbl[:40], len(dbl))
