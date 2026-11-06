"""renumber.py <worktree> <in.json> <out.json>: rewrite `…example@<line>` declaration names of an
unseal file into the stable `…example#<ordinal>` names of the current tools/declx.py."""
import json, re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import declx
WT, IN, OUT = sys.argv[1:4]
d = json.load(open(IN))
for path, ents in d.items():
    src = open(os.path.join(WT, path), encoding='utf-8').read()
    exts = declx.extents(src)
    for e in ents:
        m = re.match(r'^(.*)\.example@(\d+)$', e['decl'])
        if m:
            ln = int(m.group(2))
            hit = [x for x in exts if x['start'] == ln and x['kind'] == 'example']
            assert hit, e['decl']
            e['decl'] = hit[0]['name']
json.dump(d, open(OUT, 'w'), indent=1)
print('ok')
