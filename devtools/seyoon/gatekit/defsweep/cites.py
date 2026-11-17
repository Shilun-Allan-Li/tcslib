"""Gate 149 (G147-02 procedure): list every identifier in the changed or added declarations at head
and in the same declarations at base, for a Lean #kinds pass that resolves each to its home module.
Usage: cites.py <SOURCE.json> <head-root> <base-root> <outdir>"""
import json, re, sys
from pathlib import Path
src = json.loads(Path(sys.argv[1]).read_text()); head, base, out = map(Path, sys.argv[2:5])
import os as _os
decl = (Path(_os.environ['TCSLIB_REPO'])/'devtools/seyoon/declfreeze.py').read_text()
ns = {}; exec(compile(decl.split('a = chunks(open(sys.argv[1]).read())')[0], 'declfreeze', 'exec'), ns)
IDENT = re.compile(r"(?<![\w.'])((?:[A-Za-z_][\w']*\.)*[A-Za-z_][\w']*)")
KW = set('_ at only by fun show from with this true false have let in if then else match do return '
         'theorem lemma def abbrev structure where private noncomputable protected instance class '
         'namespace end open section variable intro exact refine obtain rcases rintro simp simpa rw omega '
         'calc and or not Type Prop Sort forall exists'.split())
def strip(t):
    t = re.sub(r'/-.*?-/', ' ', t, flags=re.S); return re.sub(r'--[^\n]*', ' ', t)
report = {}
for row in src['owner_source']:
    path = row['path']; names = set(row['total_changed_or_added_from_campaign'])
    sides = {}
    for side, root in (('head', head), ('base', base)):
        p = root / path; text = p.read_text() if p.exists() else ''
        ids = set()
        for n, priv, txt in ns['chunks'](text):
            if n in names: ids |= {a for a in IDENT.findall(strip(txt)) if a not in KW and not a[0].isdigit()}
        sides[side] = sorted(ids)
    report[path] = sides
    text = (head / path).read_text(); mod = path[:-5].replace('/', '.')
    opens = '\n'.join(re.findall(r'^open [^\n]*', text, re.M))
    allids = ['.'.join('«' + c + '»' for c in a.split('.')) for a in sorted(set(sides['head']) | set(sides['base']))]
    blocks = [f'section\n{opens}\n#kinds ' + ' '.join(allids) + '\nend']
    for s in dict.fromkeys(re.findall(r'^namespace (\S+)', text, re.M)):
        blocks.append(f'namespace {s}\n{opens}\n#kinds ' + ' '.join(allids) + f'\nend {s}')
    (out / ('Cite_' + Path(path).stem + '.lean')).write_text(
        'import ' + mod + '\nimport TCSlib.Scratch.Kinds\n' + '\n'.join(blocks) + '\n')
(out / 'cite-idents.json').write_text(json.dumps(report, indent=1) + '\n')
print({p: (len(v['head']), len(v['base'])) for p, v in report.items()})
