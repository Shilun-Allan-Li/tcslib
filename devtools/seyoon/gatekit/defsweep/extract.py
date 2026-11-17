"""Gate 144 G144-01 (reused at gate 145): collect the identifiers passed explicitly to simp/rw/unfold-style tactics in the
changed declarations of each owner. Usage: extract.py <SOURCE.json> <src-root> <outdir>"""
import json, re, sys
from pathlib import Path
src = json.loads(Path(sys.argv[1]).read_text()); root = Path(sys.argv[2]); out = Path(sys.argv[3])
import os as _os
decl = (Path(_os.environ['TCSLIB_REPO'])/'devtools/seyoon/declfreeze.py').read_text()
ns = {}; exec(compile(decl.split('a = chunks(open(sys.argv[1]).read())')[0], 'declfreeze', 'exec'), ns)
TAC = re.compile(r'\b(simp_all|simp|simpa|dsimp|simp_rw|rw|rwa|erw|nth_rw|nth_rewrite|unfold|delta|norm_num|field_simp|split_ifs)\b[^\[\n]*\[([^\]]*)\]|\b(unfold|delta)\b([^\n]*)')
IDENT = re.compile(r"(?<![\w.'])((?:[A-Za-z_][\w']*\.)*[A-Za-z_][\w']*)")
report = {}
for row in src['owner_source']:
    path = row['path']; names = set(row['total_changed_or_added_from_campaign'])
    text = (root / path).read_text()
    idents = {}
    for n, priv, txt in ns['chunks'](text):
        if n not in names: continue
        for m in TAC.finditer(txt):
            args = m.group(2) if m.group(2) is not None else m.group(4)
            for a in IDENT.findall(args or ''):
                if a in ('_', 'at', 'only', 'by', 'fun', 'show', 'from', 'with', 'this', 'true', 'false'): continue
                idents.setdefault(a, set()).add(n)
    report[path] = {k: sorted(v) for k, v in sorted(idents.items())}
    opens = re.findall(r'^open [^\n]*', text, re.M)
    nss = re.findall(r'^namespace (\S+)', text, re.M)
    mod = path[:-5].replace('/', '.')
    chk = out / ('Check_' + Path(path).stem + '.lean')
    chk.write_text('import ' + mod + '\nimport TCSlib.Scratch.Kinds\n' + '\n'.join(f'namespace {s}' for s in nss[:1]) + '\n'
                   + '\n'.join(opens) + '\n#kinds ' + ' '.join('.'.join('«' + c + '»' for c in a.split('.')) for a in sorted(idents)) + '\n')
(out / 'idents.json').write_text(json.dumps(report, indent=1))
print({p: len(v) for p, v in report.items()})
