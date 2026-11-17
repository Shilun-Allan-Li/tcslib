# ownercheck.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW, the brief's owner check (Checks, step 2). For each owner:
# the collector's stored constants (ROOT) reduced to source-level declarations (kind theorem/def/opaque/axiom/inductive;
# not internal, aux recursor, noConfusion, constructor, recursor, projection, matcher, or a generated equation/splitter/
# injectivity/sizeOf/ext lemma), against the pack's static scanner (derivation/leanindex.py decls, at the base, from git
# objects) and owners.txt's `decls` column. Differences are categorized: anonymous instances (static '<anon>'), instances
# with no static counterpart (deriving / anonymous), generated theorems (`simps`, `ext`), structure/inductive types counted
# by both, and UNEXPLAINED names (static name not found in the collector, or a collector def/theorem with no static name).
# Usage: python3 -I ownercheck.py <evidence> <pack> <repo> <base> <out.tsv> <out-names.tsv>
import sys, json, re, os, collections, importlib.util
ev, pack, repo, base, outp, outn = sys.argv[1:7]
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('leanindex', os.path.join(pack, 'derivation/leanindex.py'))
li = importlib.util.module_from_spec(spec); spec.loader.exec_module(li)
import subprocess
GEN = re.compile(r'\.(eq_\d+|eq_def|eq_unfold|splitter|inj|injEq|sizeOf_spec|ext|ext_iff|mk\.inj|mk\.injEq|recOn|casesOn|below|brecOn|binductionOn|ibelow|noConfusionType|noConfusion|ctorIdx|toCtorIdx)$')
rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(ev, 'collect/batches.tsv'))][1:]
own = {}
for l in open(os.path.join(pack, 'owners.txt'), encoding='utf-8').read().split('# FACADES')[0].split('\n'):
    if l and not l.startswith('#') and not l.startswith('path\t'):
        f = l.split('\t'); own[f[0]] = f
res, names_out = [], []
for b in sorted({r[0] for r in rows}):
    lp = os.path.join(ev, 'collect', b, 'runs/mods', f'DW10Probe_Collect_{b}.log')
    roots = collections.defaultdict(list); stored = {}
    for l in open(lp, encoding='utf-8'):
        if l.startswith('ROOT '): r = json.loads(l[5:]); roots[r['module']].append(r)
        elif l.startswith('MODULE '): m, c = l[7:].strip().split(': stored '); stored[m] = int(c)
    for bb, module, path, *_ in rows:
        if bb != b: continue
        src = subprocess.run(['git', '-C', repo, 'show', f'{base}:{path}'], capture_output=True, text=True).stdout
        st = li.decls(src)
        sname = [d[0] for d in st]
        coll = []
        for r in roots[module]:
            n = r['name']['display']; fl = r.get('flags', {})
            if r['kind'] in ('constructor', 'recursor', 'quotient'): continue
            if fl.get('internal') or fl.get('aux_recursor') or fl.get('no_confusion') or fl.get('projection') or fl.get('matcher'): continue
            u = re.sub(r'^_private\.[^ ]*?\.0\.', '', n)
            if GEN.search(u): continue
            coll.append((u, r['kind'], fl.get('instance', False)))
        cset = {c[0] for c in coll}
        anon = sum(1 for s in sname if s.endswith('<anon>'))
        missing = [s for s in sname if not s.endswith('<anon>') and s not in cset and not any(c.endswith('.' + s) for c in cset)]
        extra = [c for c in coll if c[0] not in set(sname) and not any(c[0].endswith('.' + s) or s.endswith('.' + c[0]) for s in sname if not s.endswith('<anon>'))]
        inst_extra = [c for c in extra if c[2]]
        thm_extra = [c for c in extra if not c[2] and c[1] == 'theorem']
        other_extra = [c for c in extra if not c[2] and c[1] != 'theorem']
        unexpl = len(missing) + max(0, len(inst_extra) - anon) + len(other_extra)
        res.append([path, own[path][1], own[path][2], own[path][5], str(len(st)), str(len(coll)), str(stored.get(module, 0)), str(anon),
                    str(len(inst_extra)), str(len(thm_extra)), str(len(other_extra)), str(len(missing)), str(unexpl), b])
        for s in missing: names_out.append([path, 'STATIC_NOT_IN_COLLECTOR', s, '-'])
        for c in extra: names_out.append([path, 'COLLECTOR_NOT_IN_STATIC', c[0], c[1] + (' instance' if c[2] else '')])
H = ['path', 'tier', 'agent', 'owners_txt_decls', 'static_decls', 'collector_decls', 'stored_constants', 'static_anon_instances',
     'extra_instances', 'extra_theorems', 'extra_other', 'static_missing', 'unexplained', 'batch']
open(outp, 'w').write('\t'.join(H) + '\n' + ''.join('\t'.join(x) + '\n' for x in res))
open(outn, 'w').write('path\tcategory\tname\tkind\n' + ''.join('\t'.join(x) + '\n' for x in names_out))
print('owners', len(res), 'with unexplained', sum(1 for x in res if x[12] != '0'), 'owners.txt != static', sum(1 for x in res if x[3] != x[4]))
