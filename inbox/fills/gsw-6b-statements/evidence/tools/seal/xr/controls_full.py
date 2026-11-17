r"""controls_full.py <collector-lines.log> <worktree> <spec.json> <outdir> [<tree>]
(gsw-6b-statements sub-agent `seal`, new; combines gsw-6a-statements tools/controls.py (a separate consumer file that
imports the owner and reads one of its new definitions) with gsw-6a-fills tools/lead/liveness.py (pretest unsealed,
then the full seal harness, strict A and coe-A, exactly one error expected for the body read)).

Paired Rule 10 controls, one pair per owner. spec: list of {owner, def, stmt, neg, pos[, open, ns]}:
  `example <stmt> := <neg>` reads the owner's new definition <def> through its body (rfl / Iff.rfl / unfold),
  `example <stmt> := <pos>` reads it through its published reader. Optional `ns` (a namespace the examples are
  placed in) and `open` (namespaces opened). The control file is ANOTHER file: `import <owner>` + the example.
For each owner O (tag = O without its first component, dots -> _) it writes under <worktree>/evidence-scratch/rule10/
ctl-<parent of outdir>-<basename outdir>/ and copies to <outdir>/src/:
  Ctl_<tag>_neg_unsealed.lean      no harness; must elaborate with 0 errors (PRETEST; the sealed runs only start
                                   when every pretest passes);
  Ctl<V>_<tag>_neg_sealed.lean     V in {A, coeA}: the whole-file seal harness of build_seals.instrument (with the
                                   request_payload_adapter: component checks, instance mask, EOF verification)
                                   installed after the import, requesting every eligible TCSlib definition of the
                                   control's import closure = CLOSURE(O) + O itself (so <def> is requested), with the
                                   exclusions of mkseals_ab.py (A: PolyExpr.eval) resp. mkseals_coe.py (coe-A:
                                   + FinDist.instCoeFunForallReal); must fail with EXACTLY ONE error, located inside
                                   the example, and the install/EOF records must show requested = verified;
  Ctl<V>_<tag>_pos_sealed.lean     same harness + the reader example; must pass (rc 0, 0 errors, records complete).
Every file runs as `lean -DmaxErrors=0` through runner_pool.py (shared pool, no -o). Writes <outdir>/summary.tsv
and <outdir>/records/*.json (requests, line maps), and prints ALL_OK."""
import sys, os, json, re, subprocess, importlib.util, hashlib
from pathlib import Path
log, wt, specf, outdir = sys.argv[1:5]
tree = sys.argv[5] if len(sys.argv) > 5 else '/home/user/oleans/seal'
T = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path); m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m); return m
bs = load(T / 'build_seals.py', 'levin_bs'); controls = load(T / 'build_controls.py', 'levin_controls')
adapter = load(T / 'request_payload_adapter.py', 'levin_adapter'); adapter.configure_builders(bs, controls)
cat, closures = {}, {}
for line in open(log, encoding='utf-8'):
    if line.startswith('CAT '):
        r = json.loads(line[4:]); cat[r['name']['display']] = r
    elif line.startswith('CLOSURE '):
        r = json.loads(line[8:]); closures[r['module']] = r['closure']
EXCL = {'A': {'Complexity.PolyExpr.eval'},
        'coeA': {'Complexity.PolyExpr.eval', 'TCSlib.InformationTheory.FinDist.instCoeFunForallReal'}}
spec = json.load(open(specf))
outdir = os.path.abspath(outdir); name = os.path.basename(os.path.dirname(outdir)) + '-' + os.path.basename(outdir)
sub = f'evidence-scratch/rule10/ctl-{name}'
os.makedirs(os.path.join(wt, sub), exist_ok=True)
for d in ('src', 'records'): os.makedirs(os.path.join(outdir, d), exist_ok=True)
sha = lambda b: hashlib.sha256(b).hexdigest()
def tag(o): return o.split('.', 1)[1].replace('.', '_')
def source(s, kind):
    txt = f'import {s["owner"]}\nset_option autoImplicit false\n'
    if s.get('ns'): txt += f'namespace {s["ns"]}\n'
    for o in s.get('open', []): txt += f'open {o}\n'
    txt += (f'-- Rule 10 control ({kind}): reads `{s["def"]}` of {s["owner"]} from another file '
            + ('through its body' if kind == 'neg' else 'through its published reader') + '\n')
    ex_line = txt.count('\n') + 1
    txt += f'example {s["stmt"]} :=\n  {s[kind]}\n'
    ex_end = txt.count('\n')
    if s.get('ns'): txt += f'end {s["ns"]}\n'
    return txt.encode(), ex_line, ex_end
def write(mod, raw):
    (Path(wt) / (mod + '.lean')).write_bytes(raw); (Path(outdir) / 'src' / (os.path.basename(mod) + '.lean')).write_bytes(raw)
def run(mods, rd):
    order = os.path.join(outdir, os.path.basename(rd) + '-order.txt'); open(order, 'w').write('\n'.join(mods) + '\n')
    subprocess.run(['rm', '-rf', rd]); subprocess.run(['python3', '-I', str(T / 'runner_pool.py'), wt, order, tree, rd, '3'], check=True)
    res = {}
    for l in open(os.path.join(rd, 'results.jsonl')):
        x = json.loads(l)
        if 'module' in x: res[x['module']] = x
    return res
recs = {}
unsealed = []
for s in spec:
    t = tag(s['owner']); raw, a, b = source(s, 'neg'); m = f'{sub}/Ctl_{t}_neg_unsealed'
    write(m, raw); unsealed.append(m); recs[m] = dict(kind='neg_unsealed', owner=s['owner'], def_=s['def'], expect=0, ex=(a, b), requested=None)
sealed = []
for s in spec:
    t = tag(s['owner']); clo = set(closures[s['owner']]) | {s['owner']}
    for V in ('A', 'coeA'):
        def eligible(r): return r['kind'] == 'def' and (r['matcher'] or r['status'] != 'reducible') and r['name']['display'] not in EXCL[V]
        crow = sorted((r for r in cat.values() if r['home']['display'] in clo and eligible(r)), key=lambda r: r['name']['display'])
        assert s['def'] in {r['name']['display'] for r in crow}, ('control definition not requested', V, s['def'])
        rows = [dict(spelling=r['name']['display'], home=r['home']['display'], name_components=r['name']['components'],
                     home_components=r['home']['components'], instance=r['instance'], matcher=r['matcher'],
                     abbrev=r['abbrev'], collector_reducibility=r['status']) for r in crow]
        for kind in ('neg', 'pos'):
            raw, a, b = source(s, kind); label = f'Ctl{V}_{t}_{kind}_sealed'; m = f'{sub}/{label}'
            probe, ins, lmap = bs.instrument(raw, bs.header(raw), label, rows)
            write(m, probe); sealed.append(m)
            p2 = {d['source_line']: d['probe_line'] for d in lmap}
            rec = dict(kind=f'{kind}_sealed', variant=V, owner=s['owner'], def_=s['def'], expect=1 if kind == 'neg' else 0,
                       ex=(p2[a], p2[b]), requested=len(rows), label=label, source_sha256=sha(raw), probe_sha256=sha(probe),
                       insertions=ins, source_to_probe_lines=lmap, requests=[r['spelling'] for r in rows])
            recs[m] = rec
for m, r in recs.items():
    json.dump(r, open(os.path.join(outdir, 'records', os.path.basename(m) + '.json'), 'w'), indent=1)
r0 = run(unsealed, os.path.join(outdir, 'run-unsealed'))
pre_ok = all(r0[m]['rc'] == 0 and r0[m]['errors'] == 0 for m in unsealed)
r1 = run(sealed, os.path.join(outdir, 'run-sealed')) if pre_ok else {}
allres = dict(r0); allres.update(r1)
out = open(os.path.join(outdir, 'summary.tsv'), 'w')
out.write('control\towner\tdefinition\tharness\trc\terrors\texpected_errors\terror_in_example\tinstall\teof\tverdict\terror_lines\n')
ok_all = pre_ok
for m in unsealed + sealed:
    r = recs[m]; x = allres.get(m)
    if x is None:
        out.write(f'{os.path.basename(m)}\t{r["owner"]}\t{r["def_"]}\t-\tNOT-RUN\n'); ok_all = False; continue
    txt = open(os.path.join(outdir, 'run-unsealed' if m in unsealed else 'run-sealed', 'mods', m.replace('/', '_') + '.log'),
               encoding='utf-8', errors='replace').read()
    el = [(int(g.group(1)), g.group(0)) for g in re.finditer(r'^\S+\.lean:(\d+):\d+: error.*$', txt, re.M)]
    inex = all(r['ex'][0] <= e <= r['ex'][1] for e, _ in el)
    if r['requested'] is None:
        insr = eofr = '-'; rec_ok = True; harness = 'none'
    else:
        lab = re.escape(r['label']); harness = 'strict(A)' if r['variant'] == 'A' else 'coe(coe-A)'
        i = re.findall(r'G06-SEAL label=' + lab + r' requested=(\d+) .*?verified=(\d+)', txt)
        e = re.findall(r'G06-SEAL-END label=' + lab + r' requested=(\d+) verified=(\d+)', txt)
        insr = ';'.join('/'.join(p) for p in i); eofr = ';'.join('/'.join(p) for p in e)
        rec_ok = len(i) == 1 and len(e) == 1 and i[0] == (str(r['requested']),) * 2 and e[0] == (str(r['requested']),) * 2
    good = x['errors'] == r['expect'] and inex and rec_ok and (r['expect'] == 1 or x['rc'] == 0)
    ok_all &= good
    out.write('\t'.join(map(str, [os.path.basename(m), r['owner'], r['def_'], harness, x['rc'], x['errors'], r['expect'], int(inex),
                                  insr, eofr, 'OK' if good else 'UNEXPECTED', ' || '.join(l for _, l in el)])) + '\n')
out.write(f'# pretest_unsealed_ok={pre_ok} ALL_OK={ok_all}\n'); out.close()
print(open(os.path.join(outdir, 'summary.tsv')).read())
