"""liveness.py <worktree> <probe-dir> <spec.json> <outdir> (gsw-6a-fills, new; check 5 controls): one liveness pair
per owner, in the owner's own context. <probe-dir> holds the owner's seal probes per variant (<probe-dir>/<V>/Seal<V>_*.lean,
as made by seal_pipeline.sh). For each spec row {owner, def, stmt, neg, pos} it writes, under
<worktree>/evidence/rule10/live/:
  Live_<O>_neg_unsealed.lean  = the owner file at HEAD (git show) + `example <stmt> := <neg>` (reads the foreign
                                definition <def> through its body by rfl/Iff.rfl): must pass (0 errors), pretested first;
  Live_<O>_neg_<V>.lean       = the owner's full seal probe of variant V (A = strict, coeA = coe) + the same example:
                                must fail with exactly one error;
  Live_<O>_pos_<V>.lean       = the seal probe + `example <stmt> := <pos>` (the published reader): must pass.
Each file runs as `lean -DmaxErrors=0` (runner_pool.py, shared pool, no -o). Writes <outdir>/summary.txt with
ALL_OK per variant."""
import sys, json, os, re, glob, subprocess
wt, pdir, specf, outdir = sys.argv[1:5]
spec = json.load(open(specf))
ld = os.path.join(wt, 'evidence/rule10/live'); os.makedirs(ld, exist_ok=True); os.makedirs(outdir, exist_ok=True)
def tag(o): return o.split('.', 2)[2].replace('.', '_')
def run(mods, rd):
    order = os.path.join(outdir, os.path.basename(rd) + '-order.txt')
    open(order, 'w').write('\n'.join(mods) + '\n')
    subprocess.run(['python3', '-I', '/home/user/w6/tools/stmt/xr/runner_pool.py', wt, order,
                    os.environ['TCSLIB_OLEANS'], rd], check=True)
    res = {}
    for l in open(os.path.join(rd, 'results.jsonl')):
        x = json.loads(l)
        if 'module' in x: res[x['module']] = x
    return res
rows = []
unsealed = []
for s in spec:
    t = tag(s['owner']); path = s['owner'].replace('.', '/') + '.lean'
    src = subprocess.run(['git', '-C', wt, 'show', f'HEAD:{path}'], capture_output=True, check=True).stdout.decode()
    m = f'Live_{t}_neg_unsealed'
    open(os.path.join(ld, m + '.lean'), 'w').write(src + f'\n-- liveness control: reads `{s["def"]}` through its body\nexample {s["stmt"]} :=\n  {s["neg"]}\n')
    unsealed.append(f'evidence/rule10/live/{m}')
r0 = run(unsealed, os.path.join(outdir, 'run-unsealed'))
sealed = []
for s in spec:
    t = tag(s['owner'])
    for V in ['A', 'coeA']:
        probe = [p for p in glob.glob(os.path.join(pdir, V, f'Seal{V}_*.lean')) if p.endswith(t + '.lean')]
        assert len(probe) == 1, (V, t, probe)
        base = open(probe[0]).read()
        for kind in ['neg', 'pos']:
            m = f'Live_{t}_{kind}_{V}'
            open(os.path.join(ld, m + '.lean'), 'w').write(base + f'\n-- liveness control ({kind}, seal {V}): reads `{s["def"]}` ' + ('through its body' if kind == 'neg' else 'through its reader') + f'\nexample {s["stmt"]} :=\n  {s[kind]}\n')
            sealed.append(f'evidence/rule10/live/{m}')
pre_ok = all(r0[m]['rc'] == 0 and r0[m]['errors'] == 0 for m in unsealed)
r1 = run(sealed, os.path.join(outdir, 'run-sealed')) if pre_ok else {}
summ = open(os.path.join(outdir, 'summary.txt'), 'w')
ok = {'A': True, 'coeA': True}
for s in spec:
    t = tag(s['owner']); m = f'evidence/rule10/live/Live_{t}_neg_unsealed'
    line = f'{t}\tdef={s["def"]}\tneg_unsealed errors={r0[m]["errors"]} rc={r0[m]["rc"]} (want 0)'
    for V in ['A', 'coeA']:
        n, p = r1.get(f'evidence/rule10/live/Live_{t}_neg_{V}'), r1.get(f'evidence/rule10/live/Live_{t}_pos_{V}')
        good = n is not None and p is not None and n['errors'] == 1 and p['errors'] == 0 and p['rc'] == 0
        ok[V] &= good
        line += f'\t{V}: neg errors={n and n["errors"]} (want 1) pos errors={p and p["errors"]} (want 0) {"OK" if good else "BAD"}'
    print(line); summ.write(line + '\n')
for V in ok:
    print(f'{V} ALL_OK {ok[V] and pre_ok}'); summ.write(f'{V} ALL_OK {ok[V] and pre_ok}\n')
