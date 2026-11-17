# mkctl_dw10.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW controls generator for the brief's suite item 3 (one
# pair per owner that defines at least one TCSlib `def`, batched about 25 owners per harness, strict and coe). It keeps
# the archived harness of the earlier generators (build_seals.seal_command via request_payload_adapter, the
# controls-plan format that ctlcheck2.py reads, SEAL_CHUNK) and replaces their hand-written rows by rows derived from the
# collector:
#   target  - a definition of the owner (CAT: home = owner, kind def, not abbrev, not reducible, not an instance, matcher,
#             projection, private or internal name);
#   reader  - a theorem of the owner whose type refers to the target (collector ROOT own_type_refs), preferring the names
#             <target>_eq, _def, _apply, _iff, _eq_def, then <target>_*, then any other;
#   negative- `theorem … : type_of% @<reader> := by intros; rfl` (the reader's statement read by unfolding: must pass
#             unsealed, fail exactly once sealed);
#   positive- `theorem … : type_of% @<reader> := @<reader>` (the same fact through the published reader: passes sealed);
#   no reader: negative only, `type_of% @<target>.eq_def` by `intros; rfl` (the lemma is realized by a `#check` before
#             the seal is installed), recorded "no reader".
# Attempt 2 (2026-11-17): every control body carries `set_option maxHeartbeats 400000 in` (twice Lean's default):
# attempt 1's unsealed pretest harness CtlPre_b2g2 ran 48 min without finishing (an unsealed `rfl` candidate unfolding
# without bound); it was stopped by PID and its records are kept in controls/pretest-attempt1/. A candidate that cannot pass
# unsealed within the limit is not used. The harness command itself keeps maxHeartbeats 0.
# Phases:
#   pretest <evidence> <worktree> <probe-subdir> <outdir>
#       one UNSEALED harness per control batch with every candidate (up to 4 reader pairs and 1 eq_def negative per owner);
#   final <evidence> <worktree> <probe-subdir> <outdir> <pretest-rundir> [<exclude.json>]
#       picks per owner the first candidate whose negative and positive both passed the pretest (never by sealed outcome),
#       and writes per batch ControlU_<n> (unsealed), ControlS_<n> (strict-A request set) and ControlC_<n> (coe-A request
#       set: FinDist.instCoeFunForallReal also excluded), plus plan-strict.json and plan-coe.json (both list ControlU).
# Request set of a harness: every ordinary TCSlib definition (kind def, matcher or not reducible) whose home is one of the
# batch's owners or in one of their import closures, minus Complexity.PolyExpr.eval (A) [and the FinDist coercion (coe)].
import sys, json, re, os, collections, importlib.util
from pathlib import Path
phase = sys.argv[1]; ev, wt, sub, outdir = sys.argv[2:6]
sys.dont_write_bytecode = True
G = Path(ev) / 'tools/seal/review/archived-gate10-tools'
def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
bs = load(G / 'build_seals.py', 'levin_bs'); controls = load(G / 'build_controls.py', 'levin_controls')
adapter = load(G / 'request_payload_adapter.py', 'levin_adapter'); adapter.configure_builders(bs, controls)
CHUNK = int(os.environ.get('SEAL_CHUNK', '2000'))
_orig = bs.seal_command
def _chunked(label, rows, *, end):
    if len(rows) <= CHUNK: return _orig(label, rows, end=end)
    return b''.join(_orig(f'{label}_part{i // CHUNK + 1}', rows[i:i + CHUNK], end=end) for i in range(0, len(rows), CHUNK))
bs.seal_command = _chunked
PER = 25
COE = 'TCSlib.InformationTheory.FinDist.instCoeFunForallReal'
EVAL = 'Complexity.PolyExpr.eval'
rows = [l.rstrip('\n').split('\t') for l in open(Path(ev) / 'collect/batches.tsv')][1:]
batches = collections.OrderedDict()
for b, module, path, *_ in rows: batches.setdefault(b, []).append(module)
def collector(b):
    cat, roots, clo = {}, collections.defaultdict(list), {}
    for l in open(Path(ev) / 'collect' / b / 'runs/mods' / f'DW10Probe_Collect_{b}.log', encoding='utf-8'):
        if l.startswith('CAT '): r = json.loads(l[4:]); cat[r['name']['display']] = r
        elif l.startswith('ROOT '): r = json.loads(l[5:]); roots[r['module']].append(r)
        elif l.startswith('CLOSURE '): r = json.loads(l[8:]); clo[r['module']] = r['closure']
    return cat, roots, clo
BAD = re.compile(r'(^_private\.|\._|\.match_\d+$|\.proof_\d+$|\.eq_\d+$|\.eq_def$|\.eq_unfold$)')
SUF = ['_eq', '_def', '_apply', '_iff', '_eq_def']
def candidates(module, cat, roots):
    rs = roots[module]
    proj = {r['name']['display'] for r in rs if r.get('flags', {}).get('projection')}
    defs = [n for n, r in cat.items() if r['home']['display'] == module and r['kind'] == 'def' and not r['abbrev']
            and r['status'] != 'reducible' and not r['instance'] and not r['matcher'] and n not in proj and not BAD.search(n)
            and n not in (EVAL, COE)]
    thms = [r for r in rs if r['kind'] == 'theorem' and not BAD.search(r['name']['display'])]
    out = []
    for d in sorted(defs):
        rd = [t['name']['display'] for t in thms if d in {x['display'] for x in t.get('own_type_refs', [])}]
        def rank(t):
            for k, s in enumerate(SUF):
                if t == d + s: return (0, k, t)
            if t.startswith(d + '_'): return (1, len(t), t)
            return (2, len(t), t)
        for t in sorted(rd, key=rank)[:2]: out.append(dict(target=d, reader=t, rank=rank(t)[:2]))
    out.sort(key=lambda c: (c['rank'], c['target']))
    nr = [dict(target=d, reader=None, rank=(9, 0)) for d in sorted(defs)[:2]]
    return defs, out[:4] + nr
def bodies_for(k, j, c):
    tag = f'c{k}_{j}'
    if c['reader']:
        neg = f"set_option maxHeartbeats 400000 in\ntheorem {tag}_neg : type_of% @{c['reader']} := by intros; rfl\n"
        pos = f"set_option maxHeartbeats 400000 in\ntheorem {tag}_pos : type_of% @{c['reader']} := @{c['reader']}\n"
        return [(f'{tag}_neg', c['target'], True, neg), (f'{tag}_pos', c['target'], False, pos)]
    neg = f"set_option maxHeartbeats 400000 in\ntheorem {tag}_neg : type_of% @{c['target']}.eq_def := by intros; rfl\n"
    return [(f'{tag}_neg', c['target'], True, neg)]
def assemble(label, mods, req, bodies, sealed, eqdefs):
    src = ("import Lean\n" + ''.join(f'import {m}\n' for m in mods) + "\nset_option maxHeartbeats 0\nset_option autoImplicit false\n"
           "set_option relaxedAutoImplicit false\n\n").encode()
    src += ''.join(f'#check @{t}.eq_def\n' for t in eqdefs).encode() + b'\n'
    if sealed: src += bs.seal_command(label, req, end=False)
    src += b"namespace DW10Controls\n\n"
    expect = []
    for name, target, negative, body in bodies:
        start = src.count(b"\n") + 1
        src += body.encode() + b"\n"
        expect.append(dict(control=name, target=target, negative=negative, start_line=start, end_line=start + body.count('\n') - 1))
    src += b"end DW10Controls\n\n"
    if sealed: src += bs.seal_command(label, req, end=True)
    return src, expect
def reqrows(owners, cat, clo, coe):
    homes = set(owners) | {m for o in owners for m in clo[o]}
    ex = {EVAL} | ({COE} if coe else set())
    rs = sorted((r for r in cat.values() if r['home']['display'] in homes and r['kind'] == 'def' and (r['matcher'] or r['status'] != 'reducible')
                 and r['name']['display'] not in ex), key=lambda r: r['name']['display'])
    return [dict(spelling=r['name']['display'], home=r['home']['display'], name_components=r['name']['components'],
                 home_components=r['home']['components'], instance=r['instance'], matcher=r['matcher'], abbrev=r['abbrev'],
                 collector_reducibility=r['status']) for r in rs]
out = Path(outdir); out.mkdir(parents=True, exist_ok=True)
pdir = Path(wt) / sub; pdir.mkdir(parents=True, exist_ok=True)
groups = []  # (gid, batch, owners)
for b, mods in batches.items():
    for i in range(0, len(mods), PER): groups.append((f'{b}g{i // PER + 1}', b, mods[i:i + PER]))
if phase == 'pretest':
    allc = {}
    for gid, b, mods in groups:
        cat, roots, clo = collector(b)
        bodies, eqd, meta = [], [], []
        for k, m in enumerate(mods):
            defs, cs = candidates(m, cat, roots)
            allc[m] = dict(group=gid, ndefs=len(defs), defs=defs, candidates=cs)
            for j, c in enumerate(cs):
                bodies += bodies_for(f'{gid}_{k}', j, c)
                if not c['reader']: eqd.append(c['target'])
        lab = f'CtlPre_{gid}'
        src, expect = assemble(lab, mods, [], bodies, False, eqd)
        (pdir / (lab + '.lean')).write_bytes(src); (out / (lab + '.lean.txt')).write_bytes(src)
        meta = dict(label=lab, module=f'{sub}/{lab}', owners=mods, controls=expect)
        (out / (lab + '.json')).write_text(json.dumps(meta, indent=1))
    (out / 'candidates.json').write_text(json.dumps(allc, indent=1))
    print('groups', len(groups), 'owners', len(allc), 'with defs', sum(1 for v in allc.values() if v['ndefs']),
          'candidates', sum(len(v['candidates']) for v in allc.values()))
elif phase == 'final':
    prd = sys.argv[6]; excl = json.load(open(sys.argv[7])) if len(sys.argv) > 7 else {}
    allc = json.load(open(Path(outdir).parent / 'pretest' / 'candidates.json'))  # outdir = controls/final, pretest = controls/pretest
    plan_s, plan_c, chosen = [], [], {}
    for gid, b, mods in groups:
        meta = json.load(open(Path(outdir).parent / 'pretest' / f'CtlPre_{gid}.json'))
        log = open(Path(prd) / 'mods' / f"{sub.replace('/', '_')}_CtlPre_{gid}.log", encoding='utf-8', errors='replace').read()
        errs = [int(m.group(1)) for m in re.finditer(r'^\S+\.lean:(\d+):\d+: error[:(]', log, re.M)]
        okc = {c['control'] for c in meta['controls'] if not any(c['start_line'] <= e <= c['end_line'] for e in errs)}
        cat, roots, clo = collector(b)
        bodies, eqd, owners_with = [], [], []
        for k, m in enumerate(mods):
            cs = allc[m]['candidates']; pick = None
            for j, c in enumerate(cs):
                tag = f'c{gid}_{k}_{j}'
                if f'{tag}_neg' in okc and (c['reader'] is None or f'{tag}_pos' in okc) and tag not in excl.get(m, []): pick = (j, c); break
            chosen[m] = dict(group=gid, ndefs=allc[m]['ndefs'], pick=pick[1] if pick else None, pick_index=pick[0] if pick else None,
                             status=('pair' if pick and pick[1]['reader'] else 'no reader' if pick else ('defines nothing' if not allc[m]['ndefs'] else 'no passing candidate')))
            if pick:
                bodies += bodies_for(f'{gid}_{k}', pick[0], pick[1])
                if not pick[1]['reader']: eqd.append(pick[1]['target'])
        if not bodies: continue
        for kind, coe in (('U', None), ('S', False), ('C', True)):
            lab = f'Control{kind}_{gid}'
            req = reqrows(mods, cat, clo, bool(coe)) if coe is not None else []
            src, expect = assemble(lab, mods, req, bodies, coe is not None, eqd)
            (pdir / (lab + '.lean')).write_bytes(src); (out / (lab + '.lean.txt')).write_bytes(src)
            p = dict(label=lab, module=f'{sub}/{lab}', owner=gid, kind='batch-owners', sealed=coe is not None, requested=len(req),
                     owners=mods, controls=expect, expected_errors=[e['start_line'] for e in expect if e['negative']] if coe is not None else [])
            if kind in ('U', 'S'): plan_s.append(p)
            if kind in ('U', 'C'): plan_c.append(p)
    (out / 'plan-strict.json').write_text(json.dumps(plan_s, indent=1)); (out / 'plan-coe.json').write_text(json.dumps(plan_c, indent=1))
    (out / 'chosen.json').write_text(json.dumps(chosen, indent=1))
    print(collections.Counter(v['status'] for v in chosen.values()), 'harnesses', len(plan_s) // 2)
