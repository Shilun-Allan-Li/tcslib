#!/usr/bin/env python3
"""mkctl_s1.py <archived-gate10-tools> <collector-log> <controls-spec.json> <worktree> <probe-subdir>
              <outdir> <variant: strict|coe>      (cleanup-stage1; adapted from DW-5's mkctl_dw5.py)

Paired Rule-10 controls for every new or changed owner.  DW-5's generator sealed controls with the
seal record of a downstream owner; several Stage 1 owners have none (the new modules), so each control
probe here carries its own seal: every ordinary TCSlib definition (kind def, matcher or not
status-reducible; the collector's CAT rows) whose home is in the owner's TCSlib import closure OR is
the owner itself (so the owner's own definitions are sealed too), minus the notation exclusions:
PolyExpr.eval always excluded (as seal A), and in the coe variant also
FinDist.instCoeFunForallReal (as mkseals_coe.py).  Seal command: the archived Gate06/10
`build_seals.seal_command` (install after the imports, EOF verification), unchanged.

controls-spec.json: {owner module (dotted): [{"name": ..., "negative": <lean>, "positive": <lean>}]}.
Each negative reads one of the owner's definitions by `rfl`/`show`/`unfold` (it must fail exactly
once when sealed); each positive states the same fact through the published reader.  For each owner
two probes are written: ControlS_<owner> (sealed) and ControlU_<owner> (unsealed, the pretest).
controls-plan.json lists, per probe, the control line ranges and the expected error lines (sealed
negatives only), in the format of DW-5's ctlcheck2.py.
"""
import importlib.util, json, sys
from pathlib import Path

tools, log, specf, wt, sub, outdir, variant = sys.argv[1:8]
sys.dont_write_bytecode = True


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


bs = load(Path(tools) / 'build_seals.py', 'levin_bs')
controls = load(Path(tools) / 'build_controls.py', 'levin_controls')
adapter = load(Path(tools) / 'request_payload_adapter.py', 'levin_adapter')
adapter.configure_builders(bs, controls)
cat, closures = {}, {}
for line in open(log, encoding='utf-8'):
    if line.startswith('CAT '):
        r = json.loads(line[4:]); cat[r['name']['display']] = r
    elif line.startswith('CLOSURE '):
        r = json.loads(line[8:]); closures[r['module']] = r['closure']
EXCL = {'Complexity.PolyExpr.eval'}
if variant == 'coe':
    EXCL |= {'TCSlib.InformationTheory.FinDist.instCoeFunForallReal'}
SPEC = json.load(open(specf))
out = Path(outdir); out.mkdir(parents=True, exist_ok=True)
plan = []
for owner, ctls in sorted(SPEC.items()):
    homes = set(closures[owner]) | {owner}
    rows = sorted((r for r in cat.values() if r['home']['display'] in homes and r['kind'] == 'def'
                   and (r['matcher'] or r['status'] != 'reducible')
                   and r['name']['display'] not in EXCL), key=lambda r: r['name']['display'])
    rows = [dict(spelling=r['name']['display'], home=r['home']['display'],
                 name_components=r['name']['components'], home_components=r['home']['components'],
                 instance=r['instance'], matcher=r['matcher'], abbrev=r['abbrev'],
                 collector_reducibility=r['status']) for r in rows]
    own = sorted(r['spelling'] for r in rows if r['home'] == owner)
    bodies = []
    for c in ctls:
        bodies.append((c['name'], True, c['negative']))
        bodies.append((c['name'] + 'Reader', False, c['positive']))
    for sealed in (True, False):
        tag = owner.split('.', 1)[1].replace('.', '_')
        lab = ('ControlS_' if sealed else 'ControlU_') + tag
        src = (f"import Lean\nimport {owner}\n\nset_option maxHeartbeats 0\nset_option autoImplicit false\n"
               "set_option relaxedAutoImplicit false\n\n").encode()
        if sealed:
            src += bs.seal_command(lab, rows, end=False)
        src += b"namespace S1Controls\n\n"
        expect = []
        for name, negative, body in bodies:
            start = src.count(b"\n") + 1
            src += body.encode() + b"\n"
            expect.append(dict(control=name, target=owner, negative=negative, start_line=start,
                               end_line=start + body.count('\n') - 1))
        src += b"end S1Controls\n\n"
        if sealed:
            src += bs.seal_command(lab, rows, end=True)
        p = Path(wt) / sub / (lab + '.lean'); p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(src); (out / (lab + '.lean.txt')).write_bytes(src)
        plan.append(dict(label=lab, module=f'{sub}/{lab}', owner=owner, kind='own-and-closure-seal',
                         variant=variant, sealed=sealed, requested=len(rows) if sealed else 0,
                         own_definitions_sealed=len(own) if sealed else 0, controls=expect,
                         expected_errors=[e['start_line'] for e in expect if e['negative']]
                         if sealed else []))
(out / 'controls-plan.json').write_text(json.dumps(plan, indent=1))
print(len(plan), 'control probes;', sum(len(p['expected_errors']) for p in plan),
      'expected sealed failures')
