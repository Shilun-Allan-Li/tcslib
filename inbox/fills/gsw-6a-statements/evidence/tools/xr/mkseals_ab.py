"""mkseals_ab.py (nm-cca2 review: levin mkseals.py with one change, SEAL_EVAL=1 empties the notation exclusion)
mkseals.py <tools-dir> <collector-log> <worktree> <rev> <outdir> <probe-subdir> <label-prefix> <module>...
Builds whole-file conservative seals with the archived Gate06/Gate10 instrumenter
(build_seals.instrument + request_payload_adapter.configure_builders: actual-Name component checks,
instance unfolding mask, EOF verification). Requests per owner = every ordinary TCSlib definition
in the owner's transitive import closure (kind def, matcher or not status-reducible), minus the exact
notation exclusion PolyExpr.eval (the conservative closure that also covers anonymous commands).
The elaborated-term rows (foreign definitions referenced by any stored constant of the owner) must be
a subset of the closure rows or of the recorded reducible/abbrev/notation exclusions.
Source bytes are taken from `git show <rev>:<path>` and must equal the worktree file when rev is HEAD."""
import sys, json, importlib.util, subprocess, hashlib
from pathlib import Path
tools, log, wt, rev, outdir, sub, prefix = sys.argv[1:8]
modules = sys.argv[8:]
sys.dont_write_bytecode = True
def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path); m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m); return m
bs = load(Path(tools) / 'build_seals.py', 'levin_bs')
controls = load(Path(tools) / 'build_controls.py', 'levin_controls')
adapter = load(Path(tools) / 'request_payload_adapter.py', 'levin_adapter')
adapter.configure_builders(bs, controls)
import os
CHUNK = int(os.environ.get('SEAL_CHUNK', '0'))
if CHUNK:
    # Very large request sets overflow Lean's stack in one harness command (observed at 2,921 and
    # 5,459 rows); split them into several complete harness commands of at most CHUNK rows each.
    _orig = bs.seal_command
    def _chunked(label, rows, *, end):
        if len(rows) <= CHUNK: return _orig(label, rows, end=end)
        return b''.join(_orig(f'{label}_part{i // CHUNK + 1}', rows[i:i + CHUNK], end=end) for i in range(0, len(rows), CHUNK))
    bs.seal_command = _chunked
sha = lambda b: hashlib.sha256(b).hexdigest()
cat, roots, closures, counts = {}, {}, {}, {}
for line in open(log, encoding='utf-8'):
    line = line.rstrip('\n')
    if line.startswith('CAT '):
        r = json.loads(line[4:]); assert r['name']['display'] not in cat, r; cat[r['name']['display']] = r
    elif line.startswith('ROOT '):
        r = json.loads(line[5:]); roots.setdefault(r['module'], []).append(r)
    elif line.startswith('CLOSURE '):
        r = json.loads(line[8:]); closures[r['module']] = r['closure']
    elif line.startswith('MODULE '):
        m, c = line[7:].split(': stored '); counts[m] = int(c)
EXCL = set() if os.environ.get('SEAL_EVAL') == '1' else {'Complexity.PolyExpr.eval'}  # nm-cca2 review: SEAL_EVAL=1 seals PolyExpr.eval too (variant B)
out = Path(outdir); out.mkdir(parents=True, exist_ok=True)
manifest = {'rev': rev, 'collector_log_sha256': sha(open(log, 'rb').read()),
            'tools_sha256': {p.name: sha(p.read_bytes()) for p in sorted(Path(tools).glob('*.py'))},
            'notation_exclusions': sorted(EXCL), 'probes': []}
for module in modules:
    path = module.replace('.', '/') + '.lean'
    raw = subprocess.run(['git', '-C', wt, 'show', f'{rev}:{path}'], capture_output=True, check=True).stdout
    clo = set(closures[module])
    def eligible(r): return r['kind'] == 'def' and (r['matcher'] or r['status'] != 'reducible') and r['name']['display'] not in EXCL
    closure_rows = sorted((r for r in cat.values() if r['home']['display'] in clo and eligible(r)), key=lambda r: r['name']['display'])
    term = {}
    for rt in roots.get(module, []):
        for ref in rt['type_refs'] + rt['value_refs']:
            term.setdefault(ref['display'], set()).add(rt['name']['display'])
    cnames = {r['name']['display'] for r in closure_rows}
    excluded_terms = {}
    for t in sorted(term):
        if t in cnames: continue
        r = cat[t]
        assert r['home']['display'] in clo, (module, t)
        reason = 'notation' if t in EXCL else ('abbrev' if r['abbrev'] else ('reducible' if r['status'] == 'reducible' else None))
        assert reason, ('term row outside closure and not excluded', module, t)
        excluded_terms[t] = reason
    rows = [dict(spelling=r['name']['display'], home=r['home']['display'], name_components=r['name']['components'],
                 home_components=r['home']['components'], instance=r['instance'], matcher=r['matcher'],
                 abbrev=r['abbrev'], collector_reducibility=r['status']) for r in closure_rows]
    label = prefix + module.split('.', 1)[1].replace('.', '_')
    probe, ins, lmap = bs.instrument(raw, bs.header(raw), label, rows)
    pp = Path(wt) / sub / (label + '.lean'); pp.parent.mkdir(parents=True, exist_ok=True)
    pp.write_bytes(probe); (out / (label + '.lean.txt')).write_bytes(probe)
    rec = dict(label=label, module=module, source=path, rev=rev, source_sha256=sha(raw), probe_sha256=sha(probe),
               probe_module=f'{sub}/{label}', requested=len(rows), term_names=len(term),
               term_in_closure=sum(1 for t in term if t in cnames), term_excluded=excluded_terms,
               stored_constants=counts.get(module), closure_modules=len(clo),
               reducible_nonabbrev_in_closure=sorted(r['name']['display'] for r in cat.values()
                   if r['home']['display'] in clo and r['kind'] == 'def' and r['status'] == 'reducible' and not r['abbrev'] and not r['matcher']),
               insertions=ins, source_to_probe_lines=lmap,
               term_readers={t: sorted(v) for t, v in term.items()}, rows=rows)
    (out / (label + '.json')).write_text(json.dumps(rec, indent=1))
    manifest['probes'].append({k: rec[k] for k in ('label', 'module', 'source', 'source_sha256', 'probe_sha256', 'probe_module', 'requested', 'term_names', 'term_in_closure', 'stored_constants')} | {'term_excluded': len(excluded_terms)})
    print(label, module, 'requests', len(rows), 'terms', len(term), 'excluded-terms', len(excluded_terms), 'stored', counts.get(module))
(out / 'manifest.json').write_text(json.dumps(manifest, indent=1))
