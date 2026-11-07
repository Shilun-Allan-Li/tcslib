from pathlib import Path
import collections, datetime, hashlib, json, re, subprocess

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
SETUP = json.loads((OUT / 'setup.json').read_text())
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

runs = []
for f in sorted(OUT.glob('*-run.json')):
    r = json.loads(f.read_text()); name = r['name']
    assert sha(Path(r['source'])) == r['input_sha256']
    assert sha(OUT / (name + '.out')) == r['output_sha256']
    log = (OUT / (name + '.out')).read_text()
    count = len(re.findall(r'^.*:\d+:\d+: error(?:\([^)]*\))?:', log, re.M))
    assert count == r['errors']
    runs.append(dict(name=name, exit=r['exit'], errors=count, seconds=r['seconds'],
                     warnings=len(re.findall(r': warning:', log))))
for n in ['Wrappers-sealed-v2', 'Wrappers-native-v2', 'Primitives-sealed-v2',
          'Primitives-native-v2', 'Published-consumers', 'Controls-native']:
    r = next(r for r in runs if r['name'] == n)
    assert r['exit'] == 0 and r['errors'] == 0

guard = (OUT / 'guard.txt').read_text()
recoveries = []
for name in ['Wrappers', 'Primitives']:
    native = (OUT / (name + '-native.lean.txt')).read_text()
    sealed = (OUT / (name + '-sealed-v2.lean.txt')).read_text()
    block = (OUT / (name + '-target.lean.txt')).read_text()
    wrapper = 'section\n' + guard + '\n' + block + 'end\n\n'
    assert sealed.count(wrapper) == 1
    assert sealed.index(guard) < sealed.index(block)
    tail = '\n#print axioms Turing.FinTM.' + ('redirectTM_spaceUsedByTape' if name == 'Wrappers' else 'incFixedTM_spaceUsed') + '\n'
    appendix = (OUT / (name + '-owner-metadata.lean.txt')).read_text()
    assert sealed.endswith(tail + appendix)
    assert sealed.removesuffix(tail + appendix).replace(wrapper, block, 1) == native
    rel = 'TCSlib/Complexity/TuringMachine/Build/' + name + '.lean'
    base = subprocess.run(['git', 'show', SETUP['base_source'] + ':' + rel], cwd=ROOT,
                          stdout=subprocess.PIPE, check=True).stdout
    assert native.count(block) == 1
    exact_recovery = native.replace(block, '', 1).encode() == base
    if not exact_recovery:
        assert name == 'Wrappers' and native.count(block + '\n') == 1
        assert native.replace(block + '\n', '', 1).encode() == base
    actual = Path(SETUP['actual_worktree']) / rel
    assert actual.read_bytes() == native.encode()
    recoveries.append(dict(owner=name, guard_removal_recovers_native=True,
                           insertion_removal_recovers_API1160=exact_recovery,
                           extra_one_blank_line=(not exact_recovery), actual_live_bytes_equal=True))

models = SETUP['model_definitions']
defs = models + ['Turing.FinTM.redirectTM', 'Turing.FinTM.incFixedTM']
expected = {(n, mode) for n in defs for mode in ['point', 'abstract']}
positive = re.findall(r'^CONTROL\|([^|]+)\|([^|]+)\|PASS\|kernelChecked=(.+)$',
                      (OUT / 'Controls-native.out').read_text(), re.M)
negative = re.findall(r'^CONTROL\|([^|]+)\|([^|]+)\|FAIL$',
                      (OUT / 'Controls-sealed.out').read_text(), re.M)
errors = re.findall(r'^.*:\d+:\d+: error: RFL_CONTROL\|([^|]+)\|([^|]+)\|Tactic `rfl` failed:',
                    (OUT / 'Controls-sealed.out').read_text(), re.M)
for rows in [[(n, m) for n, m, _ in positive], negative, errors]:
    assert collections.Counter(rows) == collections.Counter(expected)
assert len({k for _, _, k in positive}) == 52
neg_run = next(r for r in runs if r['name'] == 'Controls-sealed')
assert neg_run['exit'] == 1 and neg_run['errors'] == 52
cs = (OUT / 'Controls-sealed.lean.txt').read_text()
cn = (OUT / 'Controls-native.lean.txt').read_text()
seal_line = 'attribute [local irreducible] ' + ' '.join(defs) + '\n'
assert cs.replace(seal_line, '', 1) == cn
(OUT / 'control-check.json').write_text(json.dumps(dict(definitions=26, controls=52,
    positive_kernel_theorems=52, negative_errors=52, every_identity_once=True,
    no_unexpected_negative_error=True, source_guard_only_difference=True), indent=2) + '\n')

inventory = []
for name in ['Wrappers-sealed-v2', 'Primitives-sealed-v2', 'Published-consumers']:
    text = (OUT / (name + '.out')).read_text()
    roots = re.findall(r'^ROOT\|([^|]+)\|private=(true|false)$', text, re.M)
    axs = re.findall(r'^PROOFAX\|([^|]+)\|kind=([^|]+)\|\[([^]]*)\]', text, re.M)
    reached = re.findall(r'^FOREIGNDEF\|([^|]+)\|([^|]+)\|([^|]+)\|hints=(\w+)$', text, re.M)
    homes = re.findall(r'^HOMEDEF\|([^|]+)\|(.+)$', text, re.M)
    for _, _, a in axs:
        assert {x.strip() for x in a.split(',') if x.strip()} <= ALLOWED
    if name != 'Published-consumers':
        assert not {d for _, d, _, h in reached if h != 'abbrev'} - set(models)
    else:
        # Actual imported API roots are inspected as their owner sections; consumer roots
        # consume them opaquely. Do not call the owned redirect matcher a foreign consumer read.
        for r, d, owner, hint in reached:
            if hint != 'abbrev' and (r.startswith('Gate119IncRedirect.') or 'importedRedirectSymmetry' in r):
                assert d in defs
    inventory.append(dict(run=name, roots=roots,
        roots_and_descendants=[dict(name=n, kind=k, axioms=[x.strip() for x in a.split(',') if x.strip()]) for n, k, a in axs],
        direct_foreign_definitions=[dict(root=r, definition=d, owner=o, hints=h) for r, d, o, h in reached],
        same_home_definitions=[dict(root=r, definition=d) for r, d in homes]))
(OUT / 'compiled-inventory.json').write_text(json.dumps(inventory, indent=2) + '\n')

boundary = next(r for r in runs if r['name'] == 'Raw-header-boundary')
bt = (OUT / 'Raw-header-boundary.out').read_text()
assert boundary['exit'] == 1 and boundary['errors'] == 1
assert 'Fin M.k' in bt and 'Fin (M.redirectTM haltOn).k' in bt
for rel, expected_hash in SETUP['snapshot_target_hashes'].items():
    assert sha(Path(SETUP['snapshot']) / Path(rel).with_suffix('.olean')) == expected_hash
assert len(list(Path(SETUP['overlay']).rglob('*.olean'))) == SETUP['olean_files_before'] == 895
assert (Path(SETUP['project']) / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.25.0'
result = dict(checked_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    status='PASS bounded actual incFixed and relocated redirect owner sections/imported consumers',
    runs=runs, source_recoveries=recoveries, complete_private_overlay_oleans=895,
    shared_target_snapshot_objects_unchanged=True, expected_raw_index_header_failure=True,
    no_actual_source_or_Git_or_shared_snapshot_or_screen_mutation=True,
    toolchain_side_effect='Initial temporary project omitted pin: elan installed4.35, four incompatible-header failures. Corrected to4.25; root notified; no removal by this agent.',
    limits='Partial2-owner native import chain on complete mra2 clone; root owns integrated5-module chain/full replay/gate. No global legacy seal or merge clearance.')
(OUT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(status=result['status'], runs=runs,
    metadata_counts={r['run']:len(r['roots_and_descendants']) for r in inventory}), indent=2))
