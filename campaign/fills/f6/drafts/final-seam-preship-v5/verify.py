from pathlib import Path
import collections, datetime, hashlib, json, re

OUT = Path(__file__).resolve().parent
OLD = OUT.parent / 'layout-preship-v2'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

runs = []
for receipt in sorted(OUT.glob('*-run.json')):
    name = receipt.name.removesuffix('-run.json')
    row = json.loads(receipt.read_text())
    assert digest(OUT / (name + '.lean.txt')) == row['input_sha256']
    assert digest(OUT / (name + '.out')) == row['output_sha256']
    assert digest(Path(row['command'][-1])) == row['input_sha256']
    output = (OUT / (name + '.out')).read_text()
    errors = re.findall(r'^.*:\d+:\d+: error(?:\([^)]*\))?:', output, re.M)
    assert len(errors) == row['errors']
    runs.append(dict(name=name, exit=row['exit'], errors=len(errors),
                     seconds=row['seconds'], warnings=len(re.findall(r': warning:', output))))

for name in ['Seam-sealed-v5', 'Final-native', 'Final-sealed', 'Controls-native']:
    row = next(r for r in runs if r['name'] == name)
    assert row['exit'] == 0 and row['errors'] == 0 and row['warnings'] == 0
    assert 'sorryAx' not in (OUT / (name + '.out')).read_text()

sealed = (OUT / 'Final-sealed.lean.txt').read_text()
native = (OUT / 'Final-native.lean.txt').read_text()
guard = (OUT / 'guard.txt').read_text().splitlines()[0] + '\n'
assert sealed.count(guard) == 1
assert sealed.replace(guard, '') == native
assert sealed.index(guard) < sealed.index('/-- Pure layout')
assert 'attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg' in sealed

text = (OUT / 'Final-sealed.out').read_text()
roots = re.findall(r'^ROOT\|([^|]+)\|private=(true|false)$', text, re.M)
axioms = re.findall(r'^PROOFAX\|([^|]+)\|kind=([^|]+)\|\[([^]]*)\]', text, re.M)
defs = re.findall(r'^FOREIGNDEF\|([^|]+)\|([^|]+)\|([^|]+)\|hints=(\w+)$', text, re.M)
assert len(roots) == 11
assert len({n for n, _ in roots}) == 11
for name, kind, raw in axioms:
    assert kind == 'theorem'
    assert {x.strip() for x in raw.split(',') if x.strip()} <= ALLOWED
guards = json.loads((OUT / 'seal-inventory.json').read_text())['definitions']
ordinary = sorted({d for _, d, _, hint in defs if hint != 'abbrev'})
abbreviations = sorted({d for _, d, _, hint in defs if hint == 'abbrev'})
assert not set(ordinary) - set(guards)
inventory = dict(
    roots=[dict(name=n, private=v == 'true') for n, v in roots],
    roots_count=len(roots),
    selected_including_descendants=[dict(name=n, kind=k, axioms=[x.strip() for x in a.split(',') if x.strip()])
                                    for n, k, a in axioms],
    selected_count=len(axioms),
    direct_foreign_definitions=[dict(root=r, definition=d, owner=m, hints=h) for r, d, m, h in defs],
    ordinary_definitions=ordinary, abbrev_projection_exclusions=abbreviations,
    all_direct_ordinary_defs_guarded=True, guard_count=len(guards),
    scope='All11 scratch roots and prefix-named compiler descendants; direct types/values; imported theorem proofs opaque. Guard32 is conservative.')
(OUT / 'compiled-inventory.json').write_text(json.dumps(inventory, indent=2) + '\n')

cs = (OUT / 'Controls-sealed.lean.txt').read_text()
cn = (OUT / 'Controls-native.lean.txt').read_text()
assert cs.replace(guard, '') == cn
decls = [(m.group(1), cs[:m.start()].count('\n') + 1)
         for m in re.finditer(r'^theorem (control_\d+)', cs, re.M)]
assert len(decls) == 64
raw_errors = [(int(m.group(1)), m.group(3)) for m in re.finditer(
    r'^.*:(\d+):(\d+): error(?:\([^)]*\))?: (.*)$',
    (OUT / 'Controls-sealed.out').read_text(), re.M)]
old_index = json.loads((OLD / 'controls-index.json').read_text())
assert len(old_index) == 32
count = collections.Counter()
rows = []
for line, msg in raw_errors:
    assert msg.startswith('Tactic `rfl` failed')
    owners = [name for i, (name, start) in enumerate(decls)
              if start <= line < (decls[i+1][1] if i+1 < len(decls) else 100000)]
    assert len(owners) == 1
    count[owners[0]] += 1
assert set(count) == {n for n, _ in decls}
for i, (name, start) in enumerate(decls):
    assert count[name] == 1
    definition = old_index[i // 2]['definition']
    assert definition in guards
    stop = decls[i+1][1] if i+1 < len(decls) else 100000
    rows.append(dict(name='F6SeamControls.' + name, definition=definition,
                     mode='pointwise' if i % 2 == 0 else 'abstracted',
                     sealed_start_line=start, sealed_error_lines=[l for l, _ in raw_errors if start <= l < stop]))
assert {r['definition'] for r in rows} == set(guards)
assert len(raw_errors) == 64
assert next(r for r in runs if r['name'] == 'Controls-sealed')['exit'] == 1
native_controls = re.findall(r"^'F6SeamControls\.(control_\d+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
                             (OUT / 'Controls-native.out').read_text(), re.M)
assert len(native_controls) == 64
assert {n for n, _ in native_controls} == {n for n, _ in decls}
for _, raw in native_controls:
    assert {x.strip() for x in raw.split(',') if x.strip()} <= ALLOWED
(OUT / 'controls-index.json').write_text(json.dumps(rows, indent=2) + '\n')

context = json.loads((OUT / 'context.json').read_text())
pins = []
for row in context['files']:
    a = digest(Path(row['source_path'])) == row['source_sha256']
    b = digest(Path(row['olean_path'])) == row['olean_sha256']
    assert a and b
    pins.append(dict(module=row['module'], source_unchanged=a, compiled_unchanged=b))

result = dict(
    checked_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    status='PASS bounded conditional last-ruler final seam only; F6 remains unissued',
    runs=runs, roots=len(roots), roots_and_descendants=len(axioms),
    ordinary_definitions=len(ordinary), abbrev_projection_exclusions=len(abbreviations),
    guard_definitions=len(guards), native_sealed_guard_only_difference=True,
    controls=dict(definitions=32, native_theorems=64, sealed_errors=64,
                  exactly_one_expected_rfl_failure_per_identity=True),
    pin_checks=pins, initial_context_capture_after_v1_to_v5=True,
    no_source_Git_cache_snapshot_screen_or_target_admission_mutations=True,
    limit='No actual prefix/run/cut/hB/hloop proof, universal machine/target fill, merged-tree replay, dispatch or prerequisite merge attestation.')
(OUT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ['status', 'runs', 'roots', 'roots_and_descendants', 'ordinary_definitions', 'abbrev_projection_exclusions', 'controls']}, indent=2))
