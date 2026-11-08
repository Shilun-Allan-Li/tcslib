"""Read-only checks of all retained attempts, final pins, controls and compiled inventory."""
from pathlib import Path
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
context = json.loads((OUT / 'context.json').read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


attempts = []
for receipt in sorted(OUT.glob('*-run.json')):
    row = json.loads(receipt.read_text())
    name = receipt.name[:-len('-run.json')]
    source = (OUT / (name + '.lean.txt')).read_bytes()
    log = (OUT / (name + '.out')).read_bytes()
    assert sha(source) == row['input_sha256']
    assert sha(log) == row['output_sha256']
    assert Path(row['command'][-1]).read_bytes() == source
    assert row['command'][1].endswith('/devtools/seyoon/leanelab.sh')
    assert row['plain_managed'] and row['local_slots'] == '3'
    errors = len(re.findall(r'^.*:\d+:\d+: error(?:\([^)]*\))?:', log.decode(), re.M))
    assert errors == row['errors']
    attempts.append(dict(name=name, exit=row['exit'], errors=errors,
                         warnings=len(re.findall(r'^.*:\d+:\d+: warning:', log.decode(), re.M)),
                         seconds=row['seconds'], input_sha256=row['input_sha256'],
                         output_sha256=row['output_sha256']))
assert len(attempts) == 7
by_name = {row['name']: row for row in attempts}
for name in ['First-header-native-v3', 'First-header-sealed-v3']:
    assert (by_name[name]['exit'], by_name[name]['errors'], by_name[name]['warnings']) == (0, 0, 0)

native = (OUT / 'First-header-native-v3.lean.txt').read_text()
sealed = (OUT / 'First-header-sealed-v3.lean.txt').read_text()
guard = (OUT / 'guard.txt').read_text()
assert sealed.count(guard) == 1 and sealed.replace(guard, '', 1) == native
assert sealed.index(guard) < sealed.index('/--') < sealed.index('private theorem first_header_component')
definitions = (OUT / 'control-definitions.txt').read_text().splitlines()
assert len(definitions) == len(set(definitions)) == 34
assert definitions == guard.splitlines()[0].split('] ', 1)[1].split()
control = json.loads((OUT / 'control-check.json').read_text())
assert control['definitions'] == 34 and control['pointwise_and_abstracted_pairs'] == 68
assert control['positive_exit'] == 0 and control['negative_exit'] == 1
assert control['negative_lean_diagnostics'] == 68 and control['all_exact_multiplicities_match']
assert set(control['checker_negative_cases'].values()) == {'rejected'}

log = (OUT / 'First-header-sealed-v3.out').read_text()
axioms = []
for match in re.finditer(r'^PROOFAX\|([^|\n]+)\|kind=([^|\n]+)\|\[([^\]]*)\]', log, re.M):
    name, kind, raw = match.groups()
    ax = [x.strip() for x in raw.split(',') if x.strip()]
    assert set(ax) <= {'propext', 'Classical.choice', 'Quot.sound'}
    axioms.append(dict(name=name, kind=kind, axioms=ax))
assert len(axioms) == 3 and all(row['kind'] == 'theorem' for row in axioms)
assert 'sorryAx' not in log
foreign = []
for line in log.splitlines():
    if line.startswith('FOREIGNDEF|'):
        _, root, name, owner, hints = line.split('|')
        foreign.append(dict(root=root, name=name, owner=owner, hints=hints.split('=', 1)[1]))
ordinary = sorted({row['name'] for row in foreign if row['hints'] == 'regular'})
abbreviations = sorted({row['name'] for row in foreign if row['hints'] == 'abbrev'})
assert len(ordinary) == 9 and set(ordinary) <= set(definitions)
(OUT / 'compiled-inventory.json').write_text(json.dumps(dict(
    root_count=1, compiled_descendants=2, axioms=axioms,
    direct_foreign_references=foreign, direct_ordinary_definitions=ordinary,
    direct_abbreviations=abbreviations, all_direct_ordinary_guarded=True,
    scope='The actual first-header theorem type/value and all prefix-named compiled descendants. Imported theorem proof bodies are consumed opaquely, not recursively re-audited.'), indent=2) + '\n')

for rel, expected in context['sources'].items():
    assert sha((Path(context['worktree']) / rel).read_bytes()) == expected, rel
for rel, expected in context['compiled'].items():
    assert sha((Path(context['snapshot']) / rel.replace('.lean', '.olean')).read_bytes()) == expected, rel
summary = dict(status='Bounded first-header+rewind pre-ship component passed; no fill, complete prefix or dispatch readiness claim.',
    attempts=attempts, guard_definitions=34, controls_pairs=68,
    root_count=1, compiled_descendants=2, all_three_standard_axioms=True,
    source_and_snapshot_pins_unchanged=True, native_sealed_guard_removal_byte_identity=True,
    guard_before_docs_and_headers=True, default_simp_definitions_removed=[
        'Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg'],
    final_native_sha256=sha(native.encode()), final_sealed_sha256=sha(sealed.encode()),
    tested_reader_or_type_gap=None,
    no_actual_source_git_snapshot_cache_screen_or_admission_changes=True)
(OUT / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({key: value for key, value in summary.items() if key != 'attempts'}, indent=2))
