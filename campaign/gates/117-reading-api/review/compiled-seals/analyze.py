"""Reconcile raw gate117 evidence, preserving every run and checking frozen inputs."""
from collections import Counter, defaultdict
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

out = Path(__file__).resolve().parent
root = out.parents[4]
scratch = Path(os.environ['TCSLIB_SCRATCH'])
base = 'e3adffac67377a8b6e23bed74bfdbb44a123dd86'
head = '1160c18f03fd318f0dec25738790935fa61379d4'
wt = scratch / 'wt-natbits'
for commit in (base, head):
    subprocess.run(['git', '-C', str(wt), 'cat-file', '-e', commit + '^{commit}'], check=True)


def sha(data):
    return hashlib.sha256(data).hexdigest()


census = {}
for side in ('base', 'head'):
    entries = {}
    for line in (out / ('Census-' + side + '.out')).read_text().splitlines():
        if not line.startswith('CONSTANT|'):
            continue
        _, name, owner, kind, internal, private = line.split('|')
        assert name not in entries
        entries[name] = dict(name=name, owner=owner, kind=kind,
                             internal=internal == 'true', private=private == 'true')
    census[side] = entries
added = set(census['head']) - set(census['base'])
removed = set(census['base']) - set(census['head'])
assert len(added) == 23 and not removed
assert all(census['base'][n] == census['head'][n] for n in set(census['base']) & set(census['head']))
assert all(census['head'][n]['kind'] == 'theorem' and not census['head'][n]['private']
           and not census['head'][n]['internal'] for n in added)
generated = {f'Turing.FinTM.{stem}_{field}' for stem in ('leftCfg', 'rightCfg')
             for field in ('state', 'inputPos', 'workTapes', 'workTapePos', 'output')}
generated |= {f'Turing.captureCfg_{field}' for field in
              ('state', 'inputPos', 'workTapes', 'workTapePos', 'output')}
assert generated <= added and len(generated) == 15

targets, axioms, defaults = {}, {}, []
foreign, abbreviations = defaultdict(set), set()
auxiliaries = []
lines = (out / 'Metadata-head-v2.out').read_text().splitlines()
for line in lines:
    parts = line.split('|')
    if line.startswith('TARGET|'):
        assert parts[1] not in targets
        targets[parts[1]] = parts
    elif line.startswith('AXIOMS|'):
        assert parts[1] not in axioms
        axioms[parts[1]] = [] if parts[2] == '[]' else parts[2][1:-1].split(', ')
    elif line.startswith('DEF|') and parts[4] == 'sameOwner=false':
        if parts[5] == 'hints=abbrev':
            abbreviations.add(parts[2])
        else:
            foreign[parts[1]].add(parts[2])
    elif line.startswith('SIMPDEF|'):
        defaults.append(parts[1])
    elif line.startswith('AUXILIARY|'):
        auxiliaries.append(line)
assert set(targets) == added == set(axioms)
assert all(t[3:] == ['private=false', 'internal=false', 'simp=false', 'unfold=false']
           for t in targets.values())
assert all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms.values())
assert not auxiliaries
assert len(abbreviations) == 9
assert set(defaults) == {'Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg'}
foreign_by_owner = defaultdict(set)
for name, defs in foreign.items():
    foreign_by_owner[targets[name][2]].update(defs)

additions = json.loads((root / 'campaign/gates/117-reading-api/evidence/additions.json').read_text())
context = dict(base=base, head=head, toolchain=(wt / 'lean-toolchain').read_text().strip(),
               sources={}, snapshots={}, owner_sources_recovered=True)
guard_map = json.loads((out / 'owner-full-source-map.json').read_text())
for row in guard_map:
    path = row['source']
    frozen = subprocess.check_output(['git', '-C', str(wt), 'show', head + ':' + path])
    assert (wt / path).read_bytes() == frozen
    assert sha(frozen) == row['source_sha256']
    copy = (out / (row['probe'] + '.lean.txt')).read_text()
    assert sha(copy.encode()) == row['guarded_sha256']
    recovered = re.sub(r'\nsection Gate117NewSection\d+\nattribute \[local irreducible\] [^\n]+\n'
                       r'attribute \[-simp\] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n',
                       '', copy)
    recovered = re.sub(r'\nend Gate117NewSection\d+\nattribute \[simp\] Turing.Action.apply '
                       r'Turing.Cfg.init Turing.MultiTapeTM.initCfg\n', '', recovered)
    assert recovered.encode() == frozen
    context['sources'][path] = dict(head_sha256=sha(frozen),
        head_blob=subprocess.check_output(['git', '-C', str(wt), 'rev-parse', head + ':' + path], text=True).strip())
    for label, snapshot in [('base', 'oleans-mac3'), ('head', 'oleans-reading-preflight2')]:
        p = scratch / snapshot / path.replace('.lean', '.olean')
        context['snapshots'].setdefault(label, {})[str(p)] = dict(sha256=sha(p.read_bytes()), bytes=p.stat().st_size)
context['worktree_heads'] = {label: subprocess.check_output(['git', '-C', str(scratch / tree), 'rev-parse', 'HEAD'], text=True).strip()
                            for label, tree in [('base', 'wt-camp'), ('head', 'wt-natbits')]}
(out / 'context.json').write_text(json.dumps(context, indent=2) + '\n')

expected = {'Metadata-head': (1, 1), 'Owner-sections-sealed': (1, 3),
            'Published-consumers-sealed': (1, 4), 'Controls-sealed': (1, 32),
            'Abbreviations-unsealable': (1, 9)}
runs = []
for receipt_path in sorted(out.glob('*-run.json')):
    stem = receipt_path.name.removesuffix('-run.json')
    receipt = json.loads(receipt_path.read_text())
    source = (out / (stem + '.lean.txt')).read_bytes()
    raw = (out / (stem + '.out')).read_bytes()
    assert sha(source) == receipt['input_sha256'] and sha(raw) == receipt['output_sha256']
    assert len(re.findall(rb'(?m)^.*:\d+:\d+: error:', raw)) == receipt['errors']
    assert (receipt['exit'], receipt['errors']) == expected.get(stem, (0, 0)), stem
    runs.append(dict(probe=stem, exit=receipt['exit'], errors=receipt['errors'],
                     input_output_hashes_match=True))
result = dict(base_constants=len(census['base']), head_constants=len(census['head']),
              added_public_theorems=len(added), generated_public_fields=len(generated),
              explicit_source_theorems=len(added - generated), removals=0,
              private_counts={side: sum(r['private'] for r in census[side].values()) for side in census},
              additional_compiler_auxiliaries=auxiliaries,
              axiom_sets=dict(Counter(str(a) for a in axioms.values())),
              all_23_public_non_simp=True,
              foreign_regular_by_target_owner={owner: sorted(names) for owner, names in foreign_by_owner.items()},
              default_simp_definitions=sorted(defaults), abbreviation_exclusions=sorted(abbreviations),
              runs=runs, all_recorded_outcomes_and_hashes_match=True)
(out / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
