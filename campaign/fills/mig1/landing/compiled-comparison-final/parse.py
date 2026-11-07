"""Read-only exact-name analysis of supplied native metadata, with retained maps and deltas.

Run with python3 -I. No Lean, Git, payload scripts, source edits or cache/snapshot writes.
"""
from pathlib import Path
from collections import Counter, defaultdict
import datetime
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
LAND = OUT.parent
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
PENDING = {'Turing.pairDiagTM_spaceUsed', 'Turing.FinTM.incFixedTM_spaceUsed',
           'Turing.MultiTapeTM.exists_first_entry_of_fixed'}
KINDS = {'theorem', 'def', 'axiom', 'opaque', 'constructor', 'recursor', 'inductive', 'quotient'}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def write(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + '\n')


def parse(path):
    lines = path.read_text().splitlines()
    data = dict(census={}, all_axioms={}, public_axioms={}, root_map=[], proof_axioms={},
                descendants={}, cited=[], pending_absent=[], root_count=None)
    ax_tags = {'ALLAX': 'all_axioms', 'PUBLICAX': 'public_axioms'}
    seen_cited = set()
    i = 0
    while i < len(lines):
        text = lines[i]; line = i + 1; i += 1
        if text.startswith('CENSUS|'):
            _, owner, name, kind, priv, internal = text.split('|')
            assert kind in KINDS and priv in {'private=true', 'private=false'}
            assert internal in {'internal=true', 'internal=false'}
            assert name not in data['census'], ('duplicate census name', name)
            data['census'][name] = dict(owner=owner, kind=kind, private=priv == 'private=true',
                                        internal=internal == 'internal=true', line=line)
        elif text.startswith(('ALLAX|', 'PUBLICAX|', 'PROOFAX|')):
            tag = text.split('|', 1)[0]
            if tag == 'PROOFAX':
                _, root, name, ax = text.split('|', 3)
            else:
                _, name, ax = text.split('|', 2)
            while not ax.rstrip().endswith(']'):
                assert i < len(lines) and '|' not in lines[i], ('broken axiom continuation', line)
                ax += ' ' + lines[i].strip(); i += 1
            assert ax.startswith('[') and ax.endswith(']')
            values = [v.strip() for v in ax[1:-1].split(',') if v.strip()]
            assert len(values) == len(set(values))
            if tag == 'PROOFAX':
                target = data['proof_axioms'].setdefault(root, {})
            else:
                target = data[ax_tags[tag]]
            assert name not in target, ('duplicate axiom row', tag, name)
            target[name] = dict(axioms=values, line=line)
        elif text.startswith('ROOTMAP|'):
            _, owner, source, actual = text.split('|')
            assert not any(r['actual'] == actual or (r['owner'], r['source']) == (owner, source)
                           for r in data['root_map'])
            data['root_map'].append(dict(owner=owner, source=source, actual=actual, line=line))
        elif text.startswith('DESC|'):
            _, root, name, kind = text.split('|')
            assert kind in KINDS
            target = data['descendants'].setdefault(root, {})
            assert name not in target
            target[name] = dict(kind=kind, line=line)
        elif text.startswith('CITED|'):
            _, root, descendant, part, name, owner, kind = text.split('|')
            assert part in {'type', 'value'} and kind in KINDS
            key = (root, descendant, part, name)
            assert key not in seen_cited
            seen_cited.add(key)
            data['cited'].append(dict(root=root, descendant=descendant, part=part,
                                      name=name, owner=owner, kind=kind, line=line))
        elif text.startswith('PENDINGABSENT|'):
            _, name = text.split('|')
            assert name not in data['pending_absent']
            data['pending_absent'].append(name)
        elif text.startswith('ROOTCOUNT|'):
            assert data['root_count'] is None
            data['root_count'] = int(text.split('|')[1])
        else:
            raise AssertionError(('unrecognized metadata line', path.name, line, text))
    census = data['census']
    public = {name for name, row in census.items() if not row['private']}
    assert set(data['all_axioms']) == set(census)
    assert set(data['public_axioms']) == public
    assert all(set(data['all_axioms'][n]['axioms']) == set(row['axioms'])
               for n, row in data['public_axioms'].items())
    assert set(data['pending_absent']) == PENDING
    if data['root_map']:
        roots = {row['actual'] for row in data['root_map']}
        assert data['root_count'] == len(roots)
        assert set(data['proof_axioms']) == set(data['descendants']) == roots
        for root in roots:
            expected = {name for name in census if name == root or name.startswith(root + '.')}
            assert set(data['proof_axioms'][root]) == set(data['descendants'][root]) == expected
            for name in expected:
                assert data['descendants'][root][name]['kind'] == census[name]['kind']
                assert set(data['proof_axioms'][root][name]['axioms']) == set(data['all_axioms'][name]['axioms'])
        for row in data['cited']:
            assert row['root'] in roots and row['descendant'] in data['descendants'][row['root']]
            if row['name'] in census:
                assert (row['owner'], row['kind']) == (census[row['name']]['owner'], census[row['name']]['kind'])
    else:
        assert not data['proof_axioms'] and not data['descendants'] and not data['cited']
    return data


inputs = []
snapshots = {}
for label, folder, stem in [('base', 'metadata-final', 'Base'), ('head', 'metadata-final', 'Head'),
                             ('previous-head', 'metadata-phase2', 'Head')]:
    directory = LAND / folder
    raw, probe, receipt = [directory / (stem + suffix) for suffix in ['.out', '.lean.txt', '-run.json']]
    run = json.loads(receipt.read_text())
    assert (run['exit'], run['errors']) == (0, 0)
    assert sha(raw) == run['output_sha256'] and sha(probe) == run['input_sha256']
    assert not re.search(r'^.*:\d+:\d+: (?:error(?:\([^)]*\))?|warning):', raw.read_text(), re.M)
    for source, suffix in [(raw, '.out'), (probe, '.lean.txt'), (receipt, '-run.json')]:
        (OUT / (label + suffix)).write_bytes(source.read_bytes())
    inputs.append(dict(label=label, raw_path=str(raw.relative_to(ROOT)), raw_bytes=raw.stat().st_size,
                       raw_sha256=sha(raw), probe_sha256=sha(probe), receipt_sha256=sha(receipt),
                       native_run_recorded_pass=True, run=run))
    snapshots[label] = parse(raw)
    write('map-' + label + '.json', snapshots[label])

assert (LAND / 'metadata-final/Base.out').read_bytes() == (LAND / 'metadata-phase2/Base.out').read_bytes()
assert (LAND / 'metadata-final/Base-run.json').read_bytes() == (LAND / 'metadata-phase2/Base-run.json').read_bytes()
assert (LAND / 'metadata-final/Head.lean.txt').read_bytes() == (LAND / 'metadata-phase2/Head.lean.txt').read_bytes()
owners = sorted({row['owner'] for row in snapshots['head']['census'].values()})
assert len(owners) == 12 and {r['owner'] for r in snapshots['base']['census'].values()} == set(owners)

# Verify native root matching against the final authored proof-root QA, including privacy/kind.
qa = LAND / 'review-final-source-final'
root_source = qa / 'proof-roots.json'
source_roots = json.loads(root_source.read_text())
assert len(source_roots) == 144 and sum(not row['private'] for row in source_roots) == 66
assert sum(row['private'] for row in source_roots) == 78
expected = {(row['owner'], row['name']): row for row in source_roots}
assert len(expected) == 144
probe = (LAND / 'metadata-final/Head.lean.txt').read_text()
part = probe.split('let requested : List (String × String × Bool) :=', 1)[1].split('let mut rootCount :=', 1)[0]
requested = {(owner, name, priv == 'true') for owner, name, priv in re.findall(
    r'\("([^"]+)", "([^"]+)", (true|false)\)', part)}
assert requested == {(owner, name, row['private']) for (owner, name), row in expected.items()}
root_checks = []
for row in snapshots['head']['root_map']:
    source = expected[(row['owner'], row['source'])]
    compiled = snapshots['head']['census'][row['actual']]
    assert compiled['owner'] == source['owner'] and compiled['private'] == source['private']
    assert source['kind'] in {'lemma', 'theorem'} and compiled['kind'] == 'theorem'
    assert row['actual'] == source['name'] if not source['private'] else row['actual'].endswith('.' + source['name'])
    root_checks.append(dict(source=source, actual_name=row['actual'], compiled=compiled,
                            descendants=len(snapshots['head']['descendants'][row['actual']]) - 1,
                            source_owner_privacy_kind_match=True))
assert {(row['owner'], row['source']) for row in snapshots['head']['root_map']} == set(expected)
write('root-checks.json', root_checks)
(OUT / 'source-proof-roots.json').write_bytes(root_source.read_bytes())

# Source-export classification uses immutable QA source archives and the already reviewed lexical helper.
helper = (OUT / 'declfreeze-helpers.py.txt').read_text()
assert hashlib.sha256(helper.encode()).hexdigest() == 'ef8a784f1ddbf086535d21cadb3221dc720bfe569482e0aa9afcb2503470028c'
namespace = {}
exec(compile(helper, 'trusted-lexical-source-name-helper', 'exec'), namespace)
capture = json.loads((qa / 'capture.json').read_text())
pushed_path = LAND / 'final-tag-adoption/pushed.json'
pushed = json.loads(pushed_path.read_text())
assert pushed['head'] == 'b1f553b315f31b949076e91119473ce4070e7d53'
source_names = {}
source_receipts = []
capture_by_path = {row['path']: row for row in capture['files']}
for label, stage in [('base', 'api'), ('head', 'current')]:
    declarations = {}
    for owner in owners:
        relative = owner.replace('.', '/') + '.lean'
        source = qa / 'snapshots' / stage / (relative + '.txt')
        expected_sha = capture_by_path[relative]['stages'][stage]['sha256']
        assert sha(source) == expected_sha
        if label == 'head': assert sha(source) == pushed['all_source_SHA256'][relative]
        for name, private, text in namespace['chunks'](source.read_text()):
            assert name not in declarations
            declarations[name] = dict(owner=owner, private=private)
        source_receipts.append(dict(label=label, stage=stage, path=str(source.relative_to(ROOT)),
                                     sha256=sha(source), pinned_QA_source=True,
                                     final_pushed_hash_matches=label == 'head'))
    source_names[label] = declarations
write('source-names.json', source_names)
write('source-inputs.json', source_receipts)
for filename in ['freeze-summary.json', 'capture.json']:
    (OUT / ('source-QA-' + filename)).write_bytes((qa / filename).read_bytes())
(OUT / 'pushed-source-pins.json').write_bytes(pushed_path.read_bytes())

source_public = {label: {n for n, r in names.items() if not r['private']} for label, names in source_names.items()}
source_added = source_public['head'] - source_public['base']
source_removed = source_public['base'] - source_public['head']
assert source_added == {'Turing.FinTM.pairMapSndTM', 'Turing.FinTM.pairMapSndTM_computes', 'Turing.FinTM.pairMapSndTM_spaceUsed'}
assert source_removed == {'Turing.' + n for n in ['transferTM_run', 'copyTM_run', 'clearTM_run', 'compareTM_run', 'incrementTM_run_succ', 'incrementTM_run_overflow']}
assert (len(source_public['base']), len(source_public['head'])) == (384, 381)
assert (sum(r['private'] for r in source_names['base'].values()),
        sum(r['private'] for r in source_names['head'].values())) == (1080, 766)


def classify(name, row, label):
    if row['private']: return 'private kernel name; exact-name bookkeeping only'
    if name in source_names[label] and not source_names[label][name]['private']:
        return 'authored source export'
    if name.startswith(('Turing.FinTM.instDecidableEqFwdMapState', 'Turing.FinTM.instDecidableEqA2_MapState')):
        return 'generated deriving-instance family'
    if name in {'Turing.solveSplit.eq_def', 'Turing.solveSplitWith.eq_def'}:
        return 'generated foreign-home equation theorem'
    if name == 'Fin.castLEEmb.congr_simp': return 'generated foreign-home congruence theorem'
    if row['internal']: return 'generated proof/matcher/equation auxiliary'
    return 'generated or synthesized nonprivate constant; no lexical source root'


def distribution(census):
    c = Counter((r['owner'], r['kind'], r['private'], r['internal']) for r in census.values())
    return [dict(owner=o, kind=k, private=p, internal=i, count=n) for (o, k, p, i), n in sorted(c.items())]


def compare(a, b, source_a, source_b):
    A, B = a['census'], b['census']; shared = set(A) & set(B)
    fields = ['owner', 'kind', 'private', 'internal']
    changed = {n: dict(before=A[n], after=B[n], changed_fields=[k for k in fields if A[n][k] != B[n][k]])
               for n in sorted(shared) if any(A[n][k] != B[n][k] for k in fields)}
    added = {n: dict(B[n], classification=classify(n, B[n], source_b)) for n in sorted(set(B) - set(A))}
    removed = {n: dict(A[n], classification=classify(n, A[n], source_a)) for n in sorted(set(A) - set(B))}
    ax_changes = {n: dict(before=a['all_axioms'][n]['axioms'], after=b['all_axioms'][n]['axioms'],
                         before_constant=A[n], after_constant=B[n]) for n in sorted(shared)
                  if set(a['all_axioms'][n]['axioms']) != set(b['all_axioms'][n]['axioms'])}
    return dict(added=added, removed=removed, shared_names=sorted(shared),
                shared_attribute_changes=changed, all_axiom_set_changes=ax_changes,
                added_distribution=distribution(added), removed_distribution=distribution(removed),
                private_identity_limit='Printed kernel names are preserved exactly. No private IDs are normalized, paired as moves or assumed stable; shared names do not establish equal types/bodies or semantic identity.')


delta = compare(snapshots['base'], snapshots['head'], 'base', 'head')
later = compare(snapshots['previous-head'], snapshots['head'], 'head', 'head')
write('delta-base-head.json', delta)
write('delta-previous-head-final.json', later)
for label, d in snapshots.items():
    by_root = {r['actual']: r for r in d['root_map']}
    if by_root:
        # Direct citation differences remain partitioned by source root, descendant and type/value.
        edge_map = defaultdict(list)
        for edge in d['cited']: edge_map[by_root[edge['root']]['source']].append(edge)
        write('citations-' + label + '.json', edge_map)

summary = {}
for label, d in snapshots.items():
    c = d['census']; private = sum(r['private'] for r in c.values())
    nonstandard = {n: dict(c[n], axioms=row['axioms']) for n, row in d['all_axioms'].items()
                   if not set(row['axioms']) <= STANDARD}
    summary[label] = dict(total=len(c), private=private, nonprivate=len(c) - private,
        by_kind=dict(Counter(r['kind'] for r in c.values())), distribution=distribution(c),
        by_owner={o: dict(total=sum(r['owner'] == o for r in c.values()),
                          private=sum(r['owner'] == o and r['private'] for r in c.values()),
                          nonprivate=sum(r['owner'] == o and not r['private'] for r in c.values())) for o in owners},
        census_and_ALLAX_exact=True, PUBLICAX_exact_nonprivate=True,
        nonstandard_axioms=nonstandard,
        all_axiom_distribution=dict(Counter(', '.join(r['axioms']) or '(none)' for r in d['all_axioms'].values())),
        public_axiom_distribution=dict(Counter(', '.join(r['axioms']) or '(none)' for r in d['public_axioms'].values())))
bad = summary['head']['nonstandard_axioms']
assert set(bad) == {'WordRAM.WordSizeComputable.mono', 'WordRAM.wordSizeComputable_logSpace',
                   'WordRAM.wordSizeComputable_of_spaceConstructible'}
assert all(r['owner'] == 'TCSlib.Complexity.RAMSimulation.WordSize' and 'sorryAx' in r['axioms'] for r in bad.values())
all_selected = {n: row for group in snapshots['head']['proof_axioms'].values() for n, row in group.items()}
assert len(all_selected) == 368 and all(set(row['axioms']) <= STANDARD for row in all_selected.values())
assert all(not ('sorryAx' not in r['before'] and 'sorryAx' in r['after']) for r in delta['all_axiom_set_changes'].values())
classes = {direction: dict(Counter(r['classification'] for r in delta[direction].values() if not r['private']))
           for direction in ['added', 'removed']}
summary.update(source_exports=dict(public_before=384, public_after=381, private_before=1080, private_after=766,
                                  added=sorted(source_added), removed=sorted(source_removed)),
    exact_delta=dict(added=len(delta['added']), removed=len(delta['removed']), shared=len(delta['shared_names']),
                     added_private=sum(r['private'] for r in delta['added'].values()),
                     removed_private=sum(r['private'] for r in delta['removed'].values()),
                     nonprivate_classification=classes, shared_attribute_changes=len(delta['shared_attribute_changes']),
                     common_all_axiom_sets_changed=len(delta['all_axiom_set_changes']),
                     common_names_losing_sorryAx=sum('sorryAx' in r['before'] and 'sorryAx' not in r['after'] for r in delta['all_axiom_set_changes'].values())),
    final_selected=dict(source_roots=144, public_roots=66, private_roots=78,
                        compiled_descendants=224, total_selected_constants=368,
                        native_ROOTMAP_source_QA_and_probe_agree=True,
                        all_selected_standard=True,
                        axiom_distribution=dict(Counter(', '.join(r['axioms']) or '(none)' for r in all_selected.values())),
                        cited_records=len(snapshots['head']['cited']),
                        cited_by_part=dict(Counter(r['part'] for r in snapshots['head']['cited'])),
                        cited_owner_counts=dict(Counter(r['owner'] for r in snapshots['head']['cited']))),
    previous_to_final=dict(added=len(later['added']), removed=len(later['removed']),
                           shared=len(later['shared_names']), shared_attribute_changes=len(later['shared_attribute_changes']),
                           common_all_axiom_sets_changed=len(later['all_axiom_set_changes'])),
    pending_three_absent_both_endpoints=True, base_native_run_reused_byte_identically=True,
    scope='Twelve owner modules only; all imported-environment absence claims are restricted to the three executed PENDINGABSENT checks. Source exports differ from generated constants; private kernel names retain their exact spelling.',
    validation_limit='This parser independently checks supplied successful native logs and QA/source pins, not a new Lean run, source-to-olean replay, commit verification or gate clearance.')
write('summary.json', summary)
write('inputs.json', dict(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), inputs=inputs,
    source_QA_root_sha256=sha(root_source), source_pushed_pins_sha256=sha(pushed_path),
    lexical_helper_sha256=hashlib.sha256(helper.encode()).hexdigest(),
    head='b1f553b315f31b949076e91119473ce4070e7d53',
    executed_here='Python data parser and trusted already-reviewed lexical helper only; no Lean, Git, payload script or source mutation.'))
print(json.dumps({k: summary[k] for k in ['source_exports', 'exact_delta', 'final_selected', 'previous_to_final']}, indent=2))
