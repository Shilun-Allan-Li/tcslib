"""Check exact receipts and paired-control identities; does not run Lean."""
from pathlib import Path
import collections, hashlib, json, re

p = Path(__file__).resolve().parent
labels = ['convention-only', 'convention-only-v2', 'convention-only-v3',
          'controls-unsealed', 'controls-sealed']
receipts = {}
for label in labels:
    r = json.loads((p / (label + '.json')).read_text())
    source = Path(r['source'])
    output = p / (label + '.out')
    assert hashlib.sha256(source.read_bytes()).hexdigest() == r['input_sha256']
    assert hashlib.sha256(output.read_bytes()).hexdigest() == r['output_sha256']
    assert r['watched_before'] == r['watched_after']
    actual_errors = len(re.findall(r'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:', output.read_text()))
    assert actual_errors == r['errors']
    receipts[label] = {'exit': r['exit'], 'errors': r['errors']}
assert receipts == {
    'convention-only': {'exit': 1, 'errors': 3},
    'convention-only-v2': {'exit': 0, 'errors': 0},
    'convention-only-v3': {'exit': 0, 'errors': 0},
    'controls-unsealed': {'exit': 0, 'errors': 0},
    'controls-sealed': {'exit': 1, 'errors': 4}}

expected = collections.Counter((n, mode) for n in ['Turing.solveSplit', 'Turing.solveSplitWith']
                               for mode in ['point', 'abstract'])
for label, state in [('controls-unsealed', 'PASS'), ('controls-sealed', 'FAIL')]:
    s = (p / (label + '.out')).read_text()
    rows = re.findall(r'(?m)^CONTROL\|([^|]+)\|([^|]+)\|(PASS|FAIL)(?:\|.*)?$', s)
    assert len(rows) == 4 and all(row[2] == state for row in rows)
    assert collections.Counter((n, mode) for n, mode, _ in rows) == expected
    if state == 'PASS':
        assert s.count('|kernelChecked=') == 4
    else:
        errors = re.findall(r'error: RFL_CONTROL\|([^|]+)\|([^|]+)\|', s)
        assert collections.Counter(errors) == expected

s = (p / 'convention-only-v3.out').read_text()
for n in ['Turing.solveSplit', 'Turing.solveSplitWith']:
    assert f'BEFORE|{n}.eq_def|containsDefault=false|containsRealizations=false|containsOnBranch=false|find=false|reserved=true|' in s
    assert f'AFTER_EQDEF|{n}.eq_def|kind=theorem|containsDefault=false|containsRealizations=true|containsOnBranch=false|moduleIdxOwner=none|currentMain=_stdin|private=false|internal=false|simp=false|unfold=false|defeq=true' in s
    assert f'OPAQUE_AFTER_CONSUMERS|{n}|irreducible=true' in s
assert 'primitivesImported=false' in s
assert not re.search(r'^TCSLIB_IMPORT\|.*Primitives$', s, re.M)
assert 'sorryAx' not in s

result = {'lean_invocations': len(labels), 'receipts': receipts,
          'paired_definitions': 2, 'positive_controls': 4, 'negative_controls': 4,
          'exact_control_identities_and_multiplicities': True,
          'primary_probe_passed': True, 'foreign_opacity_retained': True,
          'convention_source_and_snapshot_olean_unchanged': True}
(p / 'checked-evidence.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
