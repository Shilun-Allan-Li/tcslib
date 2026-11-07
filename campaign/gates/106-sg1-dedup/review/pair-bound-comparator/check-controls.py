"""Check exact per-definition control multiplicities and exercise rejection cases."""
from collections import Counter
from copy import deepcopy
from pathlib import Path
import json
import re

out = Path(__file__).resolve().parent
names = (out / 'control-definitions.txt').read_text().splitlines()
expected = {(name, mode) for name in names for mode in ('point', 'abstract')}


def check(positive, negative, positive_receipt, negative_receipt):
    for text, wanted in ((positive, 'PASS'), (negative, 'FAIL')):
        rows = [line.split('|') for line in text.splitlines() if line.startswith('CONTROL|')]
        counts = Counter((row[1], row[2]) for row in rows)
        assert counts == Counter({key: 1 for key in expected}), 'control multiplicity mismatch'
        assert all(row[3] == wanted for row in rows), 'unexpected control outcome'
        if wanted == 'PASS':
            assert all(len(row) == 5 and row[4].startswith('kernelChecked=') for row in rows)
            assert len({row[4] for row in rows}) == len(expected), 'duplicate kernel proof name'
    error_ids = Counter(re.findall(r'RFL_CONTROL\|([^|\n]+)\|(point|abstract)\|', negative))
    assert error_ids == Counter({key: 1 for key in expected}), 'diagnostic multiplicity mismatch'
    error_pattern = r'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:'
    assert len(re.findall(error_pattern, positive)) == 0
    assert len(re.findall(error_pattern, negative)) == len(expected)
    assert (positive_receipt['exit'], positive_receipt['errors']) == (0, 0)
    assert (negative_receipt['exit'], negative_receipt['errors']) == (1, len(expected))


positive = (out / 'Controls-unsealed-v1.out').read_text()
negative = (out / 'Controls-sealed-v1.out').read_text()
pr = json.loads((out / 'Controls-unsealed-v1-run.json').read_text())
nr = json.loads((out / 'Controls-sealed-v1-run.json').read_text())
check(positive, negative, pr, nr)
ids = re.findall(r'RFL_CONTROL\|[^|\n]+\|(?:point|abstract)\|', negative)
negative_cases = {}
cases = {
    'duplicate_diagnostic_identity_preserving_count':
        (negative.replace(ids[0], ids[1], 1), deepcopy(nr)),
    'missing_diagnostic_identity':
        (negative.replace(ids[0], 'REMOVED_DIAGNOSTIC|', 1), deepcopy(nr)),
    'unexpected_positive_outcome':
        (negative.replace('|point|FAIL', '|point|PASS', 1), deepcopy(nr)),
    'zero_negative_exit': (negative, {**nr, 'exit': 0}),
}
for name, (changed, receipt) in cases.items():
    try:
        check(positive, changed, pr, receipt)
    except AssertionError:
        negative_cases[name] = 'rejected'
    else:
        raise AssertionError('checker accepted invalid evidence: ' + name)
result = {
    'definitions': len(names),
    'pointwise_and_abstracted_pairs': len(expected),
    'positive_exit': pr['exit'],
    'negative_exit': nr['exit'],
    'negative_lean_diagnostics': nr['errors'],
    'all_exact_multiplicities_match': True,
    'checker_negative_cases': negative_cases,
}
(out / 'control-check.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
