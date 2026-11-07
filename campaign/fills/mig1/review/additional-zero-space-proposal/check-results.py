"""Verify completed bounded probes and control multiplicity, without running Lean."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

OUT = Path(__file__).resolve().parent

def controls(source, text, code, want):
    lines = source.read_text().splitlines()
    starts = [i + 1 for i, line in enumerate(lines) if line.startswith('example')]
    ends = starts[1:] + [len(lines) + 1]
    diagnostics = list(re.finditer(r'^([^ \n][^\n]*?):(\d+):(\d+): error: ([^\n]+)', text, re.M))
    counts = Counter()
    stray, other = [], []
    expected = 'Tactic `rfl` failed: The left-hand side'
    for diagnostic in diagnostics:
        line = int(diagnostic[2])
        start = next((s for s, e in zip(starts, ends) if s <= line < e), None)
        if start is None:
            stray.append(line)
        else:
            counts[start] += 1
        if diagnostic[4] != expected:
            other.append(diagnostic[4])
    bad = [dict(line=s, count=counts[s]) for s in starts if counts[s] != want]
    accepted = len(starts) == 8 and not (bad or stray or other) and (code != 0 if want else code == 0)
    return dict(examples=len(starts), diagnostics=len(diagnostics), exit=code,
                expected_errors_per_example=want, bad_examples=bad,
                stray=stray, other_error_kinds=other, accepted=accepted)

def main():
    context = json.loads((OUT / 'context.json').read_text())
    receipts = {}
    expected = {'Availability', 'Encoding-home', 'Build-Primitives-home', 'Consumers',
                'Controls-unsealed', 'Controls-sealed'}
    for path in sorted(OUT.glob('*-run.json')):
        row = json.loads(path.read_text())
        stem = path.name.removesuffix('-run.json')
        source, log = OUT / (stem + '.lean.txt'), OUT / (stem + '.out')
        assert hashlib.sha256(source.read_bytes()).hexdigest() == row['input_sha256']
        assert hashlib.sha256(log.read_bytes()).hexdigest() == row['output_sha256']
        request = json.loads((OUT / (stem + '-request.json')).read_text())
        assert request['input_sha256'] == row['input_sha256']
        assert request['command'] == row['command']
        assert row['snapshot'] == context['snapshot'] and row['local_slots'] == '3'
        receipts[stem] = row
    assert set(receipts) == expected
    for stem in expected - {'Controls-sealed'}:
        assert receipts[stem]['exit'] == receipts[stem]['errors'] == 0
    assert receipts['Controls-sealed']['exit'] == 1 and receipts['Controls-sealed']['errors'] == 8
    positive = controls(OUT / 'Controls-unsealed.lean.txt',
                        (OUT / 'Controls-unsealed.out').read_text(),
                        receipts['Controls-unsealed']['exit'], 0)
    source = OUT / 'Controls-sealed.lean.txt'
    text = (OUT / 'Controls-sealed.out').read_text()
    negative = controls(source, text, receipts['Controls-sealed']['exit'], 1)
    assert positive['accepted'] and negative['accepted']
    starts = list(re.finditer(r'^[^ \n][^\n]*?:\d+:\d+: error:', text, re.M))
    first = text[starts[0].start():starts[1].start()]
    duplicate = text + '\n' + first
    missing = text[:starts[0].start()] + text[starts[1].start():]
    checker_negatives = dict(duplicate=controls(source, duplicate, 1, 1),
                             missing=controls(source, missing, 1, 1),
                             exit_zero=controls(source, text, 0, 1))
    assert all(not r['accepted'] for r in checker_negatives.values())
    (OUT / 'Controls-checker-duplicate.out').write_text(duplicate)
    (OUT / 'Controls-checker-missing.out').write_text(missing)
    availability = (OUT / 'Availability.out').read_text()
    assert all('REQUESTED ' + name + ': ABSENT' in availability for name in context['proposed_names'])
    axioms = {}
    for stem in ['Encoding-home', 'Build-Primitives-home', 'Consumers']:
        rows = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",
                          (OUT / (stem + '.out')).read_text(), re.M)
        assert len(rows) == (2 if stem == 'Consumers' else 1)
        assert all(set(a.split(', ')) <= {'propext', 'Classical.choice', 'Quot.sound'} for n, a in rows)
        axioms[stem] = {name: ax.split(', ') for name, ax in rows}
    for name, sha in context['source_sha256'].items():
        assert hashlib.sha256((Path(context['api_worktree']) / name).read_bytes()).hexdigest() == sha
    for name, sha in context['compiled_sha256'].items():
        path = Path(context['snapshot']) / (name.removesuffix('.lean') + '.olean')
        assert hashlib.sha256(path.read_bytes()).hexdigest() == sha
    assert not list(OUT.rglob('*.lean')) and not list(OUT.rglob('*.pyc'))
    result = dict(unapproved=True, implementation=False,
                  requested_names_absent=True,
                  two_owner_context_proofs_pass_with_spaceUsed_initCfg_sealed=True,
                  two_hypothetical_consumers_pass_with_both_machines_spaceUsed_initCfg_sealed=True,
                  positive_controls=positive, negative_controls=negative,
                  checker_negative_tests=checker_negatives,
                  checker_negative_tests_are_synthetic_not_Lean_runs=True,
                  axioms=axioms, all_receipt_hashes_match=True,
                  owner_source_and_compiled_module_hashes_unchanged=True,
                  receipts={name: {k: r[k] for k in ['exit', 'errors', 'seconds']} for name, r in receipts.items()},
                  limitations=['Consumer interfaces are theorem parameters, not compiled new library constants.',
                               'No integrated Catalog repair, source change, gate acceptance or new API approval.'])
    (OUT / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
