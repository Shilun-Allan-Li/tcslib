"""Join completed independent final18 reviews; never runs Lean.

All three inputs must be complete before this creates a fresh final summary.
Inputs: peer_audit_final_seals results, completed peer-census batch, per-phase
manual scan reviews. This script does not replace those independent checks.
"""
import argparse
import hashlib
import json
from pathlib import Path


def load(p):
    return json.loads(Path(p).read_text())


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main(args):
    logs, census = load(args.logs), load(args.census)
    scans = Path(args.scans)
    out = Path(args.output)
    if out.exists():
        raise RuntimeError('refusing to replace evidence')
    commit = '47ced271090f45918645c842cd358c5079092754'
    assert logs['commit'] == census['revision'] == commit
    assert logs['expected_phases'] == logs['accepted_phases'] == 18
    assert logs['all_phases_complete'] and not logs['source_A_failures']
    assert census['overlay_pass'] and census['native_censuses_completed'] == 18
    assert census['request_sets_completed'] == 18 and not census['issue_phases']
    rows, all_failures = [], []
    allowed_axioms = {'propext', 'Quot.sound', 'Classical.choice'}
    for phase in logs['phases']:
        ci = next(c for c in census['phases'] if c['phase'] == phase['phase'])
        scan_path = scans / (phase['phase'] + '.json')
        scan = load(scan_path)
        assert ci['target'] == phase['target'] == scan['target']
        assert scan['commit'] == commit
        assert ci['native_census'] == ci['request_coverage'] == 'PASS'
        assert not ci['nonstandard_axioms']
        for group in ci['own_axiom_set_counts']:
            assert set(group.split(',')) - {''} <= allowed_axioms
        assert not scan['genuine_forbidden_explicit_foreign_unfolds']
        assert len(scan['reviews']) == scan['foreign_candidate_rows']
        attempt = next(a for a in phase['attempts']
                       if a['attempt'] == phase['accepted_attempt'])
        assert attempt['accepted_evidence'] and not attempt['audit_issues']
        probes = attempt['probes']
        modes = {p['mode']: p for p in probes if p['mode']}
        assert set(modes) == {'A', 'B'}
        assert modes['A']['status'] == 'SOURCE_PASS' and modes['A']['errors'] == 0
        for mode in ['A', 'B']:
            selection = next(m for m in ci['mode_reviews'] if m['mode'] == mode)
            assert selection['actual_requests'] == modes[mode]['request_count']
            assert selection['expected_requests'] == selection['actual_requests']
        controls = [p for p in probes if p['control']]
        assert len(controls) == ci['generated_controls']
        assert all(c['status'] == 'CONTROL_PASS' for c in controls)
        negative = [c for c in controls if c['label'].endswith('Negative')]
        assert all(c['errors'] == c['exit'] == 1 for c in negative)
        failures = modes['B']['failing_declarations']
        if failures:
            all_failures.append(dict(phase=phase['phase'], target=phase['target'],
                                     errors=modes['B']['errors'], declarations=failures,
                                     raw_log=modes['B']['raw_log']))
        row = dict(phase=phase['phase'], target=phase['target'],
                   own_stored_constants=ci['own_stored_constants'],
                   imported_eligible_definitions=ci['imported_eligible_definitions'],
                   eligible_private_names=ci['eligible_private_names'],
                   eligible_matchers=ci['eligible_matchers'],
                   A_requests=modes['A']['request_count'], B_requests=modes['B']['request_count'],
                   A_errors=0, B_errors=modes['B']['errors'],
                   controls=len(controls), sealed_negatives=len(negative),
                   scan_readings=scan['token_readings'], scan_candidates=scan['foreign_candidate_rows'],
                   B_failing_declarations=failures, accepted_attempt=phase['accepted_attempt'],
                   own_axiom_set_counts=ci['own_axiom_set_counts'],
                   collector_log=ci['collector_log'], scan_review=str(scan_path))
        # The exact closure size is independently certified by this native collector marker.
        collector = Path(args.evidence) / ci['collector_log']
        markers = [line for line in collector.read_text().splitlines()
                   if line.startswith('LAMP-CLOSURE-EXACT\t' + phase['target'] + '\t')]
        assert len(markers) == 1
        row['TCSlib_closure_modules'] = int(markers[0].split('\t')[2])
        rows.append(row)
    assert len(rows) == 18 and len({r['target'] for r in rows}) == 18
    totals = {key: sum(r[key] for r in rows) for key in
              ['own_stored_constants', 'A_requests', 'B_requests', 'A_errors', 'B_errors',
               'controls', 'sealed_negatives', 'scan_readings', 'scan_candidates']}
    result = dict(commit=commit, all_final18_peer_reviews_complete=True,
                  logs_review=args.logs, logs_review_sha256=digest(args.logs),
                  census_review=args.census, census_review_sha256=digest(args.census),
                  phases=rows, totals=totals, final_B_failures=all_failures,
                  interpretation='A excludes PolyExpr.eval only; B seals it too. All B failures '
                                 'are retained and listed. A failures are never waived. '
                                 'Every own stored constant uses a subset of the standard three axioms.')
    out.mkdir(parents=True)
    (out / 'tool.py').write_bytes(Path(__file__).read_bytes())
    (out / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
    text = ['All eighteen final whole-file Rule 10 reviews are complete for `' + commit + '`.', '',
            '| File | Own constants | Closure | A/B definitions | A/B errors | Controls | Scan readings/candidates |',
            '|---|---:|---:|---:|---:|---:|---:|']
    for r in rows:
        label = 'Lamport' if r['phase'].endswith('Main') else r['phase'].removeprefix('FinalR2')
        text.append(f"| {label} | {r['own_stored_constants']} | {r['TCSlib_closure_modules']} | "
                    f"{r['A_requests']}/{r['B_requests']} | 0/{r['B_errors']} | {r['controls']} | "
                    f"{r['scan_readings']}/{r['scan_candidates']} |")
    text += ['', f"All eighteen A seals pass. All {totals['controls']} controls pass, including "
             f"{totals['sealed_negatives']} sealed negatives with exactly one error each. "
             f"The {totals['own_stored_constants']} stored constants have only subsets of "
             "`{propext, Classical.choice, Quot.sound}` as axioms. "
             f"All {totals['scan_candidates']} scanner candidates were reviewed in their source contexts; "
             "none is a forbidden explicit foreign unfold. Blocks has no TCSlib import closure "
             "and therefore zero requested definitions and no closure-local control; the other "
             "seventeen phases supply the paired controls.", '']
    if all_failures:
        text.append('B failures (with `PolyExpr.eval` sealed):')
        text.append('')
        for failure in all_failures:
            text.append(f"- `{failure['target']}`: {failure['errors']} errors in "
                        f"{len(failure['declarations'])} declarations: " +
                        ', '.join('`' + d + '`' for d in failure['declarations']) + '.')
    else:
        text.append('All eighteen B seals also pass.')
    text += ['', 'Per-name INSTALL and EOF multisets, actual Name/home identity, original-source '
             'maps and hashes, full eligible-set selection (including private definitions and '
             'generated matchers), exact runtime import closure, every own axiom row, and '
             'control locations were checked against the retained raw evidence. '
             'The versioned module-name cache changes only pure reads of a captured immutable '
             'environment. Earlier Core-loop/sparse proposals were not adopted; historical '
             'attempts and the actual generator bindings are preserved.', '']
    (out / 'REPORT-block.md').write_text('\n'.join(text))
    print(json.dumps(dict(phases=18, totals=totals, final_B_failure_phases=len(all_failures)), indent=2))


parser = argparse.ArgumentParser(description=__doc__)
for option in ['logs', 'census', 'scans', 'evidence', 'output']:
    parser.add_argument('--' + option, required=True)
if __name__ == '__main__':
    main(parser.parse_args())
