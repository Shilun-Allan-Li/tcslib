"""Compare the two preserved native imported-environment type-probe logs."""

import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
E = HERE / 'evidence'


def main():
    sets, logs = {}, []
    for label in ['baseline', 'current']:
        runs = json.loads((E / ('type-probe-' + label) / 'checks.json').read_text())
        assert len(runs) == 1 and runs[0]['exit_code'] == runs[0]['error_lines'] == 0
        assert runs[0]['fresh_olean']
        log = ROOT / runs[0]['log']; items = {}
        for line in log.read_text().splitlines():
            if line.startswith('RAW_TYPE|'):
                name, levels, typ = json.loads(line.split('|', 1)[1])
                assert name not in items
                items[name] = (levels, typ)
        sets[label] = items
        logs.append(dict(label=label, log=str(log.relative_to(ROOT)),
            sha256=hashlib.sha256(log.read_bytes()).hexdigest(), constants=len(items),
            seconds=runs[0]['seconds']))
    assert len(sets['baseline']) == 575 and len(sets['current']) == 589
    assert sets['baseline'].keys() <= sets['current'].keys()
    assert all(sets['current'][n] == value for n, value in sets['baseline'].items())
    rows = [dict(name=n, level_params_sha256=hashlib.sha256(v[0].encode()).hexdigest(),
        type_expr_repr_sha256=hashlib.sha256(v[1].encode()).hexdigest())
        for n, v in sorted(sets['baseline'].items())]
    (E / 'elaborated-type-identities.json').write_text(json.dumps(rows, indent=2) + '\n')
    receipt = dict(baseline_source='17b2a282b545c6ebca3fccc88d518d18ae78f485',
        current_source=(E / 'source-pin.txt').read_text().strip(),
        existing_owned_constants_compared=575, current_owned_constants=589,
        all_existing_level_params_and_type_expr_representations_exactly_equal=True,
        method='Compare exact reprStr values of ConstantInfo.levelParams and ConstantInfo.type from separate imported object environments; SHA-256 each matching representation.',
        baseline_objects_independently_rebuilt=False,
        baseline_objects_origin='This same chat archived audited statement final objects, APFS copy preserved separately.',
        whole_library_type_certificate=False, native_probes=logs)
    (E / 'type-probe-comparison.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('Exact level/type representations preserved for all 575 baseline owned constants.')


if __name__ == '__main__':
    main()
