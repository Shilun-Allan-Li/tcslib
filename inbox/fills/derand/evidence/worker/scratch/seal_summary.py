"""Select exact-final-source canonical seal evidence; preserve all older attempts."""
import importlib.util
import json
from pathlib import Path

spec = importlib.util.spec_from_file_location('derand_seals', 'evidence/tools/make_seals.py')
seals = importlib.util.module_from_spec(spec)
spec.loader.exec_module(seals)
shared = 'TCSlib/Complexity/'
crypto = 'TCSlib/Cryptography/Randomness/'
selection = {
 shared+'ClassP/DTIME.lean': 'checkpoint1-focus-v2',
 shared+'Randomized/Classes.lean': 'checkpoint1-focus-v2',
 shared+'Randomized/Build/IterateFind.lean': 'harvest-reader-final',
 shared+'Randomized/SeedMajority.lean': 'final-facades',
 crypto+'Derandomization.lean': 'final-facades',
 shared+'Randomized/SeedMajority/Words.lean': 'host-final',
 shared+'Randomized/SeedMajority/State.lean': 'state-doc-final',
 shared+'Randomized/SeedMajority/Enumeration.lean': 'host-final',
 shared+'Randomized/SeedMajority/Envelope.lean': 'host-final',
 crypto+'Derandomization/RootSchedule.lean': 'doc-final',
 crypto+'Derandomization/AdviceGap.lean': 'doc-final',
 crypto+'Derandomization/Expanded.lean': 'consumer-filled',
 crypto+'Derandomization/CoinGap.lean': 'consumer-filled',
 crypto+'Derandomization/Majority.lean': 'final-facades',
 crypto+'Derandomization/TimeBound.lean': 'consumer-filled',
}
base_path = Path('/Users/seyoonr/.codex/worktrees/derand/tcslib-exchange/evidence/seals/base/results.jsonl')
base_rows = [json.loads(line) for line in base_path.read_text().splitlines()]
result = []
for source, phase in selection.items():
    folder = Path('evidence/seals') / phase
    rows = [json.loads(line) for line in (folder / 'results.jsonl').read_text().splitlines()
            if json.loads(line)['source'] == source]
    assert len(rows) == 4, (source, phase, len(rows))
    for row in rows:
        assert row['harness_valid'], row
        expected, _, _ = seals.prepare(Path(source).read_text(), row['label'], row['mode'], row['coe'])
        assert Path(row['probe']).read_text() == expected, ('Final source mismatch', source, phase)
        baseline = next((item for item in base_rows if item['source'] == source and
                         item['mode'] == row['mode'] and item['coe'] == row['coe']), None)
        old_errors = len(baseline['errors']) if baseline else None
        expected_errors = 20 if source.endswith('/Build/IterateFind.lean') else 0
        assert len(row['errors']) == expected_errors, row
        result.append(dict(source=source, phase=phase, mode=row['mode'], coe=row['coe'],
            base_errors=old_errors, final_errors=len(row['errors']),
            diagnostic_lines=[error['source_line'] for error in row['errors']],
            requests=row['requests'], harness_valid=True, exact_final_source=True,
            log=row['probe'][:-5]+'.log'))
folder = Path('evidence/seals/summary')
folder.mkdir(parents=True, exist_ok=True)
(folder / 'final-canonical.json').write_text(json.dumps(result, indent=2) + '\n')
table = '| File | Variant | Base diagnostics | Final diagnostics | Status |\n|---|---|---:|---:|---|\n'
for row in result:
    variant = row['mode'] + (' coe' if row['coe'] else ' strict')
    old = row['base_errors'] if row['base_errors'] is not None else 'new file'
    status = 'EX-02: 11 inherited + 9 E1' if row['final_errors'] else 'PASS'
    table += f'| `{row["source"]}` | {variant} | {old} | {row["final_errors"]} | {status} |\n'
(folder / 'final-canonical.md').write_text(table)
print(f'CANONICAL SEAL COVERAGE PASS: {len(selection)} exact-final-source files, {len(result)} valid variants')
print('Rule 10 disposition: 56 passing variants; four harvest variants retain 11 inherited + 9 E1 diagnostics (EX-02).')
