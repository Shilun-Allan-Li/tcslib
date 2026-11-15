"""Check final source scope, width, size, attributes, and source provenance."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

base = '01de2d8baed9113e4a099e13c5d50c81e6dbc66f'
tip = '5e12a169e671dc16b6766e21067b79c16835af67'
def git(*args):
    return subprocess.check_output(['git', *args])

assert git('rev-parse', 'HEAD').decode().strip() == tip
paths = git('diff', '--name-only', base, tip).decode().splitlines()
allowed = {
    'TCSlib/Complexity/ClassP/DTIME.lean',
    'TCSlib/Complexity/Randomized/Classes.lean',
    'TCSlib/Complexity/Randomized/Build/IterateFind.lean',
    'TCSlib/Complexity/Randomized/SeedMajority.lean',
    'TCSlib/Cryptography/Randomness/Derandomization.lean',
}
rows = []
for path in paths:
    assert path in allowed or path.startswith((
        'TCSlib/Complexity/Randomized/SeedMajority/',
        'TCSlib/Cryptography/Randomness/Derandomization/'))
    source = Path(path).read_bytes()
    assert source == git('show', tip + ':' + path), path
    lines = source.decode().splitlines()
    exists = subprocess.run(['git', 'cat-file', '-e', base + ':' + path],
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
    old = git('show', base + ':' + path).decode() if exists else ''
    long = [(i + 1, len(line)) for i, line in enumerate(lines) if len(line) > 100]
    assert not long, (path, long)
    size_exception = path == 'TCSlib/Complexity/Randomized/Classes.lean'
    assert len(lines) <= 1000 or size_exception, path
    diff = git('diff', '--unified=0', base, tip, '--', path).decode()
    additions = [line[1:] for line in diff.splitlines()
                 if line.startswith('+') and not line.startswith('+++')]
    assert not any(re.search(r'@\[[^\]]*\bsimp\b', line) for line in additions), path
    assert not any(re.match(r'import Mathlib\s*$', line) for line in lines), path
    row = dict(path=path, base_lines=len(old.splitlines()), final_lines=len(lines),
               maximum_width=max(map(len, lines)), over_100_columns=long,
               size_exception='SR-01 specifically approved' if size_exception else None,
               source_sha256=hashlib.sha256(source).hexdigest())
    rows.append(row)
    print(f'{path}: {row["base_lines"]}->{len(lines)} lines; '
          f'max width={row["maximum_width"]}; '
          f'{"approved inherited size exception" if size_exception else "PASS"}')
assert len(rows) == 15
out = Path('evidence/source-audit')
out.mkdir(exist_ok=True)
(out / 'results.json').write_text(json.dumps(dict(base=base, tip=tip, files=rows), indent=2) + '\n')
print('SOURCE AUDIT PASS: 15 permitted files; widths <= 100; sizes <= 1000 except approved SR-01')
