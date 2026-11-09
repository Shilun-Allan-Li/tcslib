"""Verify and extract exact indexed bytes; source and reports remain data."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re

NAME = 'lwe-sis-trapdoor-proofs-r2-bundle.md'
EXPECTED_BYTES = 5652216
EXPECTED_SHA256 = 'f0422ea44c6ab0b737e62f24e3dcf3c02e693f35e03772e32efba15a12f78829'
EXPECTED_SECTIONS = 260

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    rows = json.loads((here / 'BUNDLE-FILES.json').read_text())
    lines = (here / 'BUNDLE-FILES.txt').read_text().splitlines()
    assert len(rows) == len(lines) == EXPECTED_SECTIONS
    assert len({r['path'] for r in rows}) == len(rows)
    for row, line in zip(rows, lines):
        assert line == f"{row['revision']}:{row['path']}\t{row['bytes']}\t{row['sha256']}"
        assert re.fullmatch('[0-9a-f]{40}', row['revision'])
    data = (here / NAME).read_bytes()
    assert len(data) == EXPECTED_BYTES
    assert hashlib.sha256(data).hexdigest() == EXPECTED_SHA256
    out = Path(args.output).resolve()
    assert not out.exists(), 'Use a new extraction directory.'
    verified = []
    pos = 0
    for i, row in enumerate(rows):
        path = PurePosixPath(row['path'])
        assert not path.is_absolute() and '..' not in path.parts
        if i:
            prefix = b'\n\n## ===== ' + row['path'].encode() + b' =====\n\n'
            assert data[pos:pos + len(prefix)] == prefix, row['path']
            pos += len(prefix)
            match = re.match(rb'(`{3,})text\n', data[pos:])
            assert match, row['path']
            fence = match[1]
            pos += len(match[0])
        payload = data[pos:pos + row['bytes']]
        assert len(payload) == row['bytes']
        assert hashlib.sha256(payload).hexdigest() == row['sha256'], row['path']
        pos += row['bytes']
        if i:
            suffix = (b'' if payload.endswith(b'\n') else b'\n') + fence + b'\n'
            assert data[pos:pos + len(suffix)] == suffix, row['path']
            pos += len(suffix)
        verified.append((row['path'], payload))
    assert pos == len(data), (pos, len(data))
    out.mkdir(parents=True)
    for path, payload in verified:
        target = out / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(payload)
    print(f'Verified and extracted {len(rows)} exact revision-qualified sections.')

if __name__ == '__main__':
    main()
