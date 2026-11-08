#!/usr/bin/env python3
"""Read-only Gate 06B byte/provenance verification. Usage: script REPOSITORY."""
import csv
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import zipfile

EXCHANGE = '5928e06c02b382b63b9b384db89d0458b520f351'
HEAD = '3f6db40e1688c4a0bb922c9575dd3bd2157a650b'
RECORDS = 'c81baa7712ab1b43357276ef5df138d02616c9d0'
BASE = 'eee107e92a7db11f1f8c98a5c2867304f57ddc54'


def main():
    repo = Path(sys.argv[1]).resolve()
    git = lambda *args: subprocess.check_output(['git', '-C', str(repo), *args])
    assert git('rev-parse', 'HEAD').decode().strip() == EXCHANGE
    root = repo / 'outbox/gates'
    checksums = {}
    for folder in ('06B-r1-gate', '06-common-r1-gate'):
        checksums[folder] = {}
        for line in (root / folder / 'SHA256SUMS').read_text().splitlines():
            expected, filename = line.split('  ', 1)
            raw = (root / folder / filename).read_bytes()
            actual = hashlib.sha256(raw).hexdigest()
            assert actual == expected, filename
            assert raw == git('show', f'{EXCHANGE}:outbox/gates/{folder}/{filename}')
            checksums[folder][filename] = actual
    manifest = json.loads((root / '06B-r1-gate/gate06B-source-manifest.json').read_text())
    assert manifest['head'] == HEAD and manifest['base'] == BASE
    source = (root / '06B-r1-gate/gate06B-source-bundle.md').read_bytes()
    for row in manifest['files']:
        header = f"## ===== {row['path']} =====\n\n".encode()
        assert source.count(header) == 1
        start = source.index(header) + len(header)
        raw = source[start:start + row['bytes']]
        assert hashlib.sha256(raw).hexdigest() == row['sha256']
        assert raw == git('show', f"{row['revision']}:{row['path']}")
    records_bundle = (root / '06B-r1-gate/gate06B-records-bundle.md').read_bytes()
    record_count = 0
    for line in (root / '06B-r1-gate/gate06B-records-bundle-FILES.txt').read_text().splitlines():
        rev, path = line.split(' ', 1)
        assert rev == RECORDS
        raw = git('show', f'{rev}:{path}')
        header = f'## ===== {path} =====\n\n'.encode()
        assert records_bundle.count(header) == 1
        start = records_bundle.index(header) + len(header)
        assert records_bundle[start:start + len(raw)] == raw
        record_count += 1
    rows = list(csv.DictReader((root / '06-common-r1-gate/ZIP-CONTENTS.tsv').open(), delimiter='\t'))
    with zipfile.ZipFile(root / '06-common-r1-gate/gate06-common-evidence.zip') as archive:
        assert archive.testzip() is None
        assert set(archive.namelist()) == {r['path'] for r in rows}
        for row in rows:
            raw = archive.read(row['path'])
            assert len(raw) == int(row['bytes'])
            assert hashlib.sha256(raw).hexdigest() == row['sha256']
            assert raw == git('show', f"{row['revision']}:{row['path']}")
        final_index = archive.read('briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/FINAL-EVIDENCE.md')
        assert hashlib.sha256(final_index).hexdigest() == '0e011edc90d469d1b3dd1156a74f6f7856f756e15e085343486a232ea24aa73b'
    assert not git('diff', BASE, RECORDS, '--', 'TCSlib', 'TCSlib.lean')
    assert not git('status', '--porcelain')
    print(json.dumps({'status': 'PASS', 'exchange': EXCHANGE, 'lean': HEAD,
                      'records': RECORDS, 'comparison_base': BASE,
                      'checksums': checksums, 'source_sections_verified': len(manifest['files']),
                      'records_sections_verified': record_count,
                      'archive_members_verified': len(rows),
                      'comparison_base_records_TCSlib_equal': True,
                      'checkout_clean': True, 'lean_elaboration_run': False}, indent=2))


if __name__ == '__main__':
    main()
