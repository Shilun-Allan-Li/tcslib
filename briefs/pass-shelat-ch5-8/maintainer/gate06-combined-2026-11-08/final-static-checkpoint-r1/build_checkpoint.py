#!/usr/bin/env python3
"""Own nonnative archive writer; all source programs are opaque input bytes.

Writes only this fresh sibling checkpoint. No imports of source/input programs,
subprocesses, Lean, Git, cache, or build commands. Never overwrites an output.
"""
from pathlib import Path, PurePosixPath
from collections import Counter
import csv
import datetime
import hashlib
import io
import json
import stat
import sys
import zipfile

sys.dont_write_bytecode = True
ROOT = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
BASE = ROOT / '.lake/ps-maintainer/gate06-combined-20261108'
SOURCE = BASE / 'source-review/final-static-r1'
MEMO = BASE / 'simp-ruling-request-r1.md'
OUT = BASE / 'final-static-checkpoint-r1'
SOURCE_MANIFEST = 'ffeb493b1390f5a283316d339ecd534b49f2b1565ebe49a6141c9a41f37093ad'
SOURCE_REPORT = '24a3894aaaf4fa4f1df67da375018b819afd38e4645aeded489d9bb2046749ba'
MEMO_SHA = '7a6c6448fbcf3f1f00baf2c354e4d47ca32a44213f02cb21e14e1bc6a1c4b4cc'
CHUNK = 1 << 20


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encode(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()


def identity(s):
    return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, stat.S_IMODE(s.st_mode))


def digest_file(path):
    h = hashlib.sha256()
    count = 0
    with path.open('rb') as stream:
        while chunk := stream.read(CHUNK):
            h.update(chunk)
            count += len(chunk)
    return count, h.hexdigest()


def write_new(name, raw):
    with (OUT / name).open('xb') as stream:
        stream.write(raw)
    return {'path': name, 'bytes': len(raw), 'sha256': sha(raw)}


def snapshot():
    need(SOURCE.is_dir() and not SOURCE.is_symlink(), 'source root must be ordinary directory')
    inputs = []
    for path in sorted(SOURCE.rglob('*')):
        s = path.lstat()
        need(not stat.S_ISLNK(s.st_mode), 'source symlink forbidden')
        if stat.S_ISDIR(s.st_mode):
            continue
        need(stat.S_ISREG(s.st_mode), 'nonordinary source file')
        rel = path.relative_to(SOURCE).as_posix()
        inputs.append((path, 'final-static-r1/' + rel, 'FROZEN_FINAL_STATIC_SOURCE_REVIEW'))
    inputs.append((MEMO, 'pending-ruling-memo/' + MEMO.name, 'PENDING_USER_RULING_MEMO_NOT_APPROVAL'))
    rows = []
    for path, zip_path, category in inputs:
        s = path.lstat()
        need(stat.S_ISREG(s.st_mode) and not path.is_symlink(), 'input must be ordinary file')
        need(path.suffix not in {'.olean', '.ilean'}, 'native object forbidden')
        need(not zip_path.startswith('/') and all(p not in {'..', '.', ''} for p in zip_path.split('/')), 'unsafe archive path')
        count, digest = digest_file(path)
        need(count == s.st_size and identity(path.lstat()) == identity(s), 'input changed during full read')
        rows.append({'source_path': str(path), 'zip_path': zip_path, 'category': category,
                     'bytes': count, 'sha256': digest, 'stat_identity': identity(s)})
    return sorted(rows, key=lambda row: row['zip_path'])


def fingerprint(rows):
    return sha(''.join(f"{r['zip_path']}\t{r['bytes']}\t{r['sha256']}\n" for r in rows).encode())


def validate_bindings(rows):
    by_path = {r['source_path']: r for r in rows}
    need(by_path[str(SOURCE / 'manifest.json')]['sha256'] == SOURCE_MANIFEST, 'source manifest changed')
    need(by_path[str(SOURCE / 'report.json')]['sha256'] == SOURCE_REPORT, 'source report changed')
    need(by_path[str(MEMO)]['sha256'] == MEMO_SHA, 'pending memo changed')
    manifest = json.loads((SOURCE / 'manifest.json').read_bytes())
    report = json.loads((SOURCE / 'report.json').read_bytes())
    expected = {}
    for row in manifest['files']:
        rel = PurePosixPath(row['path'])
        need(not rel.is_absolute() and all(p not in {'.', '..', ''} for p in row['path'].split('/')), 'unsafe manifest leaf')
        need(row['path'] not in expected, 'duplicate manifest leaf')
        expected[row['path']] = row
    need(len(expected) == manifest['file_count'] == 2244, 'manifest leaf count differs')
    actual = {str(Path(r['source_path']).relative_to(SOURCE)): r for r in rows
              if r['category'] == 'FROZEN_FINAL_STATIC_SOURCE_REVIEW'}
    need(set(actual) == set(expected) | {'manifest.json'}, 'manifest does not cover exact source directory')
    for rel, row in expected.items():
        need((actual[rel]['bytes'], actual[rel]['sha256']) == (row['bytes'], row['sha256']), 'manifest leaf hash mismatch')
    attrs = report['pending_policy']['attributes']
    need(len(attrs) == 6 and all(r['status'] == 'PENDING_USER' for r in attrs), 'all six rulings must remain pending')
    need(manifest['simp_approval'] == 'PENDING_USER' and report['merge_clearance'] is False, 'no approval or merge clearance')
    need(manifest['head'] == report['head'] == 'a495f3953afff46ad5dec2d29ac8a7f55bd8ae37', 'wrong source head')
    need(len(rows) == 2246 and sum(r['bytes'] for r in rows) == 79343953, 'complete input count/size changed')


def main():
    need(OUT.resolve().parent == BASE.resolve() and not OUT.resolve().is_relative_to(SOURCE.resolve()), 'output must be separate sibling')
    names = ['final-static-r1.zip', 'FILES.json', 'FILES.tsv', 'checkpoint-manifest.json', 'checkpoint-receipt.json', 'SHA256SUMS']
    need(all(not (OUT / name).exists() for name in names), 'existing output: never overwrite')
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    before = snapshot()
    validate_bindings(before)
    archive = OUT / names[0]
    with archive.open('xb') as rawout:
        with zipfile.ZipFile(rawout, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9, allowZip64=True) as z:
            for row in before:
                path = Path(row['source_path'])
                need(identity(path.lstat()) == tuple(row['stat_identity']), 'input changed before ZIP write')
                info = zipfile.ZipInfo(row['zip_path'], date_time=(1980, 1, 1, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info._compresslevel = 9
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | row['stat_identity'][4]) << 16
                h = hashlib.sha256()
                count = 0
                with path.open('rb') as source, z.open(info, 'w', force_zip64=True) as target:
                    while chunk := source.read(CHUNK):
                        h.update(chunk)
                        count += len(chunk)
                        target.write(chunk)
                need((count, h.hexdigest()) == (row['bytes'], row['sha256']) and identity(path.lstat()) == tuple(row['stat_identity']), 'input changed while archived')
    need(archive.stat().st_size < 50_000_000, 'archive exceeds 50MB; preserve it and report before further work, never exclude inputs')
    with zipfile.ZipFile(archive) as z:
        infos = z.infolist()
        expected = {r['zip_path']: r for r in before}
        need(len(infos) == len(expected) and {i.filename for i in infos} == set(expected), 'ZIP missing or duplicate entries')
        for info in infos:
            row = expected[info.filename]
            need(not info.is_dir() and not (info.flag_bits & 1) and stat.S_ISREG(info.external_attr >> 16), 'invalid ZIP entry type/encryption')
            h = hashlib.sha256()
            count = 0
            with z.open(info) as stream:
                while chunk := stream.read(CHUNK):
                    h.update(chunk)
                    count += len(chunk)
            need((count, h.hexdigest()) == (row['bytes'], row['sha256']) and info.file_size == count, 'complete ZIP readback mismatch')
    after = snapshot()
    need(before == after, 'source changed between complete before/after reads')
    validate_bindings(after)
    archive_bytes, archive_sha = digest_file(archive)
    archive_row = {'path': archive.name, 'bytes': archive_bytes, 'sha256': archive_sha,
                   'entries': len(before), 'uncompressed_bytes': sum(r['bytes'] for r in before)}
    categories = {category: {'files': sum(r['category'] == category for r in before),
                            'bytes': sum(r['bytes'] for r in before if r['category'] == category)}
                  for category in sorted({r['category'] for r in before})}
    public = [{k: v for k, v in r.items() if k != 'stat_identity'} for r in before]
    indices = [write_new('FILES.json', encode({'files': public, 'categories': categories}))]
    buf = io.StringIO()
    writer = csv.writer(buf, delimiter='\t', lineterminator='\n')
    keys = ['zip_path', 'bytes', 'sha256', 'category', 'source_path']
    writer.writerow(keys)
    for row in public:
        writer.writerow([row[k] for k in keys])
    indices.append(write_new('FILES.tsv', buf.getvalue().encode()))
    builder_sha = sha(Path(__file__).read_bytes())
    manifest = {'status': 'FROZEN_STATIC_CHECKPOINT_PENDING_USER_RULING_NO_ACCEPTANCE',
                'source_root': str(SOURCE), 'source_manifest_sha256': SOURCE_MANIFEST,
                'source_report_sha256': SOURCE_REPORT, 'source_manifest_indexed_leaves': 2244,
                'source_head': 'a495f3953afff46ad5dec2d29ac8a7f55bd8ae37',
                'actual_PRbase': '067c5d8d6dd436e62681d7dc607984c705dc80a2',
                'pending_ruling_memo': {'path': str(MEMO), 'sha256': MEMO_SHA, 'bytes': 2398,
                                       'status': 'PENDING_USER_NOT_APPROVAL', 'pending_attributes': 6},
                'archive': archive_row, 'categories': categories, 'indices': indices,
                'source_content_fingerprint_sha256': fingerprint(before), 'builder_sha256': builder_sha,
                'all_original_bytes_unchanged': True, 'full_archive_readback_verified': True,
                'archive_includes_itself': False, 'failure_checkpoint_included': False,
                'native_run': False, 'input_programs_executed': False, 'approval_inferred': False,
                'limits': ['Static review and pending memo are data; this archive grants no approval, waiver, native clearance or merge acceptance.',
                           'All 2244 indexed source leaves plus the frozen manifest and separately labelled memo are included without exclusions.',
                           'No Lean/native/cache/build/app/Git or input-program execution; all source .lean files remain inside the ZIP only.']}
    mr = write_new('checkpoint-manifest.json', encode(manifest))
    receipt = {'status': 'COMPLETE_ARCHIVE_READBACK_VERIFIED_PENDING_RULING_NO_ACCEPTANCE',
               'started_utc': started, 'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'archive': archive_row, 'checkpoint_manifest': mr,
               'source_before_fingerprint_sha256': fingerprint(before), 'source_after_fingerprint_sha256': fingerprint(after),
               'full_source_before_after_equal': True, 'zip_entries_fully_read_back': len(before),
               'categories': categories, 'all_six_attributes': 'PENDING_USER', 'approval_inferred': False,
               'originals_preserved': True, 'native_run': False, 'input_programs_executed': False,
               'builder_sha256': builder_sha}
    rr = write_new('checkpoint-receipt.json', encode(receipt))
    checksums = [{'path': 'build_checkpoint.py', 'sha256': builder_sha}, archive_row, *indices, mr, rr]
    write_new('SHA256SUMS', ''.join(f"{r['sha256']}  {r['path']}\n" for r in checksums).encode())
    print(json.dumps({'archive': archive_row, 'manifest_sha256': mr['sha256'], 'receipt_sha256': rr['sha256'],
                      'categories': categories, 'originals_unchanged': True, 'approval_inferred': False}, indent=2))


if __name__ == '__main__':
    main()
