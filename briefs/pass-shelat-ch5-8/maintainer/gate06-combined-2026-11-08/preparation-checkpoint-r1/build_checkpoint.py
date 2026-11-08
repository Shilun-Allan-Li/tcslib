"""Own preparation-data backup only; never execute a selected input program.

Run with python3 -I. Exact selected files are read twice and a deterministic ZIP
is read back. No source, object, cache, lease or active native evidence is changed.
"""
from pathlib import Path
import datetime as dt
import hashlib
import io
import json
import os
import stat
import subprocess
import sys
import zipfile
import zlib

OUT = Path(__file__).resolve().parent
AREA = OUT.parent
W = AREA.parents[2]
HEAD = 'a495f3953afff46ad5dec2d29ac8a7f55bd8ae37'
FORBIDDEN = {'.olean', '.ilean', '.o', '.a', '.so', '.dylib', '.pyc'}


def digest(raw): return hashlib.sha256(raw).hexdigest()
def encode(value): return (json.dumps(value, indent=2, ensure_ascii=False)+'\n').encode()
def put(path, raw):
    with path.open('xb') as stream: stream.write(raw)


def read_input(rel):
    path = AREA/rel
    assert not Path(rel).is_absolute() and '..' not in Path(rel).parts
    assert path.resolve(strict=True).is_relative_to(AREA.resolve(strict=True))
    assert path.is_file() and not path.is_symlink() and path.suffix not in FORBIDDEN, rel
    assert not any(x in path.parts for x in ('final-static-r1', '__pycache__', '.git'))
    assert not rel.startswith(('native-bootstrap-r1/', 'native-local-r1/', 'oleans-r1/', 'preparation-checkpoint-r1/'))
    assert path.name != 'native-runner.lease.json'
    raw = path.read_bytes()
    mode = stat.S_IMODE(path.stat().st_mode)
    return raw, mode


def zip_bytes(members):
    output = io.BytesIO()
    with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        archive.comment = b''
        for name, (raw, mode) in sorted(members.items()):
            entry = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
            entry.create_system = 3
            entry.compress_type = zipfile.ZIP_DEFLATED
            entry.external_attr = (stat.S_IFREG | mode) << 16
            entry.extra = b''; entry.comment = b''
            archive.writestr(entry, raw, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    return output.getvalue()


def main():
    assert {p.name for p in OUT.iterdir()} == {'build_checkpoint.py', 'selected-paths.txt'}, 'Use a fresh checkpoint; preserve every older result'
    selection_raw = (OUT/'selected-paths.txt').read_bytes()
    selected = selection_raw.decode().splitlines()
    assert selected == sorted(set(selected)) and len(selected) == 289
    builder_raw = Path(__file__).read_bytes()
    payload = {rel: read_input(rel) for rel in selected}
    get = lambda rel: json.loads(payload[rel][0])
    receipt = get('combined-source-commit.json')
    assert receipt['head'] == HEAD
    env = dict(os.environ, GIT_OPTIONAL_LOCKS='0')
    assert subprocess.check_output(['git', '-C', str(W), 'rev-parse', 'HEAD'], env=env, text=True).strip() == HEAD
    cache = get('cache-r2/RESULT.json')
    hashes = get('cache-r2/POST-CACHE-146.json')
    copied = get('copy-r1/RESULT.json')
    assert cache['passed'] is True and cache['rc'] == 0 and cache['roots'] == 54 and not cache['missing_non_PFR_package_objects']
    assert hashes['historical_direct_Mathlib_objects'] == 146 and hashes['all_byte_hashes_unchanged'] and hashes['cache_passed']
    assert copied['copied_TCSlib_objects'] == 437 and copied['status'] == 'COPY_HASH_VERIFIED_NOT_YET_RELIED_ON'
    assert copied['reproductions'] == 'PENDING_3_FRESH_NATIVE_BYTE_COMPARISONS'
    assert digest(payload['rule10-r1/Collect.lean'][0]) == digest(payload['rule10-evidence-r1/Collect.source.txt'][0]) == '5654cc5a325f746a5d1fc7c7d3076cd0df4e46415be2866edf50e542ed110929'
    rows = [{'path': rel, 'archive_path': 'payload/'+rel, 'bytes': len(raw), 'sha256': digest(raw), 'mode_octal': oct(mode)}
            for rel, (raw, mode) in sorted(payload.items())]
    exclusions = ['active native-bootstrap-r1/ and native-local-r1/ evidence', 'native-runner.lease.json',
                  'all object trees and .olean/.ilean/compiled objects', 'source-review/final-static-r1/ and new failure-prep/static-review directories',
                  'future Rule10 collector/seal/control results; only the16 explicitly selected preparation files are captured',
                  'unlisted new workflow/review directories; selection is a frozen positive allowlist']
    manifest = {'status': 'EXACT_PREPARATION_INPUT_SNAPSHOT_NOT_ACCEPTANCE', 'source_head': HEAD,
                'origin_area': str(AREA), 'raw_input_files': len(rows), 'raw_input_bytes': sum(r['bytes'] for r in rows),
                'selected_paths_sha256': digest(selection_raw), 'builder_sha256': digest(builder_raw),
                'zip_layout': 'payload/<AREA-relative path> plus four checkpoint metadata files',
                'deliberate_exclusions': exclusions, 'files': rows}
    manifest_raw = encode(manifest)
    readme = f'''# Combined Gate06 preparation checkpoint r1

This is an exact backup of {len(rows)} selected preparation inputs ({manifest['raw_input_bytes']:,} raw bytes) for source `{HEAD}`. It is **not acceptance or merge clearance**.

The ZIP contains raw files under `payload/`, plus this README, the raw-file manifest, frozen positive allowlist and the own builder source. Every selected input byte is preserved, including existing older rejected assemblies, explicitly reconstructed prior provenance, failed guards and host-deferred cache history. Files are hashed before and after archiving. Sorted ZIP entries use fixed timestamps/permissions and no comments/extras; a second construction is byte-identical and every entry is read back and compared. Compression uses the recorded Python/zlib implementation; different compressor versions are not asserted to produce identical compressed bytes.

Included: frozen source-review and its existing peer/namespace companion; native-prep; all existing Rule10 proposal assemblies and prior provenance; native-runtime-proposal including peer-api; copy-r1; both cache attempts; PFR config/bin; the frozen actual collector source and its16 preparation files; source/cache/preparation scripts and available source/copy/preparation receipts. Programs are archived as data and were not imported or executed. No separate copy-program file is selected: the original437-row copy log and receipt are retained verbatim.

Completed evidence captured here is limited to the native **54-root cache operation** (rc0, required non-PFR objects present) and the **146 historical direct Mathlib-object hash recheck** after it. The hash recheck is cache/environment evidence, not a Lean proof run. The **437 copied TCSlib objects are only hash-verified, with three fresh exact-byte reproductions still pending** in the captured copy receipt.

The full1075 root/`audits/pass-shelat/Checks` source/object scope, complete bootstrap/PFR31/three reproductions, the638 fresh local checks, and fresh Rule10 collection/seals/controls/C3/axiom acceptance remain **unestablished by this checkpoint**. Active bootstrap evidence and its lease are deliberately excluded; this archive makes no native-bootstrap-start or success claim. Rule10 collector preparation is not execution.

The new `source-review/final-static-r1` review and future failure-prep/workflow output are not raced or recursively captured. Later results belong in fresh separately bound records. Archived GitHub/target/PR snapshots are preparation history, not a new assertion about the latest target branch; final acceptance must recheck that target source.

`INPUT-MANIFEST.json` maps every raw file to its original AREA-relative path, byte count, SHA256 and mode. `receipt.json` outside the ZIP binds archive/metadata hashes and read-back/stability results without a self-hash cycle. No .olean/object file is included. No tracked source, MAIN, exchange, package/cache or object tree was changed by the checkpoint builder.

**Not yet clear to merge — fresh native and Rule10 verification pending**
'''.encode()
    members = {'payload/'+k: value for k, value in payload.items()}
    members.update({'INPUT-MANIFEST.json': (manifest_raw, 0o644), 'README.md': (readme, 0o644),
                    'build_checkpoint.py': (builder_raw, 0o644), 'selected-paths.txt': (selection_raw, 0o644)})
    zipped = zip_bytes(members)
    assert zip_bytes(members) == zipped, 'Deterministic second construction differs'
    with zipfile.ZipFile(io.BytesIO(zipped)) as archive:
        assert archive.namelist() == sorted(members) and len(archive.namelist()) == len(set(archive.namelist()))
        assert archive.testzip() is None
        for name, (raw, mode) in members.items():
            entry = archive.getinfo(name)
            assert archive.read(name) == raw and entry.file_size == len(raw), name
            assert entry.date_time == (1980, 1, 1, 0, 0, 0) and stat.S_IMODE(entry.external_attr >> 16) == mode
            assert entry.extra == b'' and entry.comment == b''
    for rel, expected in payload.items():
        observed = read_input(rel)
        assert len(observed[0]) == len(expected[0]) and digest(observed[0]) == digest(expected[0]) and observed[1] == expected[1], 'Input changed during checkpoint: '+rel
    assert (OUT/'selected-paths.txt').read_bytes() == selection_raw and Path(__file__).read_bytes() == builder_raw
    put(OUT/'INPUT-MANIFEST.json', manifest_raw); put(OUT/'README.md', readme)
    put(OUT/'preparation-checkpoint.zip', zipped)
    # Validate the persisted ZIP again, not just the in-memory construction.
    assert digest((OUT/'preparation-checkpoint.zip').read_bytes()) == digest(zipped)
    with zipfile.ZipFile(OUT/'preparation-checkpoint.zip') as archive:
        for name, (raw, _) in members.items(): assert archive.read(name) == raw
    for rel, expected in payload.items():
        observed = read_input(rel)
        assert digest(observed[0]) == digest(expected[0]) and observed[1] == expected[1], 'Input changed after write/read-back: '+rel
    result = {'status': 'PREPARATION_BACKUP_ONLY_NOT_ACCEPTANCE', 'finished_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
              'source_head': HEAD, 'raw_inputs': len(rows), 'raw_input_bytes': manifest['raw_input_bytes'],
              'zip_members': len(members), 'zip_bytes': len(zipped), 'zip_sha256': digest(zipped),
              'input_manifest_sha256': digest(manifest_raw), 'README_sha256': digest(readme),
              'builder_sha256': digest(builder_raw), 'selected_paths_sha256': digest(selection_raw),
              'input_bytes_and_modes_stable_before_after': True, 'second_zip_construction_byte_identical': True,
              'all_zip_members_crc_and_raw_bytes_readback_valid': True, 'persisted_zip_readback_valid': True,
              'compression': {'method': 'DEFLATE', 'level': 9, 'python': sys.version, 'zlib': zlib.ZLIB_RUNTIME_VERSION},
              'captured_cache': {'roots': 54, 'rc': 0, 'passed': True, 'cache_result_sha256': digest(payload['cache-r2/RESULT.json'][0]), 'historical146_hash_recheck': True},
              'copy437': 'HASH_VERIFIED_PENDING_THREE_NATIVE_REPRODUCTIONS',
              'native_bootstrap_root_Checks_638_Rule10_acceptance': 'NOT_ESTABLISHED_BY_THIS_CHECKPOINT',
              'active_native_logs_and_lease_included': False, 'object_files_included': 0,
              'worker_or_archived_program_execution': False, 'native_or_cache_execution_by_builder': False,
              'tracked_source_MAIN_exchange_object_or_cache_mutation': False, 'merge_clearance': False,
              'deliberate_exclusions': exclusions}
    put(OUT/'receipt.json', encode(result))
    checksums = ''.join(digest(p.read_bytes())+'  '+p.name+'\n' for p in sorted(OUT.iterdir()) if p.is_file())
    put(OUT/'SHA256SUMS', checksums.encode())
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    try: main()
    except BaseException as exc:
        if not (OUT/'FAILED.json').exists(): put(OUT/'FAILED.json', encode({'error': repr(exc), 'previous_data_preserved': True}))
        raise
