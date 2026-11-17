"""Package a JSONL dataset into size-bounded, checksum-verified gzip shards."""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import zlib

SHIPPED_DATASET = Path(__file__).resolve().parent.parent / 'dataset' / 'tcslib_theorems.jsonl'


def refresh_mirrors(source: Path) -> Path:
    """Refresh gzip mirrors; also publish shards for the repository dataset.

    Intermediate exports retain their adjacent gzip. The shipped dataset keeps
    its complete gzip in ignored local storage and publishes a manifest instead.
    """
    shipped = source.resolve() == SHIPPED_DATASET.resolve()
    target = source.with_suffix(source.suffix + '.gz')
    if shipped:
        target = source.parent / 'local' / target.name
    target.parent.mkdir(parents=True, exist_ok=True)
    temp = target.with_suffix(target.suffix + '.tmp')
    with source.open('rb') as src, gzip.open(temp, 'wb', compresslevel=9) as dst:
        shutil.copyfileobj(src, dst)
    temp.replace(target)
    manifest = source.with_suffix('.manifest.json')
    if shipped or manifest.exists():
        package(source, manifest)
    return target


def package(source: Path, manifest: Path, max_bytes: int = 80 * 1024**2) -> dict:
    folder = manifest.parent / 'shards'
    folder.mkdir(parents=True, exist_ok=True)
    shards = []
    total_hash = hashlib.sha256()
    total_rows = 0
    stream = None
    handle = None
    size = rows = 0
    first_id = last_id = None

    def start():
        nonlocal stream, handle, size, rows, first_id, last_id
        stream = zlib.compressobj(level=6, wbits=31)
        handle = tempfile.NamedTemporaryFile(dir=folder, prefix='.building-', delete=False)
        size = rows = 0
        first_id = last_id = None

    def finish():
        nonlocal handle
        if handle is None:
            return
        handle.write(stream.flush(zlib.Z_FINISH))
        handle.close()
        path = Path(handle.name)
        if path.stat().st_size > max_bytes:
            path.unlink()
            raise ValueError('A shard exceeds the configured compressed byte limit')
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        target = folder / f'tcslib_theorems-{len(shards)+1:04d}-{digest[:12]}.jsonl.gz'
        os.replace(path, target)
        shards.append(dict(path=target.relative_to(manifest.parent).as_posix(),
                           compressed_bytes=target.stat().st_size, sha256=digest,
                           rows=rows, first_id=first_id, last_id=last_id))
        handle = None

    try:
        opener = gzip.open if source.suffix == '.gz' else open
        with opener(source, 'rb') as src:
            for line in src:
                if not line.strip():
                    raise ValueError('Blank lines are not valid dataset records')
                if not line.endswith(b'\n'):
                    raise ValueError('Every JSONL record must end in a newline')
                record = json.loads(line)
                if handle is None:
                    start()
                candidate = stream.copy()
                piece = candidate.compress(line) + candidate.flush(zlib.Z_SYNC_FLUSH)
                if size + len(piece) + 64 > max_bytes and rows:
                    finish()
                    start()
                    candidate = stream.copy()
                    piece = candidate.compress(line) + candidate.flush(zlib.Z_SYNC_FLUSH)
                if len(piece) + 64 > max_bytes:
                    raise ValueError('A single record exceeds the compressed shard limit')
                stream = candidate
                handle.write(piece)
                size += len(piece)
                rows += 1
                first_id = first_id or record['id']
                last_id = record['id']
                total_rows += 1
                total_hash.update(line)
        finish()
    finally:
        if handle is not None:
            handle.close()
            Path(handle.name).unlink(missing_ok=True)
    result = dict(format='tcslib-jsonl-shards-v1', rows=total_rows,
                  uncompressed_sha256=total_hash.hexdigest(), max_shard_bytes=max_bytes,
                  shards=shards)
    manifest.parent.mkdir(parents=True, exist_ok=True)
    temp = manifest.with_suffix(manifest.suffix + '.tmp')
    temp.write_text(json.dumps(result, indent=2) + '\n')
    os.replace(temp, manifest)
    return result


def verify(manifest: Path) -> dict:
    data = json.loads(manifest.read_text())
    digest = hashlib.sha256()
    rows = 0
    for shard in data['shards']:
        path = manifest.parent / shard['path']
        if path.stat().st_size != shard['compressed_bytes'] or path.stat().st_size > data['max_shard_bytes']:
            raise ValueError(f'Invalid shard size: {path}')
        if hashlib.sha256(path.read_bytes()).hexdigest() != shard['sha256']:
            raise ValueError(f'Invalid shard checksum: {path}')
        count = 0
        with gzip.open(path, 'rb') as src:
            for line in src:
                json.loads(line)
                digest.update(line)
                count += 1
        if count != shard['rows']:
            raise ValueError(f'Invalid shard row count: {path}')
        rows += count
    if rows != data['rows'] or digest.hexdigest() != data['uncompressed_sha256']:
        raise ValueError('Invalid complete dataset checksum or row count')
    return data


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source', type=Path, nargs='?', help='JSONL or gzip JSONL input')
    ap.add_argument('--manifest', type=Path, default=Path('dataset/tcslib_theorems.manifest.json'))
    ap.add_argument('--max-mib', type=int, default=80)
    ap.add_argument('--verify', action='store_true', help='verify the manifest without repackaging')
    args = ap.parse_args()
    if not args.verify:
        if args.source is None:
            ap.error('source is required unless --verify is used')
        package(args.source, args.manifest, args.max_mib * 1024**2)
    result = verify(args.manifest)
    print(f"Verified {result['rows']} rows in {len(result['shards'])} shards")
