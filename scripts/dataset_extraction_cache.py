"""Reuse deterministic exports only while all inputs and output hashes match."""
from __future__ import annotations
import fcntl
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

from proofmatch.artifacts import atomic_json, sha256_file


def extraction_inputs(base: Path, roots: dict[str, Path]):
    paths = {base / 'dep_graph.json', base / 'dataset/projects.json'}
    for name in ['build_dataset.py', 'dataset_projects.py', 'informal_sources.py', 'dataset_extraction_cache.py']:
        paths.add(base / 'scripts' / name)
    for name in ['blueprint.py', 'dataset_io.py', 'models.py']:
        paths.add(base / 'proofmatch' / name)
    paths.update((base / 'blueprint/src/chapter').rglob('*.tex'))
    refs = base / 'blueprint/src/references'
    paths.update(p for p in refs.glob('*.md') if not p.name.endswith('.raw.md'))
    paths.update(p for p in (refs / 'informalized').glob('*.md') if p.stem != 'WORKLIST')
    for name, root in roots.items():
        paths.update((root / name).rglob('*.lean'))
        paths.update(root / suffix for suffix in ['lean-toolchain', 'lake-manifest.json', 'LICENSE', name + '.lean'])
    return sorted(paths, key=str)


def input_fingerprint(base: Path, roots: dict[str, Path], flags):
    entries = [(str(p.resolve()), sha256_file(p) if p.is_file() else None)
               for p in extraction_inputs(base, roots)]
    value = dict(version=1, python=sys.version, flags=list(flags), inputs=entries)
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def _valid_outputs(receipt, paths):
    try:
        return all(p.is_file() and p.stat().st_size == receipt['outputs'][p.name]['bytes']
                   and sha256_file(p) == receipt['outputs'][p.name]['sha256'] for p in paths)
    except (KeyError, TypeError):
        return False


def ensure_extraction(base: Path, roots: dict[str, Path], cache_dir: Path, flags, build):
    """Publish a fresh export atomically; incomplete/interrupted builds cannot hit."""
    cache_dir.mkdir(parents=True, exist_ok=True)
    mode = 'statements' if '--no-proof' in flags else 'proofs'
    output = cache_dir / (mode + '.jsonl')
    compressed = Path(str(output) + '.gz')
    receipt_path = cache_dir / (mode + '.receipt.json')
    with (cache_dir / (mode + '.lock')).open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        fingerprint = input_fingerprint(base, roots, flags)
        if receipt_path.is_file():
            try:
                receipt = json.loads(receipt_path.read_text())
            except json.JSONDecodeError:
                receipt = {}
            if not isinstance(receipt, dict):
                receipt = {}
            if receipt.get('fingerprint') == fingerprint and _valid_outputs(receipt, [output, compressed]):
                print(f'  extraction cache: reusing validated {mode} export', flush=True)
                return output
        print(f'  extraction cache: rebuilding {mode} export (missing, changed, or invalid cache)', flush=True)
        with tempfile.NamedTemporaryFile(dir=cache_dir, suffix='.jsonl', prefix='.building-', delete=False) as handle:
            temporary = Path(handle.name)
        temporary_gz = Path(str(temporary) + '.gz')
        try:
            build(temporary)
            if input_fingerprint(base, roots, flags) != fingerprint:
                raise RuntimeError('Dataset inputs changed during extraction; rerun before publishing the export')
            if not temporary.is_file() or not temporary_gz.is_file():
                raise RuntimeError('Extraction did not produce both JSONL and gzip outputs')
            os.replace(temporary, output)
            os.replace(temporary_gz, compressed)
            receipt = dict(fingerprint=fingerprint, flags=list(flags), outputs={
                p.name: dict(bytes=p.stat().st_size, sha256=sha256_file(p)) for p in [output, compressed]})
            atomic_json(receipt_path, receipt)
        finally:
            temporary.unlink(missing_ok=True)
            temporary_gz.unlink(missing_ok=True)
    return output


def publish_mirror(source: Path, destination: Path):
    """Link complete immutable outputs into the pipeline's existing logical paths."""
    destination.parent.mkdir(parents=True, exist_ok=True)
    for src, dst in [(source, destination), (Path(str(source) + '.gz'), Path(str(destination) + '.gz'))]:
        with tempfile.NamedTemporaryFile(dir=dst.parent, prefix='.mirror-', delete=False) as handle:
            temporary = Path(handle.name)
        temporary.unlink()
        try:
            os.link(src, temporary)
            os.replace(temporary, dst)
        finally:
            temporary.unlink(missing_ok=True)
    # Readers prefer the newest mirror. The identical plain text avoids a
    # decompression pass when parsing a multi-gigabyte export locally.
    os.utime(destination, None)
