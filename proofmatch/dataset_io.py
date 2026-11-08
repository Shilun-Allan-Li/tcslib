"""Read plain, gzip, or manifested gzip-shard representations of a dataset."""
from __future__ import annotations
import gzip
import io
import json
from pathlib import Path


def resolve_dataset(path: Path) -> Path:
    """Pick the newest available mirror; explicit existing representations win."""
    path = Path(path)
    if (path.suffix == '.gz' or path.name.endswith('.manifest.json')) and path.exists():
        return path
    logical = Path(str(path)[:-3]) if path.suffix == '.gz' else path
    candidates = [logical, Path(str(logical) + '.gz'), logical.with_suffix('.manifest.json')]
    existing = [p for p in candidates if p.exists()]
    return max(existing, key=lambda p: p.stat().st_mtime_ns) if existing else path


class _ShardReader(io.TextIOBase):
    def __init__(self, manifest: Path):
        super().__init__()
        data = json.loads(manifest.read_text())
        if data.get('format') != 'tcslib-jsonl-shards-v1':
            raise ValueError(f'Unsupported dataset manifest: {manifest}')
        root = manifest.parent.resolve()
        paths = []
        for shard in data['shards']:
            path = (root / shard['path']).resolve()
            if not path.is_relative_to(root):
                raise ValueError('Shard paths must stay inside the manifest directory')
            if path.stat().st_size != shard['compressed_bytes']:
                raise ValueError(f'Shard size mismatch: {path}')
            paths.append(path)
        self.paths = iter(paths)
        self.current = None

    def readable(self):
        return True

    def _advance(self):
        if self.current is not None:
            self.current.close()
        path = next(self.paths, None)
        self.current = gzip.open(path, 'rt', encoding='utf-8') if path else None
        return self.current is not None

    def read(self, size=-1):
        self._checkClosed()
        chunks = []
        remaining = size
        while remaining != 0:
            if self.current is None and not self._advance():
                break
            part = self.current.read(remaining)
            chunks.append(part)
            if size >= 0:
                remaining -= len(part)
            if not part:
                if not self._advance():
                    break
        return ''.join(chunks)

    def readline(self, size=-1):
        self._checkClosed()
        if size == 0:
            return ''
        chunks = []
        remaining = size
        while remaining != 0:
            if self.current is None and not self._advance():
                break
            part = self.current.readline(remaining)
            chunks.append(part)
            if size >= 0:
                remaining -= len(part)
            if part.endswith('\n'):
                break
            if not part and not self._advance():
                break
        return ''.join(chunks)

    def close(self):
        if self.current is not None:
            self.current.close()
        super().close()


def open_dataset(path: Path) -> io.TextIOBase:
    resolved = resolve_dataset(path)
    if resolved.name.endswith('.manifest.json'):
        return _ShardReader(resolved)
    if resolved.suffix == '.gz':
        return gzip.open(resolved, 'rt', encoding='utf-8')
    return resolved.open(encoding='utf-8')


def read_dataset_text(path: Path) -> str:
    with open_dataset(path) as handle:
        return handle.read()


def dataset_exists(path: Path) -> bool:
    return resolve_dataset(path).exists()
