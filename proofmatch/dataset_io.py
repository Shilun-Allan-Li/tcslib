"""Reading the theorem dataset, whichever form is on disk.

`dataset/tcslib_theorems.jsonl` is generated, ~100 MB, and byte-identical to its own
gzip -- GitHub rejects files over 100 MB, so only `tcslib_theorems.jsonl.gz` (~14 MB) is
tracked and the plain `.jsonl` is git-ignored. A fresh clone therefore has the `.gz` and
no `.jsonl`.

Every reader goes through `open_dataset`, which takes the *logical* `.jsonl` path and
transparently falls back to `<path>.gz`. That keeps existing path constants, CLI
`--dataset` arguments and test fixtures written in terms of the `.jsonl` name working
unchanged, whether or not the uncompressed copy has been generated locally.
"""

from __future__ import annotations

import gzip
import io
from pathlib import Path


def resolve_dataset(path: Path) -> Path:
    """The file that actually holds `path`'s contents: itself, or its gzip."""
    if path.exists():
        return path
    gz = path.with_suffix(path.suffix + ".gz")
    if gz.exists():
        return gz
    return path


def open_dataset(path: Path) -> io.TextIOBase:
    """Open the dataset for reading as text, preferring the plain file."""
    resolved = resolve_dataset(path)
    if resolved.suffix == ".gz":
        return gzip.open(resolved, "rt", encoding="utf-8")
    return resolved.open(encoding="utf-8")


def read_dataset_text(path: Path) -> str:
    with open_dataset(path) as handle:
        return handle.read()


def dataset_exists(path: Path) -> bool:
    return resolve_dataset(path).exists()
