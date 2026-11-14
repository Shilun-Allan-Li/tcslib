#!/usr/bin/env python3
"""Seal or verify this payload; optionally create and verify the fallback ZIP.

Use python3 -I. Manifests are relative to their own containing directories.
"""
import argparse
import hashlib
from pathlib import Path
import zipfile


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def files(root):
    return {p.relative_to(root).as_posix(): p for p in root.rglob("*") if p.is_file()}


def seal(root):
    entries = files(root)
    entries.pop("SHA256SUMS", None)
    (root / "SHA256SUMS").write_text(
        "".join(f"{digest(path)}  {name}\n" for name, path in sorted(entries.items()))
    )


def verify(root):
    actual = files(root)
    actual.pop("SHA256SUMS", None)
    expected = {}
    for line in (root / "SHA256SUMS").read_text().splitlines():
        sha, name = line.split("  ", 1)
        assert name not in expected, ("duplicate", name)
        expected[name] = sha
    assert actual.keys() == expected.keys(), (actual.keys() ^ expected.keys())
    for name, path in actual.items():
        assert digest(path) == expected[name], name
    print(f"PASS exact paths and SHA-256: {root.name}, {len(actual)} files")


parser = argparse.ArgumentParser()
parser.add_argument("payload", type=Path)
parser.add_argument("--seal", action="store_true")
parser.add_argument("--zip", type=Path)
args = parser.parse_args()
payload = args.payload.resolve()
assert payload.name == "dl-crh"
if args.seal:
    seal(payload / "evidence")
    seal(payload)
verify(payload / "evidence")
verify(payload)
if args.zip:
    with zipfile.ZipFile(args.zip, "w", zipfile.ZIP_DEFLATED) as archive:
        for name, path in sorted(files(payload).items()):
            archive.write(path, f"dl-crh/{name}")
    with zipfile.ZipFile(args.zip) as archive:
        assert archive.testzip() is None
        expected = {f"dl-crh/{name}": path.read_bytes() for name, path in files(payload).items()}
        assert set(archive.namelist()) == set(expected)
        for name, data in expected.items():
            assert archive.read(name) == data, name
    print(f"PASS ZIP exact paths and bytes: {args.zip}")
    print(f"ZIP SHA256 {digest(args.zip)}")
