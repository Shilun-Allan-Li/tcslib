"""Verify archive bytes, exact ZIP entries, sizes, and raw SHA-256 without extracting."""
from pathlib import Path
import csv
import hashlib
import zipfile


def digest_stream(stream):
    result = hashlib.sha256()
    size = 0
    for block in iter(lambda: stream.read(1024 * 1024), b""):
        result.update(block)
        size += len(block)
    return result.hexdigest(), size


root = Path(__file__).resolve().parent
parts = sorted(root.glob("*diagnostics-part-*.zip"))
assert parts, "No diagnostic ZIP parts found"
for part in parts:
    expected_archive = Path(str(part) + ".SHA256").read_text().split()[0]
    with part.open("rb") as stream:
        actual_archive, _ = digest_stream(stream)
    assert actual_archive == expected_archive, part
    entries_path = part.with_name(part.stem + "-entries.tsv")
    with entries_path.open(newline="") as stream:
        entries = list(csv.DictReader(stream, delimiter="\t"))
    names = [row["entry"] for row in entries]
    assert len(names) == len(set(names)), part
    with zipfile.ZipFile(part) as archive:
        assert sorted(archive.namelist()) == sorted(names), part
        for row in entries:
            with archive.open(row["entry"]) as stream:
                digest, size = digest_stream(stream)
            assert digest == row["sha256"], (part, row["entry"], "raw hash")
            assert size == int(row["bytes"]), (part, row["entry"], "raw size")
    print(f"PASS {part.name}: {len(entries)} exact entries, raw hashes/sizes verified")
print(f"PASS {len(parts)} diagnostic ZIP parts")
