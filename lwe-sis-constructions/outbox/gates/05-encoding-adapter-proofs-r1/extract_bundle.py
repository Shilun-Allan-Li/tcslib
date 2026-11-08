"""Verify and extract frozen text attachments as data into a new scratch directory."""

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


def main():
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python3 -I extract_bundle.py NEW_OUTPUT_DIRECTORY")
    here = Path(__file__).resolve().parent
    output = Path(sys.argv[1]).resolve()
    if output.exists():
        raise SystemExit("Output directory already exists; choose a new scratch path.")
    bundle = (here / "lwe-sis-adapter-proofs-r1-bundle.md").read_bytes()
    assert len(bundle) == 5711128
    assert hashlib.sha256(bundle).hexdigest() == (
        "24de3637321750a0ad12ec46120e32d28db102fd4cd77f0b56621e5e4bd16225")
    manifest = json.loads((here / "BUNDLE-FILES.json").read_text())
    assert len(manifest) == 1009
    assert len({row["path"] for row in manifest}) == len(manifest)
    headers = list(re.finditer(rb"^## ===== (.+) =====\n\n(`+)text\n", bundle, re.M))
    assert len(headers) + 1 == len(manifest)
    recovered = []
    for index, row in enumerate(manifest):
        relative = PurePosixPath(row["path"])
        assert relative.parts and not relative.is_absolute() and ".." not in relative.parts
        start = 0
        if index:
            header = headers[index - 1]
            assert header[1].decode("utf-8") == row["path"]
            start = header.end()
        data = bundle[start:start + row["bytes"]]
        assert len(data) == row["bytes"]
        assert hashlib.sha256(data).hexdigest() == row["sha256"], row["path"]
        recovered.append((relative, data))
    output.mkdir(parents=True)
    for relative, data in recovered:
        destination = output.joinpath(*relative.parts)
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open("xb") as stream:
            stream.write(data)
    print(f"Verified and extracted {len(recovered)} attachments to {output}")


if __name__ == "__main__":
    main()
