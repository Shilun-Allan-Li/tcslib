"""Read-only safe receipt of MIG-1 checkpoint cp03.

Writes only beneath this script's directory. Payloads are data: no delivered
script, proof, Git bundle, or patch is executed/applied. Lean sources receive
an extra .txt suffix when extracted, including evidence sources.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import unicodedata
import zipfile


OUT = Path(__file__).resolve().parent
REPO = OUT.parents[4]
EXCHANGE = Path(os.environ["TCSLIB_EXCHANGE"])


def inspect(checkpoint: str) -> dict:
    name = f"fill-mig1-mega-{checkpoint}.zip"
    original = EXCHANGE / "inbox/fill-mig1-mega" / name
    raw = original.read_bytes()
    saved = OUT / "original-zips" / name
    saved.parent.mkdir(exist_ok=True)
    assert not saved.exists(), saved
    saved.write_bytes(raw)
    result = {"checkpoint": checkpoint, "input": str(original), "saved_zip": str(saved),
              "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}
    with zipfile.ZipFile(saved) as archive:
        infos = archive.infolist()
        assert len(infos) <= 10000, "member limit"
        assert sum(item.file_size for item in infos) <= 512 * 1024 * 1024, "size limit"
        members = {}
        targets = {}
        portable_targets = set()
        inventory = []
        for item in infos:
            path = PurePosixPath(item.filename)
            assert not path.is_absolute() and ".." not in path.parts, item.filename
            assert "\\" not in item.filename and not any(ord(c) < 32 for c in item.filename), item.filename
            assert not stat.S_ISLNK(item.external_attr >> 16), item.filename
            assert item.file_size <= 128 * 1024 * 1024, item.filename
            normalized = str(path)
            assert normalized not in members, ("duplicate normalized path", normalized)
            members[normalized] = item
            target = normalized + ".txt" if normalized.endswith(".lean") else normalized
            portable = unicodedata.normalize("NFC", target).casefold()
            assert portable not in portable_targets, ("colliding extracted path", target)
            portable_targets.add(portable)
            targets[normalized] = target
            inventory.append({"path": item.filename, "normalized": normalized,
                              "extracted": target, "bytes": item.file_size,
                              "compressed_bytes": item.compress_size,
                              "is_directory": item.is_dir(), "mode": oct(item.external_attr >> 16)})
        (OUT / f"{checkpoint}-inventory.json").write_text(json.dumps(inventory, indent=2) + "\n")
        # Read and CRC-check every regular payload before any extraction.
        payload = {name: archive.read(item) for name, item in members.items() if not item.is_dir()}
        manifests = [name for name in payload if PurePosixPath(name).name == "SHA256SUMS"]
        assert len(manifests) == 1, manifests
        manifest = manifests[0]
        parent = PurePosixPath(manifest).parent
        checked = set()
        for line in payload[manifest].decode("utf-8").splitlines():
            if not line.strip():
                continue
            match = re.fullmatch(r"([0-9a-fA-F]{64}) [ *](.+)", line)
            assert match, ("bad checksum line", line)
            relative = PurePosixPath(match.group(2))
            assert not relative.is_absolute() and ".." not in relative.parts
            name = str(parent / relative)
            assert name in payload, ("missing checksummed file", name)
            assert name not in checked, ("duplicate manifest entry", name)
            assert hashlib.sha256(payload[name]).hexdigest() == match.group(1).lower(), name
            checked.add(name)
        assert checked == set(payload) - {manifest}, ("uncovered files", sorted(set(payload) - {manifest} - checked))
        report_name = str(parent / "REPORT.md")
        assert report_name in payload, report_name
        # Reports are read as UTF-8 data, then preserved verbatim.
        report = payload[report_name].decode("utf-8")
        reports = OUT / "reports"
        reports.mkdir(exist_ok=True)
        (reports / f"{checkpoint}-REPORT.md").write_bytes(payload[report_name])
        (reports / f"{checkpoint}-SHA256SUMS").write_bytes(payload[manifest])
        extracted = OUT / checkpoint
        assert not extracted.exists(), extracted
        extracted.mkdir()
        for name, item in members.items():
            destination = extracted / targets[name]
            if item.is_dir():
                destination.mkdir(parents=True, exist_ok=True)
            else:
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(payload[name])
                destination.chmod(0o644)
        assert not list(extracted.rglob("*.lean"))
        result.update(status="PASS", members=len(infos), regular_files=len(payload),
                      checked_files=len(checked), total_uncompressed_bytes=sum(len(v) for v in payload.values()),
                      report_path=report_name, extracted=str(extracted), lean_sources_renamed=True)
    return result


def main() -> None:
    dispatch = json.loads((REPO / "campaign/fills/mig1/dispatch.json").read_text())
    prior = json.loads((OUT.parent / "checkpoints-2026-11-07/receipt.json").read_text())
    base = dispatch["lean_base"]
    assert base == prior["pinned_base"]
    results = {"pinned_base": base, "dispatch_agent": dispatch["agent"], "checkpoints": []}
    for checkpoint in ("cp03",):
        try:
            entry = inspect(checkpoint)
        except Exception as exc:
            entry = {"checkpoint": checkpoint, "status": "FAIL", "reason": repr(exc)}
        results["checkpoints"].append(entry)
        print(json.dumps(entry), flush=True)
    (OUT / "receipt.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
