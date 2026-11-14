#!/usr/bin/env python3
"""Build a complete dl-crh payload from a local proof commit and evidence snapshot.

Use python3 -I. This tool never pushes or changes a Git branch.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import zipfile

BASE = "eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9"
EXCHANGE = Path("/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange")
VISUALS = Path("/Users/seyoonr/.codex/visualizations/2026/11/14/01a1d88f-8a6d-79a0-830e-fa3653059b77")

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def git(*args):
    return subprocess.check_output(["git", *args])

def inventory(root):
    return {p.relative_to(root).as_posix(): p for p in root.rglob("*")
            if p.is_file() and not p.is_symlink()}

def seal(root):
    entries = inventory(root)
    entries.pop("SHA256SUMS", None)
    (root / "SHA256SUMS").write_text("".join(
        f"{sha(p.read_bytes())}  {n}\n" for n, p in sorted(entries.items())))

def verify(root):
    actual = inventory(root)
    actual.pop("SHA256SUMS", None)
    expected = {}
    for line in (root / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        assert name not in expected, name
        expected[name] = digest
    assert actual.keys() == expected.keys(), actual.keys() ^ expected.keys()
    for name, path in actual.items():
        assert sha(path.read_bytes()) == expected[name], name
    print("PASS manifest exact paths and hashes:", root, len(actual))

parser = argparse.ArgumentParser()
parser.add_argument("destination", type=Path)
parser.add_argument("report", type=Path)
parser.add_argument("--zip", required=True, type=Path)
args = parser.parse_args()
dest = args.destination.resolve()
assert dest.name == "dl-crh" and not dest.exists(), dest
head = git("rev-parse", "HEAD").decode().strip()
git("merge-base", "--is-ancestor", BASE, head)
changed = git("diff", "--name-only", BASE, head).decode().splitlines()
allowed = lambda n: (n in {"TCSlib/Cryptography/Candidates/DiscreteLog.lean",
                           "TCSlib/Cryptography/Hashing/FromDiscreteLog.lean"}
                     or n.startswith("TCSlib/Cryptography/Hashing/FromDiscreteLog/"))
assert changed and all(allowed(n) and n.endswith(".lean") for n in changed), changed
git("diff", "--exit-code", head, "--", "TCSlib")
dest.mkdir(parents=True)
for name in changed:
    path = dest / "src" / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(git("show", f"{head}:{name}"))
patches = dest / "patches"
patches.mkdir()
subprocess.run(["git", "format-patch", "--output-directory", str(patches), f"{BASE}..{head}"], check=True)
evidence = dest / "evidence"
evidence.mkdir()
for name, source in inventory(Path("evidence")).items():
    if source.suffix in {".olean", ".ilean"}:
        continue
    target = evidence / name
    target.parent.mkdir(parents=True, exist_ok=True)
    before = source.read_bytes()
    target.write_bytes(before)
    assert source.read_bytes() == before, ("source changed during snapshot", source)
inputs = EXCHANGE / "inbox/fills/dl-crh/evidence/inputs"
shutil.copytree(inputs, evidence / "inputs", dirs_exist_ok=True)
initial = VISUALS / "dl-crh-escalation.zip"
shutil.copy2(initial, evidence / "initial-escalation.zip")
(evidence / "proof-snapshot.json").write_text(json.dumps(
    dict(base=BASE, head=head, changed_files=changed,
         patch_files=[p.name for p in sorted(patches.glob("*.patch"))],
         initial_zip_sha256=sha(initial.read_bytes())), indent=2) + "\n")
(dest / "REPORT.md").write_text(args.report.read_text() +
    f"\nProof commit: `{head}`. Issue base: `{BASE}`.\n")
seal(evidence)
seal(dest)
verify(evidence)
verify(dest)
with zipfile.ZipFile(args.zip, "w", zipfile.ZIP_DEFLATED) as archive:
    for name, path in sorted(inventory(dest).items()):
        archive.write(path, "dl-crh/" + name)
with zipfile.ZipFile(args.zip) as archive:
    expected = {"dl-crh/" + n: p.read_bytes() for n, p in inventory(dest).items()}
    assert set(archive.namelist()) == set(expected)
    assert archive.testzip() is None
    for name, data in expected.items():
        assert archive.read(name) == data, name
print("PASS ZIP exact paths and bytes:", args.zip)
print("ZIP SHA256", sha(args.zip.read_bytes()))
