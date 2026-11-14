#!/usr/bin/env python3
"""Apply the complete local patch series to exact affected base source bytes.

No dependency tree or Lean process is involved. Run as python3 -I.
"""
import hashlib
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

BASE = "eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9"
ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, default=Path("evidence/patch-reproduction-final"))
args = parser.parse_args()
OUT = ROOT / args.output
# An independent source-only temporary directory avoids git-apply's implicit
# repository-subdirectory path filtering. No objects/packages are copied.
TREE = Path(tempfile.mkdtemp(prefix="dl-crh-patch-source-", dir="/private/tmp"))

def git(*args, cwd=ROOT):
    return subprocess.check_output(["git", *args], cwd=cwd)

def sha(data):
    return hashlib.sha256(data).hexdigest()

assert not OUT.exists(), "use a fresh reproduction path"
OUT.mkdir(parents=True)
head = git("rev-parse", "HEAD").decode().strip()
paths = git("diff", "--name-only", BASE, head).decode().splitlines()
base_files = set(git("ls-tree", "-r", "--name-only", BASE).decode().splitlines())
for name in paths:
    if name in base_files:
        target = TREE / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(git("show", f"{BASE}:{name}"))
patchdir = OUT / "patches"
patchdir.mkdir()
git("format-patch", "--output-directory", str(patchdir), f"{BASE}..{head}")
for patch in sorted(patchdir.glob("*.patch")):
    git("apply", "--check", str(patch), cwd=TREE)
    git("apply", str(patch), cwd=TREE)
rows = []
for name in paths:
    actual = (TREE / name).read_bytes()
    expected = git("show", f"{head}:{name}")
    assert actual == expected, name
    rows.append(dict(path=name, reproduced_sha256=sha(actual), head_sha256=sha(expected)))
record = dict(base=BASE, head=head, source_only_scratch=str(TREE),
              patches=[p.name for p in sorted(patchdir.glob("*.patch"))],
              all_reproduced=True, files=rows)
(OUT / "result.json").write_text(json.dumps(record, indent=2) + "\n")
print("PASS complete patch series reproduces all", len(rows), "changed/new source files exactly")
print("BASE", BASE)
print("HEAD", head)
