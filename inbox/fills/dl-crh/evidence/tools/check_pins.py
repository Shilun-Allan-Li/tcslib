#!/usr/bin/env python3
"""Check every package present against the committed URL/revision manifest."""
import json
from pathlib import Path
import subprocess

manifest = json.loads(Path("lake-manifest.json").read_text())
present = 0
for package in manifest["packages"]:
    name = package["name"].removeprefix("«").removesuffix("»")
    path = Path(".lake/packages") / name
    if not path.exists():
        print("ABSENT", name)
        continue
    url = subprocess.check_output(["git", "-C", str(path), "remote", "get-url", "origin"], text=True).strip()
    rev = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
    print(name, url, rev)
    assert url == package["url"], (name, url, package["url"])
    assert rev == package["rev"], (name, rev, package["rev"])
    present += 1
print(f"PASS all {present} present packages match manifest URLs and revisions")
