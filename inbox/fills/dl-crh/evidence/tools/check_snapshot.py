#!/usr/bin/env python3
"""Verify that every owned source matches a successful recorded check."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

records = []
for path in (Path("evidence/logs/bootstrap-1/results.jsonl"),
             Path("evidence/logs/helper-1/results.jsonl")):
    records.extend(json.loads(line) for line in path.read_text().splitlines())
latest = {record["module"]: record for record in records}
paths = [Path("TCSlib/Cryptography/Candidates/DiscreteLog.lean"),
         Path("TCSlib/Cryptography/Hashing/FromDiscreteLog.lean")]
paths.extend(sorted(Path("TCSlib/Cryptography/Hashing/FromDiscreteLog").glob("*.lean")))
for path in paths:
    record = latest[str(path)[:-5]]
    assert record["exit_code"] == 0, path
    assert hashlib.sha256(path.read_bytes()).hexdigest() == record["source_sha256"], path
    print("PASS successful check at current source hash:", path)
base = subprocess.check_output([
    "git", "show", "eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9:"
    "TCSlib/Cryptography/Hashing/FromDiscreteLog.lean"], text=True)
current = Path("TCSlib/Cryptography/Hashing/FromDiscreteLog.lean").read_text()
header = r"theorem dlHash_crh\b[\s\S]*?:= by"
assert re.search(header, base)[0] == re.search(header, current)[0]
print("PASS target header byte-identical to issue base")
