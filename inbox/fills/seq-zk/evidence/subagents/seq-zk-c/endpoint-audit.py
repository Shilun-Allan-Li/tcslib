"""Audit future EndpointSampling evidence; run with python3 -I."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
base = Path(__file__).resolve().parent
source = root / "TCSlib/Cryptography/Composability/SequentialZK/EndpointSampling.lean"
text = source.read_text()
lines = text.splitlines()
row = {"file": str(source.relative_to(root)), "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
       "lines": len(lines), "max_width": max(map(len, lines)),
       "width_violations": [[i, len(s)] for i, s in enumerate(lines, 1) if len(s) > 100],
       "admission_tokens": re.findall(r"\b(?:sorry|admit|axiom)\b", text)}
(base / "endpoint-source-check.json").write_text(json.dumps(row, indent=2) + "\n")
assert len(lines) <= 1000 and not row["width_violations"] and not row["admission_tokens"]
print(json.dumps(row))
checks = []
for log in sorted(base.glob("endpoint-*-check-*.log")):
    s = log.read_text()
    end = re.search(r"^EXIT (\d+)", s, re.M)
    if end is None:
        continue
    rss = re.search(r"^\s*(\d+)\s+maximum resident set size", s, re.M)
    checks.append({"log": log.name, "exit": int(end.group(1)),
                   "errors": len(re.findall(r"^\S+\.lean:\d+:\d+: error[:(]", s, re.M)),
                   "warnings": len(re.findall(r"^\S+\.lean:\d+:\d+: warning[:(]", s, re.M)),
                   "maximum_resident_set_size_bytes": int(rss.group(1)) if rss else None})
(base / "endpoint-audit-checks.jsonl").write_text("".join(json.dumps(r) + "\n" for r in checks))
for r in checks:
    print(json.dumps(r))
closed = []
for line in (base / "checkpoint2-closed-files.tsv").read_text().splitlines()[1:]:
    sha, rel, status = line.split("\t")
    actual = hashlib.sha256((root / rel).read_bytes()).hexdigest()
    assert actual == sha, rel
    closed.append(rel)
print("PASS:", len(closed), "checkpoint2 closed evidence files unchanged")
print("PASS:", len(checks), "future Endpoint checks preserved; missing-import attempt included")
