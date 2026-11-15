"""Audit all c-owned final sources and future evidence; run with python3 -I."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
base = Path(__file__).resolve().parent
names = ["Soundness", "Phases", "Congruence", "VerifierPrefix", "ErrSoundness",
         "RepeatedVerifier", "RepeatedSoundness", "Advice", "StatisticalPostprocess",
         "EndpointSampling", "HybridRecursion", "SuffixLaws", "ComputationalAdvice",
         "ContinuationProbability", "ComputationalHybrid"]
rows = []
for name in names:
    rel = Path("TCSlib/Cryptography/Composability/SequentialZK") / (name + ".lean")
    p = root / rel
    text = p.read_text()
    lines = text.splitlines()
    row = {"file": str(rel), "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
           "lines": len(lines), "max_width": max(map(len, lines)),
           "width_violations": [[i, len(s)] for i, s in enumerate(lines, 1) if len(s) > 100],
           "admission_tokens": re.findall(r"\b(?:sorry|admit|axiom)\b", text)}
    assert len(lines) <= 1000 and not row["width_violations"] and not row["admission_tokens"]
    rows.append(row)
(base / "future-audit-sources.json").write_text(json.dumps(rows, indent=2) + "\n")
for r in rows:
    print(json.dumps(r))
checks = []
for p in sorted(set(base.glob("check-*.log")) | set(base.glob("*-check-*.log"))):
    s = p.read_text()
    end = re.search(r"^EXIT (\d+)", s, re.M)
    if end is None:
        continue
    rss = re.search(r"^\s*(\d+)\s+maximum resident set size", s, re.M)
    checks.append({"log": p.name, "exit": int(end.group(1)),
                   "errors": len(re.findall(r"^\S+\.lean:\d+:\d+: error[:(]", s, re.M)),
                   "warnings": len(re.findall(r"^\S+\.lean:\d+:\d+: warning[:(]", s, re.M)),
                   "maximum_resident_set_size_bytes": int(rss.group(1)) if rss else None})
(base / "future-audit-checks.jsonl").write_text("".join(json.dumps(r) + "\n" for r in checks))
closed = []
for line in (base / "checkpoint2-closed-files.tsv").read_text().splitlines()[1:]:
    sha, rel, status = line.split("\t")
    assert hashlib.sha256((root / rel).read_bytes()).hexdigest() == sha, rel
    closed.append(rel)
print("PASS:", len(rows), "owned source files, within size/width bounds, no admissions")
print("PASS:", len(checks), "raw native attempts retained, both diagnostic forms counted")
print("PASS:", len(closed), "checkpoint2 closed evidence files unchanged")
