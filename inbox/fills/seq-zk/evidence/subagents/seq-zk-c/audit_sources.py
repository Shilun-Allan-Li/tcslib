"""Audit the seq-zk-c source files; run with python3 -I."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
base = Path(__file__).resolve().parent
names = ["Soundness", "Phases", "Congruence", "VerifierPrefix", "ErrSoundness",
         "RepeatedVerifier", "RepeatedSoundness", "Advice", "StatisticalPostprocess"]
rows = []
for name in names:
    rel = Path("TCSlib/Cryptography/Composability/SequentialZK") / (name + ".lean")
    path = root / rel
    data = path.read_bytes()
    text = data.decode()
    lines = text.splitlines()
    rows.append({"file": str(rel), "lines": len(lines),
                 "max_width": max(map(len, lines), default=0),
                 "width_violations": [[i, len(s)] for i, s in enumerate(lines, 1)
                                      if len(s) > 100],
                 "size_ok": len(lines) <= 1000,
                 "sha256": hashlib.sha256(data).hexdigest(),
                 "admission_tokens": re.findall(r"\b(?:sorry|admit|axiom)\b", text)})
(base / "audit-sources.json").write_text(json.dumps(rows, indent=2) + "\n")
for row in rows:
    print(json.dumps(row))
assert all(r["size_ok"] and not r["width_violations"] and not r["admission_tokens"]
           for r in rows)
print(f"PASS: {len(rows)} source files, all within bounds, no admission tokens")
