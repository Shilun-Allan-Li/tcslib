"""Count both Lean error diagnostic forms; run with python3 -I."""
from pathlib import Path
import json
import re

base = Path(__file__).resolve().parent
logs = sorted(set(base.glob("check-*.log")) | set(base.glob("*-check-*.log")))
rows = []
for path in logs:
    text = path.read_text()
    end = re.search(r"^EXIT (\d+)", text, re.M)
    if end is None:
        continue
    mem = re.search(r"^\s*(\d+)\s+maximum resident set size", text, re.M)
    rows.append({"log": path.name, "exit": int(end.group(1)),
                 "errors": len(re.findall(r"^\S+\.lean:\d+:\d+: error[:(]", text, re.M)),
                 "warnings": len(re.findall(r"^\S+\.lean:\d+:\d+: warning[:(]", text, re.M)),
                 "maximum_resident_set_size_bytes": int(mem.group(1)) if mem else None})
(base / "audit-logs.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
for row in rows:
    print(json.dumps(row))
print("Retained", len(rows), "raw check attempts; interrupted attempt01 is documented")
