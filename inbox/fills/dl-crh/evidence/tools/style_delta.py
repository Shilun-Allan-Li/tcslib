#!/usr/bin/env python3
"""Recover the verbatim issue-tree lint log and compare diagnostics. Use python3 -I."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
from zipfile import ZipFile


def sha(data):
    return hashlib.sha256(data).hexdigest()


def diagnostics(data):
    result = Counter()
    for line in data.decode().splitlines():
        match = re.match(r"^(FAIL|WARN)\s+(TCSlib/\S+)\s+(.*)$", line)
        if match:
            result[match.groups()] += 1
    return result


def entries(counter):
    return [dict(status=k[0], path=k[1], message=k[2], count=v)
            for k, v in sorted(counter.items())]


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--archive", type=Path, default=Path("evidence/initial-escalation.zip"))
parser.add_argument("--entry", default="dl-crh/evidence/logs/style-lint.log")
parser.add_argument("--base-log", type=Path, default=Path("evidence/logs/style-base.log"))
parser.add_argument("--final-log", type=Path, default=Path("evidence/logs/style-final.log"))
parser.add_argument("--report", type=Path, default=Path("evidence/style-delta.md"))
parser.add_argument("--json", type=Path, default=Path("evidence/style-delta.json"))
args = parser.parse_args()
with ZipFile(args.archive) as archive:
    assert archive.testzip() is None
    original = archive.read(args.entry)
args.base_log.parent.mkdir(parents=True, exist_ok=True)
args.base_log.write_bytes(original)
assert args.base_log.read_bytes() == original
final = args.final_log.read_bytes()
base_diag, final_diag = diagnostics(original), diagnostics(final)
added, removed = final_diag - base_diag, base_diag - final_diag
record = dict(
    archive=str(args.archive), archive_sha256=sha(args.archive.read_bytes()), entry=args.entry,
    base_log=str(args.base_log), base_sha256=sha(original), base_bytes=len(original),
    final_log=str(args.final_log), final_sha256=sha(final), final_bytes=len(final),
    base_counts={s: sum(v for k, v in base_diag.items() if k[0] == s) for s in ("FAIL", "WARN")},
    final_counts={s: sum(v for k, v in final_diag.items() if k[0] == s) for s in ("FAIL", "WARN")},
    added=entries(added), removed=entries(removed),
)
args.json.write_text(json.dumps(record, indent=2) + "\n")
lines = [
    "# Exact style-lint delta", "",
    f"The baseline is recovered verbatim from `{args.archive}`, entry `{args.entry}`.",
    f"`{args.base_log}` retains all {len(original):,} original bytes; no baseline lint rerun is substituted.",
    "",
    f"- Archive SHA-256: `{record['archive_sha256']}`.",
    f"- Baseline log SHA-256: `{record['base_sha256']}`.",
    f"- Final log SHA-256: `{record['final_sha256']}`.",
    "",
    "| Diagnostics | Baseline | Final | Delta |", "|---|---:|---:|---:|",
]
for status in ("FAIL", "WARN"):
    b, f = record["base_counts"][status], record["final_counts"][status]
    lines.append(f"| {status} | {b} | {f} | {f-b:+d} |")
lines += ["", "## Added diagnostics", ""]
for item in entries(added):
    lines.append(f"- {item['status']} `{item['path']}`: {item['message']} (count {item['count']}).")
if not added:
    lines.append("None.")
lines += ["", "## Removed diagnostics", ""]
for item in entries(removed):
    lines.append(f"- {item['status']} `{item['path']}`: {item['message']} (count {item['count']}).")
if not removed:
    lines.append("None.")
lines += [
    "", "The mechanical new-FAIL count is retained above. The user disposition for the six",
    "ancestor-facade diagnostics is recorded separately in `facade-lint-exception.md`.",
    "This comparison does not relabel those diagnostics as mechanical passes.", "",
]
args.report.write_text("\n".join(lines))
print(json.dumps({"base": record["base_counts"], "final": record["final_counts"],
                  "added": len(added), "removed": len(removed), "report": str(args.report)}))
