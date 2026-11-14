#!/usr/bin/env python3
"""Compare a completed serial sweep's raw sorry warnings with the issued baseline.

Use python3 -I. Refuses incomplete/failed sweeps, changed sources, or unverified raw
logs. It maps each warning's source location to that declaration's source name.
No Lean process is started. Run only after all expected module checks finish.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_module(name):
    if name.startswith("TCSlib/"):
        return name
    return "TCSlib/Complexity/" + name


def baseline(path):
    result = Counter()
    declared_total = None
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        if line.startswith("TOTAL "):
            declared_total = int(line.split()[1])
            continue
        match = re.fullmatch(r"(.+): (\d+): (.+)", line)
        assert match, ("unrecognized baseline row", line)
        names = [name.strip() for name in match[3].split(",")]
        assert len(names) == int(match[2]), line
        for name in names:
            result[(canonical_module(match[1]), name)] += 1
    assert declared_total == sum(result.values()), ("baseline total", declared_total, result)
    return result


def declarations(counter):
    return [dict(module=k[0], declaration=k[1], count=v) for k, v in sorted(counter.items())]


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--order", type=Path, default=Path("evidence/final-order.txt"))
parser.add_argument("--results", type=Path, default=Path("evidence/logs/final-sweep/results.jsonl"))
parser.add_argument("--baseline", type=Path, default=Path("evidence/inputs/base-sorries.txt"))
parser.add_argument("--expected-modules", type=int, default=176)
parser.add_argument("--report", type=Path, default=Path("evidence/admission-delta.md"))
parser.add_argument("--json", type=Path, default=Path("evidence/admission-delta.json"))
args = parser.parse_args()
order = [line.strip() for line in args.order.read_text().splitlines() if line.strip()]
assert len(order) == len(set(order)) == args.expected_modules, ("order length", len(order))
records = [json.loads(line) for line in args.results.read_text().splitlines() if line.strip()]
latest = {record["module"]: record for record in records}
assert set(latest) == set(order), ("incomplete/unexpected sweep modules", sorted(set(order)-set(latest)),
                                   sorted(set(latest)-set(order)))
warn_re = re.compile(r"^(.*\.lean):(\d+):(\d+): warning: declaration uses 'sorry'\s*$")
decl_re = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
                     r"(?:theorem|lemma|def|abbrev|opaque|instance)\s+([^\s:({\[]+)")
found = Counter()
locations = []
for module in order:
    record = latest[module]
    assert record["exit_code"] == 0 and record["source_unchanged"], ("failed/changed check", record)
    assert record["source_sha256"] == record["source_after_sha256"], record
    source, log = Path(module + ".lean"), Path(record["log"])
    assert sha(source) == record["source_sha256"], ("source changed since sweep", source)
    assert sha(log) == record["log_sha256"], ("raw log changed", log)
    source_lines = source.read_text().splitlines()
    for log_line_number, line in enumerate(log.read_text(errors="strict").splitlines(), 1):
        assert ": error:" not in line, ("raw error", log, log_line_number, line)
        if "declaration uses 'sorry'" not in line:
            continue
        match = warn_re.fullmatch(line)
        assert match, ("unparsed sorry warning", log, log_line_number, line)
        warning_source = Path(match[1])
        assert warning_source.resolve() == source.resolve(), ("foreign warning", line, module)
        line_number, column = int(match[2]), int(match[3])
        assert 1 <= line_number <= len(source_lines), line
        # A warning points to the declaration command. Permit a name on its next
        # line, but never silently guess a preceding declaration from a proof body.
        header = "\n".join(source_lines[line_number-1:line_number+20])
        declaration = decl_re.match(header)
        assert declaration, ("warning location is not a declaration header", line,
                             source_lines[line_number-1])
        name = declaration[1]
        found[(module, name)] += 1
        locations.append(dict(module=module, declaration=name, line=line_number, column=column,
                              log=str(log), log_line=log_line_number, raw=line))
base = baseline(args.baseline)
target = ("TCSlib/Cryptography/Hashing/FromDiscreteLog", "dlHash_crh")
assert base[target] == 1, ("target missing from issued baseline", target)
expected = base.copy()
expected[target] -= 1
expected += Counter()  # Drop zero entries.
added, removed = found-base, base-found
passed = found == expected
data = dict(status="PASS" if passed else "FAIL", module_count=len(order), record_count=len(records),
            order_sha256=sha(args.order), results_sha256=sha(args.results), baseline_sha256=sha(args.baseline),
            baseline_total=sum(base.values()), final_total=sum(found.values()),
            added=declarations(added), removed=declarations(removed),
            final=declarations(found), warning_locations=locations)
args.json.write_text(json.dumps(data, indent=2) + "\n")
lines = ["# Exact admission delta", "", f"Status: **{data['status']}**.", "",
         f"Verified {len(order)} completed successful modules from `{args.results}`; raw log hashes",
         "and the checked source hashes match. For retries, only each module's latest record is used.", "",
         f"Baseline: {data['baseline_total']} admitted declarations. Final: {data['final_total']}.",
         "Required delta: remove only `TCSlib/Cryptography/Hashing/FromDiscreteLog.dlHash_crh`.",
         "", "## Removed", ""]
for item in declarations(removed):
    lines.append(f"- `{item['module']}`: `{item['declaration']}` (count {item['count']}).")
if not removed:
    lines.append("None.")
lines += ["", "## Added", ""]
for item in declarations(added):
    lines.append(f"- `{item['module']}`: `{item['declaration']}` (count {item['count']}).")
if not added:
    lines.append("None.")
lines += ["", "The JSON companion retains every raw warning, its log/source location, and the full final list.", ""]
args.report.write_text("\n".join(lines))
print(json.dumps({k: data[k] for k in ("status", "module_count", "baseline_total", "final_total", "added", "removed")}))
raise SystemExit(0 if passed else 1)
