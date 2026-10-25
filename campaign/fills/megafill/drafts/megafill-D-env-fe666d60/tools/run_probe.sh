#!/usr/bin/env bash
# run_probe.sh <probe.lean.txt> <out file>: copy the probe record to the clone's ignored
# .lake/probes/<name>.lean, check it with scripts/lean_check_tree.sh under tools/runmem.py, and
# write the output, the record's SHA-256, the MEM line and the exit status to <out file>.
# Run from the clone's root, one at a time (one Lean process at a time).
set -u
src="$1"; out="$2"
tools="$(cd "$(dirname "$0")" && pwd)"
name="$(basename "$src" .lean.txt)"
mkdir -p .lake/probes
cp "$src" ".lake/probes/$name.lean"
{
  echo "# $name: record SHA-256 $(sha256sum "$src" | cut -d' ' -f1), base $(git rev-parse HEAD), $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  python3 -I "$tools/runmem.py" "$name" -- bash scripts/lean_check_tree.sh ".lake/probes/$name"
  echo "exit=$?"
} > "$out" 2>&1
tail -1 "$out"
