#!/usr/bin/env bash
# Compile every explicit-unfold scan module of a directory (one Lean process at a time) and
# collect the resolved rows.  Usage: rwids_run.sh <worktree> <dir (relative)> <raw log> <tsv>
set -u
wt="$1"; dir="$2"; raw="$3"; tsv="$4"
cd "$wt"
: > "$tsv"
for f in "$dir"/*.lean; do
  m="${f%.lean}"
  echo "=== $m" >> "$raw"
  WT="$wt" /workspace/ett-tools/check.sh "$m" "$raw.tmp" > /dev/null 2>&1
  cat "$raw.tmp" >> "$raw"
  grep -P '^[^\t ]+\t[^\t]+\t[^\t]+\t[^\t]+$' "$raw.tmp" | sed "s|^|$(basename $m)\t|" >> "$tsv"
  rm -f "$raw.tmp"
  echo "$(basename $m) $(grep -c "" "$tsv")"
done
