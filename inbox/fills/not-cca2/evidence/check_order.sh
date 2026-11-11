#!/usr/bin/env bash
set -euo pipefail
order="$1"
phase="$2"
evidence=/workspace/scratch/2ed4170fb4ae/not-cca2/evidence
export PATH=/workspace/scratch/2ed4170fb4ae/toolchain/lean-4.25.0-linux/bin:$PATH
export TMPDIR=/workspace/scratch/2ed4170fb4ae/tmp
export XDG_CACHE_HOME=/workspace/scratch/2ed4170fb4ae/cache
mkdir -p "$evidence/logs/$phase"
index=0
while IFS= read -r module; do
  index=$((index+1))
  log="$evidence/logs/$phase/$(printf '%03d' "$index")-${module##*/}.log"
  date -u +'%Y-%m-%dT%H:%M:%SZ' > "$log"
  printf 'MODULE %s\n' "$module" >> "$log"
  printf 'Checking %03d %s\n' "$index" "$module"
  status=0
  python3 -I "$evidence/time_check.py" "$module" >> "$log" 2>&1 || status=$?
  date -u +'%Y-%m-%dT%H:%M:%SZ' >> "$log"
  printf 'EXIT %s\n' "$status" >> "$log"
  printf '%s\t%s\t%s\n' "$index" "$module" "$status" >> "$evidence/logs/$phase.tsv"
  if [ "$status" -ne 0 ]; then cat "$log"; exit "$status"; fi
done < "$order"
printf 'PASS: %s modules in %s\n' "$index" "$phase"
