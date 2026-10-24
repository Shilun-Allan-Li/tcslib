#!/usr/bin/env bash
# usage: elab.sh <worktree> <olean dir> <file.lean relative to worktree> <out file>
# One elaboration through the throttled tools/leanelab.sh; records start, end, exit status.
WT="$1"; OL="$2"; FILE="$3"; OUT="$4"
{ echo "# leanelab.sh $WT $OL $FILE"; echo "# start $(date -u +%FT%TZ)"; } > "$OUT"
bash /private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/tools/leanelab.sh "$WT" "$OL" "$FILE" >> "$OUT" 2>&1
rc=$?
echo "# end $(date -u +%FT%TZ) exit=$rc" >> "$OUT"
