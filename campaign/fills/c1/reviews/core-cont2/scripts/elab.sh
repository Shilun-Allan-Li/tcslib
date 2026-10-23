#!/usr/bin/env bash
# usage: elab.sh <worktree> <olean dir> <file relative to worktree> <out file>
# One elaboration through the maintainer's throttled leanelab.sh; records start/end/exit.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$1"; OL="$2"; F="$3"; OUT="$4"
{ echo "# leanelab: wt=$WT oleans=$OL file=$F"; echo "# file sha256 $(shasum -a 256 < "$WT/$F" | cut -c1-64)"; echo "# start $(date -u +%FT%TZ)"; } > "$OUT"
bash $S/tools/leanelab.sh "$WT" "$OL" "$F" >> "$OUT" 2>&1; st=$?
{ echo "# end $(date -u +%FT%TZ) exit=$st"; echo "# errors: $(grep -c ': error' "$OUT") warnings: $(grep -c ': warning' "$OUT")"; } >> "$OUT"
exit $st
