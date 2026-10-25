#!/usr/bin/env bash
# usage: elab.sh <worktree> <olean dir> <file> <out>
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
WT="$1"; OL="$2"; F="$3"; OUT="$4"
start=$(date -u +%FT%TZ); t0=$(date +%s)
/usr/bin/time -l bash $S/tools/leanelab.sh "$WT" "$OL" "$F" > "$OUT" 2> "$OUT.time"
rc=$?
t1=$(date +%s)
{ echo "worktree: $WT"; echo "oleans: $OL"; echo "file: $F"; echo "sha256: $(shasum -a 256 "$WT/$F" 2>/dev/null || shasum -a 256 "$F")"; echo "start: $start end: $(date -u +%FT%TZ) wall(incl. slot wait): $((t1-t0)) s"; echo "exit: $rc"; echo "errors: $(grep -c ': error' "$OUT")"; echo "warnings: $(grep -c ': warning' "$OUT")"; grep -E 'maximum resident|real' "$OUT.time"; } > "$OUT.status"
