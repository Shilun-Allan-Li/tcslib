#!/usr/bin/env bash
# elab.sh <worktree> <file-rel> <outfile> : elaborate via leanelab.sh against oleans-leqc3; log times
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/nf-cont1-fill
WT="$1"; F="$2"; O="$3"; OL="${OL:-$S/oleans-leqc3}"
echo "queued $(date -u +%FT%TZ) $F" >> $R/out/00-runs.txt
st=$(date +%s)
bash $S/tools/leanelab.sh "$WT" "$OL" "$F" > "$O" 2>&1; ec=$?
en=$(date +%s)
echo "exit=$ec" >> "$O"
echo "done $(date -u +%FT%TZ) $F exit=$ec wall_incl_wait=$((en-st))s -> $(basename $O)" >> $R/out/00-runs.txt
