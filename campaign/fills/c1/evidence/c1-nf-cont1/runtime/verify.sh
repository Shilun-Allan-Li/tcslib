#!/usr/bin/env bash
# verify.sh <outdir> : the checkpoint verification set, one Lean process at a time
set -u
B=/tmp/claude-0/-home-user/e83f8996-d545-513c-8228-08a794edf16c/scratchpad/bin
cd /home/user/tcslib
OD="$1"; mkdir -p "$OD"
echo "[tail]"; $B/sweep.sh scratch/tail-order.txt "$OD/tail.log" "$OD/tail-summary.tsv"; cat "$OD/tail-summary.tsv"
grep -h "warning\|error" "$OD/tail.log" | head
echo "[walk+axioms]"; $B/walk.sh "$OD" >/dev/null
grep -v "^  " "$OD/axioms-raw.log" | grep -c "depends on axioms\|does not depend"
grep -h "sorryAx" "$OD/axioms-raw.log" | sed 's/^.*NFAxioms.0.//' | head
awk -F'\t' '$3 ~ /^TCSlib/ && ($2=="def" || $2=="opaque")' "$OD/walk-ext.tsv" | cut -f1 | sort > "$OD/reached-defs.txt"
echo "[seal]"; $B/seal.sh "$OD" "$OD/reached-defs.txt"
echo "[inspection]"; python3 $B/inspect.py TCSlib/Complexity/ClassNP/NDNormalForm.lean "$OD/walk-ext.tsv" "$OD/inspection.md"
echo "[lint]"; python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/ClassNP > "$OD/lint-campaign.txt" 2>&1; tail -1 "$OD/lint-campaign.txt"
python3 -I scripts/style_lint.py TCSlib/Complexity/ClassNP/NDNormalForm.lean > "$OD/lint-style.txt" 2>&1; cat "$OD/lint-style.txt"
python3 -c "
ls=open('TCSlib/Complexity/ClassNP/NDNormalForm.lean',encoding='utf-8').read().split('\n')
print('lines:',len(ls)-1 if ls[-1]=='' else len(ls),'; over 100 chars:',[i for i,l in enumerate(ls,1) if len(l)>100])" | tee "$OD/size.txt"
