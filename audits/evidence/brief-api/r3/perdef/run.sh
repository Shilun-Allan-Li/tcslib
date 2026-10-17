#!/bin/bash
# Per-definition irreducibility runs over CfgRecord at 4624fc05 against oleans-lbapi3, one at a time.
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
G=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/review/bapi-gate-r2
W=$G/wt
while read -r d; do
  [ -z "$d" ] && continue
  python3 -I $S/review/scripts/irred_copy2.py $G/edit/CfgRecord.orig.lean /dev/null $W/PerDef_CfgRecord.lean "$d" > /dev/null
  s=$(date +%s)
  bash $S/tools/leanelab.sh $W $S/oleans-lbapi3 PerDef_CfgRecord.lean > "$G/perdef/$d.out" 2>&1
  echo "exit=$? elapsed=$(( $(date +%s) - s ))s" >> "$G/perdef/$d.out"
  echo "$d $(grep -cE '^PerDef_CfgRecord.lean:[0-9]+:[0-9]+: error' "$G/perdef/$d.out") errors $(tail -1 "$G/perdef/$d.out")"
done < $G/out/perdef-candidates.txt
echo DONE
