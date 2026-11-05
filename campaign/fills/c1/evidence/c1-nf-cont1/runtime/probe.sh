#!/usr/bin/env bash
# probe.sh <outdir> : the import probe extended by the walk's external names not in it; run it
set -u
source ~/.elan/env
cd /home/user/tcslib
OD="$1"; P=campaign/fills/c1/inputs/c1-fill-nf-cont1/NFContImportProbe.lean.txt
grep '^#check @' $P | sed 's/^#check @//' | sort -u > "$OD/probe-names.txt"
cut -f1 "$OD/walk-ext.tsv" | sort -u > "$OD/cited-names.txt"
comm -23 "$OD/cited-names.txt" "$OD/probe-names.txt" > "$OD/probe-extra.txt"
{ cat $P; echo; echo "-- the continuation's citations beyond the probe (from the elaborated-constant walk)"
  while read -r n; do echo "#check @$n"; done < "$OD/probe-extra.txt"; } > scratch/NFProbeExt.lean
cp scratch/NFProbeExt.lean "$OD/NFProbeExt.lean"
bash scripts/lean_check_tree.sh scratch/NFProbeExt > "$OD/probe-run.log" 2>&1; echo "exit: $?" >> "$OD/probe-run.log"
echo "checks: $(grep -c '^#check' scratch/NFProbeExt.lean) ; names cited: $(wc -l < "$OD/cited-names.txt") ; extra: $(wc -l < "$OD/probe-extra.txt") ; errors: $(grep -c 'error' "$OD/probe-run.log")"
