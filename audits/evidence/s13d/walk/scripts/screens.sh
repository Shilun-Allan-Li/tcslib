#!/usr/bin/env bash
# The walk unit's two v3 screens, one at a time under nice -n 10 (base tree, then the overlay tree).
S=<S>
Wk=$S/walk/work; L=$S/walk/logs; V=$S/wt-hk/audits/evidence/retrofit/copy-text-screen-v3.py
for t in base ov; do
  ( cd $Wk/${t}tree && { echo "# lockstep-walk unit: copy-text screen (v3), $t tree (base = #108's head a9ee4701)"; nice -n 10 python3 -I $V . $(grep -v '^#' $Wk/screen-population.txt); echo "# exit=$?"; } > $L/screen-$t.txt 2>&1 )
done
grep '^declarations' $L/screen-base.txt $L/screen-ov.txt
python3 -I $S/land-g24/scripts/screendelta.py $L/screen-base.txt $L/screen-ov.txt
