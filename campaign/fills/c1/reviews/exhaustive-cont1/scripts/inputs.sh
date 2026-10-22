#!/usr/bin/env bash
S=/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad
R=$S/review/c1-exhaustive-cont1-fill; WB=$R/wt-base; C=$S/wt-hk/campaign/fills/c1
DISP=/Users/seyoonr/phd_experiments/tcslib/exchange/archive/fills/c1-fill-exhaustive-cont1.md
sha(){ shasum -a 256 "$1" | cut -c1-16; }
echo '# brief and inputs: base copies vs records (tip) copies vs dispatch'
echo "dispatch brief $(sha $DISP)"
echo "base briefs/c1-fill-exhaustive-cont1.md $(sha $WB/briefs/c1-fill-exhaustive-cont1.md)"
echo "records campaign/fills/c1/briefs/c1-fill-exhaustive-cont1.md $(sha $C/briefs/c1-fill-exhaustive-cont1.md)"
echo '$ diff base brief vs dispatch'; diff $WB/briefs/c1-fill-exhaustive-cont1.md $DISP
echo '$ diff base brief vs records brief'; diff $WB/briefs/c1-fill-exhaustive-cont1.md $C/briefs/c1-fill-exhaustive-cont1.md
echo "addendum dispatch $(sha /Users/seyoonr/phd_experiments/tcslib/exchange/outbox/fills/fill-environment-addendum.md) base $(sha $WB/briefs/fill-environment-addendum.md)"
while read a b; do x=$(sha $WB/$a); y=$(sha $C/$b); echo "$a base=$x records=$y $([ "$x" = "$y" ] && echo SAME || echo DIFF)"; done <<'L'
audits/evidence/c1-fill-exhaustive-cont1/ExhaustiveReplayOverlay.lean.txt inputs/c1-fill-exhaustive-cont1/ExhaustiveReplayOverlay.lean.txt
audits/evidence/c1-fill-exhaustive-cont1/C1ExhaustiveImportProbe.lean.txt inputs/c1-fill-exhaustive-cont1/C1ExhaustiveImportProbe.lean.txt
audits/evidence/c1-fill-exhaustive-cont1/screen-population.txt inputs/c1-fill-exhaustive-cont1/screen-population.txt
briefs/orders/c1-fill-exhaustive-cont1.txt orders/c1-fill-exhaustive-cont1.txt
audits/logs/c1-fill-exhaustive-cont1-base-sorries.txt logs/c1-fill-exhaustive-cont1-base-sorries.txt
audits/logs/c1-fill-exhaustive-cont1-screen-base.txt logs/c1-fill-exhaustive-cont1-screen-base.txt
audits/logs/c1-fill-exhaustive-cont1-preship.log logs/c1-fill-exhaustive-cont1-preship.log
audits/evidence/c1/fills/exhaustive-1/C1ReviewProbes.lean.txt reviews/exhaustive-1/C1ReviewProbes.lean.txt
audits/evidence/c1/fills/exhaustive-1/REVIEW.md reviews/exhaustive-1/REVIEW.md
L
echo "order list modules: $(grep -v '^#' $WB/briefs/orders/c1-fill-exhaustive-cont1.txt | grep -c .)"
echo "probe #check count: $(grep -c '^#check' $WB/audits/evidence/c1-fill-exhaustive-cont1/C1ExhaustiveImportProbe.lean.txt)"
echo '$ population'; cat $WB/audits/evidence/c1-fill-exhaustive-cont1/screen-population.txt
echo '$ base sorries'; cat $WB/audits/logs/c1-fill-exhaustive-cont1-base-sorries.txt
