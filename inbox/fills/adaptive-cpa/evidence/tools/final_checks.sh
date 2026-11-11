#!/usr/bin/env bash
# final_checks.sh : census, seals with controls, full sweep, admissions, axioms (one Lean process at a time)
E=/home/user/acpa/payload/evidence; L=$E/logs; cd /home/user/fill
/home/user/tools/chk AcpaProbe/Refs $L/refs-final.log > /dev/null 2>&1; echo "census: $(tail -1 $L/refs-final.log) decls=$(grep -c 'DECL|' $L/refs-final.log)"
python3 -I /home/user/tools/make_seal2.py /home/user/fill $L/refs-final.log $E /home/user/acpa/controls.json > $L/seal-candidates.log
for t in Hybrid Handler Games Reduction Owned; do
  /home/user/tools/chk AcpaProbe/Seal$t $L/seal-$t.log > /dev/null 2>&1
  echo "seal $t: $(tail -1 $L/seal-$t.log) sealed=$(grep -c 'SEALED|' $L/seal-$t.log) instance-aliases=$(grep -c 'INSTANCE_ALIAS|' $L/seal-$t.log) errors=$(grep -c 'error' $L/seal-$t.log) sorry=$(grep -c "uses 'sorry'" $L/seal-$t.log)"
  for w in Before After; do
    /home/user/tools/chk AcpaProbe/Control$t$w $L/control-$t-$w.log > /dev/null 2>&1
    echo "  control $t $w: $(tail -1 $L/control-$t-$w.log) $(grep -o 'error: [^:]*' $L/control-$t-$w.log | head -1)"
  done
done | tee $L/seal-summary.log
cd $E && rm -rf logs/sweep logs/sweep.tsv && /home/user/tools/sweep.sh order.txt logs/sweep logs/sweep.tsv | tee logs/sweep-summary.log
awk -F'\t' '{s+=$5; if($4>m)m=$4; t+=$3} END {print "sweep sorries",s,"max RSS KiB",m,"lean seconds",t}' logs/sweep.tsv | tee -a logs/sweep-summary.log
cd /home/user/fill && python3 -I /home/user/tools/sorry_compare.py $L/sweep.tsv $L/sweep $E/inputs/base-sorries.txt > $L/sweep-admissions.log; tail -2 $L/sweep-admissions.log
/home/user/tools/chk AcpaProbe/Axioms $L/axioms-final.log > /dev/null 2>&1; grep -c 'depends on axioms' $L/axioms-final.log
echo FINAL-CHECKS-DONE
