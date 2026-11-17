#!/usr/bin/env bash
# Re-run every bp probe against the final tree, each guarded to 110 s.
L=/home/user/work/evidence/subagents/bp/probes-final.log
for p in P0_Axioms P1_YieldOrder P2_Commutator P3_Conjugator P3b_ConjugatorAll P4_ComplementLast P5a_Barrington P5b_Barrington P5c_Barrington P6_Host P7_Converse; do
  /home/user/work/evidence/subagents/bp/guarded_check.sh evidence/probes/$p $L
done
