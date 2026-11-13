#!/usr/bin/env bash
# Grep receipts for group G, at the issue base (git grep on the base commit).
BASE=d3f2290a2c66f614e8807903b89ac595086578b3
cd /workspace/folds
run() { echo "### $1"; echo "\$ git grep -nE '$2' $BASE -- TCSlib audits"; git grep -nE "$2" $BASE -- TCSlib audits | sed "s/^$BASE://" ; echo; }
run G1-budget 'buildComp_budget_eq|toCompOn_budget_eq|CostBoundedBy \(fun _ => 1\) j'
run G1-ret 'buildComp_of_ret|buildComp_zero_of_ret h$|=> exact buildComp_zero_of_ret'
run G2-impl 'impl_of_ret|impl_of_query|finish_of_ret|theorem .*impl_.*(ret|query)'
run G2-buildComp-use 'buildComp_succ_of_query|buildComp_zero_of_ret|buildComp_succ_of_ret'
run G3 'expect_toCompOn_outLen|bitCodec ins outs d.\)'
run G4-congr 'expect_congr_of_allOutputs|le_antisymm \(.*expect_mono_of_allOutputs'
run G4-sample 'expect_expect_sample|expect_const_mul, (ProbComp\.)?expect_sum'
run G4-bind 'bind_congr_of_allOutputs|bind_congr|c\.bind f = c\.bind g'
run G4-cost 'costBoundedBy_bind_of_allOutputs|Nat\.sub_add_comm hi'
run G4-once 'simulate_costBoundedBy_once|if used s then 0 else 1'
run G5 'expect_simulate_eager|simulate_eq_of_used|Classical\.arbitrary T'
run G6 'expect_eq_until_bad|prob_eq_until_bad|if bad r\.2 then 0 else G'
run G7-fwd 'fwdHandler|fwdRun|perCall := \.const 1'
run G7-advice 'exists_withAdviceOn|pairEncode \(pairEncode \(pairFstD \(pairFstD w\)\) \(pairSndD w\)\)'
run G7-readers 'cntRead|ansRead|if decide \(v = \[\]\) then \[\] else \[true\]|pairSndD \(pairSndD \(pairFstD'
