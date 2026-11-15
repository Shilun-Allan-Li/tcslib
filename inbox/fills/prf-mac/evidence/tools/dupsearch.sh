#!/usr/bin/env bash
# Duplication searches of the prf-mac fill (TCSlib at the issue base, and Mathlib/core where noted).
# usage: dupsearch.sh ROOT   (ROOT = a checkout of the issue base)
cd "$1"
s() { echo "=== rg -n '$1' ${2:-TCSlib}"; rg -n --no-heading "$1" ${2:-TCSlib} | head -${3:-25}; echo; }
s 'finish_of_query|finish_of_ret|impl_of_query'
s 'theorem .*finish.*query|finCall := \.const 1'
s 'forgerCodec_eq_bitCodec|ext_of_fields'
s 'eval_toOracleAdversary_width|toOracleAdversary n m'
s 'withLog.*length|length.*withLog|AllOutputs.*\.length|log\.length'
s 'QueryImpl\.ofComp fun _ [a-z]+ => \.pure|QueryImpl\.ofComp \(fun _ [a-z]+ => \.pure|def fOuter|tableSigner'
s 'e\.2\.1 ≠|∀ e ∈ .*, e\.2\.1'
s 'fresh|Fresh' TCSlib/Cryptography 40
s 'map fun e => e\.2\.1|map \(·\.2\.1\)|map \(fun e => e\.2\.1\)'
s 'def chunkMap|chunkMap_flatten|def blocks|flatten_replicate_replicate'
s 'def ovr|expect_sample_ovr|expect_hitW_le|expect_sample_coord|expect_sample_mem_le'
s 'splitBits_append|splitBits_pad_concat|append_castAdd_natAdd|ofFn_fin_append' TCSlib 30
s 'Equiv.*padFin|padFin.*Equiv|arrowCongr' TCSlib 30
s 'forgeGame_eq_fixed|accept_prf_indGame|forgeGame.*deterministic|tagImpl_eq'
s 'prob_mem_le|random.*forg|forg.*random' TCSlib/Cryptography 30
s 'stateLen :=' TCSlib 30
s 'polyTimeComputable_pairTakePoly|polyTimeComputable_pairDropPoly' TCSlib/Cryptography 20
s 'runAt_coinKey|coinsEquivPoly|coinsEquiv_ofPolyTimeUniform|prfKeyEq|KeyEq' TCSlib/Cryptography 40
s 'eval_toOracleAdversary|ofFn_evalFn_toCompOn|expect_toCompOn_outLen' TCSlib 20
echo "=== Mathlib/core names used (existence)"
for n in List.flatten_replicate_replicate Fin.append_castAdd_natAdd List.ofFn_fin_append List.take_append List.take_replicate List.flatten_eq_nil_iff decide_eq_decide; do
  echo "$n: $(rg -l --no-heading "theorem ${n##*.}\b" .lake/packages/mathlib/Mathlib ~/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init 2>/dev/null | head -2 | tr '\n' ' ')"; done
