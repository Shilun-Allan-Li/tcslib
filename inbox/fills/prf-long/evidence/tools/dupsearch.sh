#!/usr/bin/env bash
# Duplication searches of the prf-long fill (TCSlib at the issue base; Mathlib/core where noted).
# usage: dupsearch.sh ROOT   (ROOT = a checkout of the issue base)
cd "$1"
s() { echo "=== rg -n '$1' ${2:-TCSlib}"; rg -n --no-heading "$1" ${2:-TCSlib} | head -${3:-25}; echo; }
s 'prfAdv_toOracleAdversary|negligible_prfAdv'
s 'prfOut_var_iff|structure PRFOut|PRFOut'
s 'OracleEnsemble.random \.var [^.]|ℓ₂ := ℓ|ℓ₂ :=' TCSlib 30
s 'def prfEncReal|def otpEnc|def multiMsgAdv|chainTree'
s 'Fin l → Bool|Fin \(ℓ.eval n\) → Bool' TCSlib/Cryptography 40
s 'histBlock|maskBlock|maskOf\b|histBlockLen|postFun|adviceBound' TCSlib 40
s 'exists_queryChain|queryChain|oneQuery|exists_.*_nuppt' TCSlib/Cryptography 40
s 'eval_toOracleAdversary_width|eval_toOracleAdversary_len' TCSlib 20
s 'exists_interactiveHandlerMachine|exists_toOracleAdversary_of_bitCodec' TCSlib 20
s 'chunkMap|polyTimeComputable_blockMap|blockMapFun' TCSlib 30
s 'take_drop_ofFn_blocks' TCSlib 20
s 'pushesUniform_restrict|distAdv_comp|zipWith_xor_ofFn_add' TCSlib 30
s 'zipWith_xor_xor_self' TCSlib 20
s 'encodeList_eq_flatMap|encodeTuple|encodeList' TCSlib/Cryptography 40
s 'uprob_not_injective_le|pushesUniform_comp_injective|abs_uexp_sub_le_uprob|prfAdv_congr_equiv|negligible_choose_div_two_pow' TCSlib 30
s 'exists_max_image' TCSlib/Cryptography 20
s 'funUnique|coinsCongr' TCSlib/Cryptography 30
# added for the final run (names of the delivered declarations; Mathlib/core flatten lemmas)
s 'encodeTupleOut|prfEncRealOut|otpEncOut|multiMsgAdvOut|histBlockOut|maskBlockOut|maskOfOut|postFunOut|adviceBoundOut|histBlockLenOut' TCSlib 60
s 'exists_negligible_distAdv|exists_queryChainOut|exists_oneQuery' TCSlib 20
s 'flatMap.*pairEncode .* \[\]|encodeList.*flatten|encodeList.*flatMap' TCSlib 20
s 'theorem flatMap_ofFn|flatMap_eq_flatten|flatten_ofFn' .lake/packages/mathlib/Mathlib 20
