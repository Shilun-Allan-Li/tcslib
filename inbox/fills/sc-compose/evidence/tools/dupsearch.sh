#!/usr/bin/env bash
# Duplication searches of the sc-compose fill (statement shapes and key names of the new
# declarations, over TCSlib and the Mathlib/Batteries sources).
# usage: dupsearch.sh ROOT   (ROOT = a checkout: the issue base, or the final tree)
cd "$1"
s() { echo "=== rg -n '$1' ${2:-TCSlib}"; rg -n --no-heading "$1" ${2:-TCSlib} | head -${3:-25}; echo; }
s 'theorem polyTimeComputable_flatMap_range|theorem flatMap_range_ite\b|flatMap_range_ite_eq' TCSlib 20
s 'theorem iterSnd_poly|iterUnary_poly|pairSndD\^\[' TCSlib 30
s 'getD_eq_pairFstD_iterate|theorem msgAt|pairFstD_encodeMsgs|iterate_pairSndD_encodeMsgs' TCSlib 20
s 'theorem encodeMsgs_eq_flatMap|theorem encodeMsgs_append|encodeMsgs \(.* \+\+' TCSlib 20
s 'slotMsgs' TCSlib/Cryptography 30
s 'def ilayout|theorem efficient_of_polyTime|Efficient.exists|exists_polyTime' TCSlib 20
s 'def padTo|def padL|theorem ofFn_padFin|padTo_poly|polyTimeComputable_padL|zeros_poly|polyTimeComputable_zeros' TCSlib 30
s 'def argX|def argZ|def argM' TCSlib 20
s 'moverIsV.*% 2|theorem moverIsV' TCSlib 20
s 'flatten_ofFn|ofFn_eq_map.*flatten|map_coe_finRange' TCSlib 20
s 'theorem distAdv_triangle|distAdv_le_add|abs_sub_le .*acceptProb' TCSlib 20
s 'abs_uexp_sub_le_uprob|abs_uprob_sub_le|distAdv_le_uprob|agree' TCSlib/Cryptography 30
s 'acceptProb_coins_fst|acceptProb_seed|uprob_fst' TCSlib 20
s 'exists_abs_sub_le|exists_abs_uexp|sections' TCSlib/Cryptography 20
s 'funSplitAt|piSplitAt|uprob_coord' TCSlib 20
s 'polyExpr_mul|negligible_polyExpr' TCSlib 20
s 'theorem exists_withAdvice|theorem exists_split|theorem exists_seq|theorem exists_comp|def wrap|def preComp' TCSlib 20
s 'ofFn_blocks_symm|blocks_symm_apply|ofFn_splitCoins|appendEquiv' TCSlib 20
s 'theorem ofFn_mul|theorem ofFn_fin_append' .lake/packages/mathlib/Mathlib/Data/List 10
s 'def segW|asmView|def asmW|filter.*moverIsV' TCSlib 20
s 'length_filter.*% 2|filter.*% 2 ==' TCSlib 20
s 'length_encodeMsgs|length_encWords_le|theorem length_layout|output_length_le|length_runAt' TCSlib 20
s 'length_transcript|transcript.*\.length ≤|length_exec' TCSlib 20
s 'theorem length_answers|answersA.*length' TCSlib 20
s 'theorem uexp_le|uexp_le_of|sum_le_card_nsmul.*uexp' TCSlib 20
s 'acceptProb_pre|acceptProb_post|coinsSplit|appendCoins|blocksCoins|coinBlock_flatten' TCSlib 20
s 'runAtL .*take|r\.take .*coinLen|drop .*coinLen' TCSlib/Cryptography 20
s 'eqW|polyTimeComputable_eqW|eqTest_poly' TCSlib/Cryptography 20
s 'acceptProb_test|distinguisherL.*= \[true\]|decide \(.*runAt.*\[true\]' TCSlib 20
s 'outP.*≠|outV.*≠|correct.*HBCSecure|exists_correct' TCSlib/Cryptography 20
s 'hybV|plugV|Function.update .* i|resample' TCSlib/Cryptography 20
s 'abs_sub_le_sum_hybrids|exists_hybrid_gap' TCSlib 20
s 'getD_append|getElem\?_append_right.*getD|getD_plug' TCSlib 20
s 'tmplW|template' TCSlib/Cryptography 20
s 'exists_max_image' TCSlib/Cryptography 20
s 'Negligible.*max|negligible_max|Negligible.add' TCSlib/Cryptography/Foundations 20
