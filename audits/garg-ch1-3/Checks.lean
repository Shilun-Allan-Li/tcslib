/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Foundations
import TCSlib.Cryptography.OneWayFunctions
import TCSlib.Cryptography.HardcoreBit
import TCSlib.Cryptography.Pseudorandom

/-!
# Garg Chapters 1–3 verification

Axiom prints for the headline theorems of the concrete layer, checking that none
depends on an admitted proof.
-/

open TCSlib.Cryptography TCSlib.Cryptography.OneWay TCSlib.Cryptography.HardcoreBit

-- Chapter 1 and foundations
#print axioms negligible_two_pow_neg
#print axioms Negligible.add
#print axioms Negligible.mul_pow
#print axioms not_negligible_sub
#print axioms exists_not_negligible_not_noticeable
#print axioms half_le_uprob_good
#print axioms exists_hybrid_gap
#print axioms distAdv_le_statDist
-- Chapter 2: one-way functions
#print axioms invProb_patch_le
#print axioms invProb_patch_le_of_correction
#print axioms invProb_update_le
#print axioms invProb_zeroPatch_eq_one
#print axioms invProb_zeroPrefix_comp_self
#print axioms invProb_zeroPrefixInverter
#print axioms invProb_dropFirst_flagged
#print axioms invProb_flagged_le
#print axioms invProb_pad_le
#print axioms exists_inverter_log_output
#print axioms yao_amplification
#print axioms yao_amplification_exp
-- Chapter 2: hard-concentrate bits
#print axioms chebyshev_pairwise
#print axioms chebyshev_pairwise_ident
#print axioms pairwiseUniform_subsetSum
#print axioms predProb_fixedBitPredictor
#print axioms invProb_perfectInverter
#print axioms invProb_majorityInverter
#print axioms invProb_guessInverter
#print axioms invProb_guessInverter_cubic
-- Chapter 3: pseudorandomness
#print axioms distAdv_sunglassRed
#print axioms exists_multicopyRed_ge
#print axioms distAdv_multicopyAvgRed
#print axioms exists_prgExtRed_ge
#print axioms prgAdv_prgExtAvgRed
#print axioms exists_prgExtBitsRed_ge
#print axioms exists_owpPredictor
#print axioms exists_owpPredictorBits
#print axioms QueryTree.uprob_evalLazy
#print axioms ggm_prfAdv_le
#print axioms exists_ggm_dist
#print axioms exists_ggmBits_dist
