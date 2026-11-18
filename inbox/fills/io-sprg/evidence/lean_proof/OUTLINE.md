# Phase A proof ladder after M0

M0 d10a560b34d58919bc1a5206ce66a444613f94c7 was published in exchange
15946b52d0615fda8afad9ed3c57cfaf5beaaa8d. Statements stay frozen.

The live Lean files are the owned StructuredSeed modules. Each step replaces one
named sorry body, checks its owner through the pinned slot wrapper, and records
source/log hashes under evidence/steps and evidence/build/M1.

M1: weighted degrees; parameter and encoding support; buckets; sparse factors;
tensor/correction algebra; sampled-seed correctness and raw complexity; LPN law.
M2: payload bound and stretch. M3: exact error probability. M4: hybrids/reductions.
M5: raw security/existence. M6: advice bounds, target links and primitive assembly.

Current direct named holes: 145. First completed body: Internal.weightedTotalDegree_add_le.
Proof-candidate packets remain untested until their individual checks pass.

Step 001: weightedTotalDegree_add_le owner check passed. Current sorry tokens: 144.

Step 002: weightedTotalDegree_mul_le owner check passed. Current sorry tokens: 144.

Step 003: weightedTotalDegree_finset_sum_le owner check passed. Current sorry tokens: 143.

Step 004: weightedTotalDegree_finset_prod_le owner check passed. Current sorry tokens: 142.

Step 005: weightedTotalDegree_C owner check passed. Current sorry tokens: 141.

Step 006: weightedTotalDegree_X_le owner check passed. Current sorry tokens: 140.

Step 007: pubDegree_zero owner check passed. Current sorry tokens: 139.

Step 008: privDegree_zero owner check passed. Current sorry tokens: 138.

Step 009: pubDegree_C owner check passed. Current sorry tokens: 137.

Step 010: privDegree_C owner check passed. Current sorry tokens: 136.

Step 011: pubDegree_X_inl owner check passed. Current sorry tokens: 135.

Step 012: pubDegree_X_inr owner check passed. Current sorry tokens: 134.

Step 013: privDegree_X_inl owner check passed. Current sorry tokens: 133.

Step 014: privDegree_X_inr owner check passed. Current sorry tokens: 132.

Step 015: pubDegree_add_le owner check passed. Current sorry tokens: 131.

Step 016: privDegree_add_le owner check passed. Current sorry tokens: 130.

Step 017: pubDegree_mul_le owner check passed. Current sorry tokens: 129.

Step 018: privDegree_mul_le owner check passed. Current sorry tokens: 128.

Step 019: pubDegree_finset_sum_le owner check passed. Current sorry tokens: 127.

Step 020: privDegree_finset_sum_le owner check passed. Current sorry tokens: 126.

Step 021: pubDegree_finset_prod_le owner check passed. Current sorry tokens: 125.

Step 022: privDegree_finset_prod_le owner check passed. Current sorry tokens: 124.

Step 023: pubDegree_rename owner check passed. Current sorry tokens: 123.

Step 024: privDegree_rename owner check passed. Current sorry tokens: 122.

M1 degree cluster committed: 68469690bf021684214da60615a7c1aec282a876. All 26 public theorem axiom sets are standard; statements unchanged. Next: Params then encoding and algebra.

Step 025: D_pos owner check passed. Current sorry tokens: 121.

Step 026: noiseWidth_pos owner check passed. Current sorry tokens: 120.

Step 027: noiseDenAt_pos owner check passed. Current sorry tokens: 119.

Step 028: W_pos owner check passed. Current sorry tokens: 118.

Step 029: B_pos owner check passed. Current sorry tokens: 117.

Step 030: kappaOf_pow owner check passed. Current sorry tokens: 116.

Step 031: kappaOf_le owner check passed. Current sorry tokens: 115.

Step 032: kappaOfN_n owner check passed. Current sorry tokens: 114.

Step 033: kappaOfN_le owner check passed. Current sorry tokens: 113.

Step 034: lpnModulus_le_pow owner check passed. Current sorry tokens: 112.

Step 035: lpnSamples_le owner check passed. Current sorry tokens: 111.

Step 036: le_n owner check passed. Current sorry tokens: 110.

Step 037: Γ_le_B owner check passed. Current sorry tokens: 109.

Step 038: le_log_n owner check passed. Current sorry tokens: 108.

Step 039: encodeList_injective_of_fixedWidth owner check passed. Current sorry tokens: 109.

Step 040: encodeList_length_of_fixedWidth owner check passed. Current sorry tokens: 108.

Step 041: ell_le_ellBound owner check passed. Current sorry tokens: 107.

Step 042: n_le_nBound owner check passed. Current sorry tokens: 106.

Step 043: m_le_mBound owner check passed. Current sorry tokens: 105.

Step 044: W_le_ell_add_one owner check passed. Current sorry tokens: 104.

Step 045: W_le_two_pow_ell_add_one owner check passed. Current sorry tokens: 103.

Step 046: B_le_bucketBound owner check passed. Current sorry tokens: 102.

Step 047: rc_le_rcBound owner check passed. Current sorry tokens: 101.

Step 048: sLen_le_sVarBound owner check passed. Current sorry tokens: 100.

Step 049: pubLen_le_seedBound owner check passed. Current sorry tokens: 99.

Step 050: privLen_le_seedBound owner check passed. Current sorry tokens: 98.

Step 051: encBuckets_injective owner check passed. Current sorry tokens: 97.

Step 052: encIdx'_injective owner check passed. Current sorry tokens: 96.

Step 053: encIdDraw_injective owner check passed. Current sorry tokens: 95.

Step 054: encOneDraw_injective owner check passed. Current sorry tokens: 94.

Step 055: encDraw_injective owner check passed. Current sorry tokens: 93.

Step 056: encSeed'_injective owner check passed. Current sorry tokens: 92.

Step 057: encIdx'_length_le owner check passed. Current sorry tokens: 91.

Step 058: lpnNoise_law owner check passed. Current sorry tokens: 90.

Step 059: encDraw_injective owner check passed. Current sorry tokens: 89.

Step 060: encSample_injective owner check passed. Current sorry tokens: 88.

Step 061: rank_lt_load owner check passed. Current sorry tokens: 87.

Step 062: eq_of_rank_eq owner check passed. Current sorry tokens: 86.

Step 063: indexMap_some_of_not_overfull owner check passed. Current sorry tokens: 85.

Step 064: indexMap_none_of_overfull owner check passed. Current sorry tokens: 84.

Step 065: indexMap_injective_on_bucket owner check passed. Current sorry tokens: 83.

Step 066: bucketMatrix_apply_indexMap owner check passed. Current sorry tokens: 82.

Step 067: bucketMatrix_nonzero_card_le owner check passed. Current sorry tokens: 81.

Step 068: sparseEntries_nodup owner check passed. Current sorry tokens: 80.

Step 069: mem_sparseEntries_iff owner check passed. Current sorry tokens: 79.

Step 070: sparseEntries_length_eq_card owner check passed. Current sorry tokens: 78.

Step 071: sparseFactor_mul owner check passed. Current sorry tokens: 77.

Step 072: sparseFactor_mul_of_card_le owner check passed. Current sorry tokens: 76.

Step 073: monomialSlot_two_halves_card_le owner check passed. Current sorry tokens: 75.

Step 074: halfForm_pubDegree_le owner check passed. Current sorry tokens: 74.

Step 075: halfForm_privDegree_le owner check passed. Current sorry tokens: 73.

Step 076: prgPoly_degrees owner check passed. Current sorry tokens: 72.

Step 077: correctionPoly_degrees owner check passed. Current sorry tokens: 71.

Step 078: G3_degrees owner check passed. Current sorry tokens: 70.

Step 079: G4_degrees owner check passed. Current sorry tokens: 69.

Step 080: halfForm_eval owner check passed. Current sorry tokens: 68.

Step 081: G1_eval owner check passed. Current sorry tokens: 67.

Step 082: G3_eval_of_scaled owner check passed. Current sorry tokens: 66.

Step 083: firstGood_none_iff owner check passed. Current sorry tokens: 65.

Step 084: firstGood_some_flag owner check passed. Current sorry tokens: 64.

Step 085: firstGood_some_minimal owner check passed. Current sorry tokens: 63.

Step 086: packSeed_public_block owner check passed. Current sorry tokens: 62.

Step 087: packSeed_error owner check passed. Current sorry tokens: 61.

Step 088: packSeed_flag owner check passed. Current sorry tokens: 60.

Step 089: packSeed_unscaled owner check passed. Current sorry tokens: 59.

Step 090: packSeed_scaled owner check passed. Current sorry tokens: 58.

Step 091: oneFlag_bounds owner check passed. Current sorry tokens: 57.

Step 092: corr_zero_of_not_bad owner check passed. Current sorry tokens: 56.

Step 093: oneSd_factors_mul owner check passed. Current sorry tokens: 55.

Step 094: G1_eval_of_good owner check passed. Current sorry tokens: 54.

Step 095: correctionPoly_eval_oneSd owner check passed. Current sorry tokens: 53.

Step 096: G2_eval_of_flag owner check passed. Current sorry tokens: 52.

Step 097: G4_eval_sdCore owner check passed. Current sorry tokens: 51.

Step 098: G4_eval_eq owner check passed. Current sorry tokens: 50.

Step 099: eval'_correct owner check passed. Current sorry tokens: 49.

Step 100: Params.G4_seed_allOutputs owner check passed. Current sorry tokens: 49.

Step 101: jls_hasComplexity owner check passed. Current sorry tokens: 48.

Step 102: HasComplexityEff.hasComplexity owner check passed. Current sorry tokens: 47.

Step 103: primeWidthBound owner check passed. Current sorry tokens: 46.

M1 complete and published. Source 19dde91afc384656e7e47cb018057e088d4ded0a; exchange 10da7fdefd9a44023cc117a672f19e8a3617b81d. All103 steps passed, 100 original holes filled plus3 new helper theorems. Current remaining original direct sorry tokens46. Next M2 includes seedBitsAt_le, jls_seedBits_eq, jls_seedBits_le and jls_hasPolyStretch. Full final kernel census/seals remain required.

Step 104: seedBitsAt_le owner check passed. Current sorry tokens: 45.

Step 105: jls_seedBits_eq owner check passed. Current sorry tokens: 44.

Step 106: jls_seedBits_le owner check passed. Current sorry tokens: 43.

Step 107: w_lower owner check passed. Current sorry tokens: 43.

Step 108: stretch_gaps owner check passed. Current sorry tokens: 43.

Step 109: eventually_seed_relative_gap owner check passed. Current sorry tokens: 43.

Step 110: jls_hasPolyStretch owner check passed. Current sorry tokens: 42.

Step 111: binomial_bound owner check passed. Current sorry tokens: 41.

Step 112: bucket_tail owner check passed. Current sorry tokens: 40.

Step 113: some_bucket_tail owner check passed. Current sorry tokens: 39.

Step 114: full_bucket_tail owner check passed. Current sorry tokens: 38.

Step 115: some_full_bucket_tail owner check passed. Current sorry tokens: 37.

Step 116: errProb_nonneg owner check passed. Current sorry tokens: 36.

Step 117: badSet_expect_le owner check passed. Current sorry tokens: 35.

Step 118: cond1_prob_le owner check passed. Current sorry tokens: 34.

Step 119: errProb_le_decomposition owner check passed. Current sorry tokens: 33.

Step 120: bucket_count_upper owner check passed. Current sorry tokens: 33.

Step 121: bucket_count_lower owner check passed. Current sorry tokens: 33.

Step 122: prefactor_eventually_le_two_pow owner check passed. Current sorry tokens: 33.

Step 123: binomial_ratio_quarter owner check passed. Current sorry tokens: 33.

Step 124: smallset_bucket_tail_quarter owner check passed. Current sorry tokens: 33.

Step 125: capacity_bucket_tail_quarter owner check passed. Current sorry tokens: 33.

Step 126: cond1_single_le_quarter owner check passed. Current sorry tokens: 33.

Step 127: cond1_repetitions_fixed_index owner check passed. Current sorry tokens: 33.

Step 128: cond1_all_fixed_index owner check passed. Current sorry tokens: 33.

Step 129: cond1_all_joint owner check passed. Current sorry tokens: 33.

Step 130: jointLaw_prob_eq_uprob owner check passed. Current sorry tokens: 33.

Step 131: cond3_joint_le_quarter_pow owner check passed. Current sorry tokens: 33.

Step 132: cond2_sparse_joint_le_quarter_pow owner check passed. Current sorry tokens: 33.

Step 133: claim42 owner check passed. Current sorry tokens: 32.

Step 134: Internal.lpnNoise_law_cast owner check passed. Current sorry tokens: 32.
