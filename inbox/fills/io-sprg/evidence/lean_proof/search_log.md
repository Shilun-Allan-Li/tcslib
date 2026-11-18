# Overlap searches

Weighted addition: isolated Mathlib-only exact? did not close; apply? produced
only partial suggestions and its diagnostic sorry, which is not a proof. The
source proof applies existing AddMonoidAlgebra.sup_support_add_le to Finsupp.weight.
Raw logs and probe hashes are in evidence/overlap/runs and archive. New
StructuredSeed modules are excluded from these search imports, preventing self hits.

degree_add: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: AddMonoidAlgebra.sup_support_add_le.

degree_mul: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: AddMonoidAlgebra.sup_support_mul_le.

degree_sum: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: AddMonoidAlgebra.supDegree_sum_le.

degree_prod: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: AddMonoidAlgebra.supDegree_prod_le.

degree_C: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: MvPolynomial.isWeightedHomogeneous_C.

degree_X: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: MvPolynomial.isWeightedHomogeneous_X.

pubDegree_zero: exact=CLOSED, apply=CLOSED. Reuse: MvPolynomial.weightedTotalDegree_zero.

privDegree_zero: exact=CLOSED, apply=CLOSED. Reuse: MvPolynomial.weightedTotalDegree_zero.

pubDegree_C: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_C.

privDegree_C: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_C.

pubDegree_X_inl: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_X_le.

pubDegree_X_inr: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_X_le.

privDegree_X_inl: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_X_le.

privDegree_X_inr: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_X_le.

pubDegree_add_le: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_add_le.

privDegree_add_le: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_add_le.

pubDegree_mul_le: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_mul_le.

privDegree_mul_le: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_mul_le.

pubDegree_finset_sum_le: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_finset_sum_le.

privDegree_finset_sum_le: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_finset_sum_le.

pubDegree_finset_prod_le: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_finset_prod_le.

privDegree_finset_prod_le: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.weightedTotalDegree_finset_prod_le.

pubDegree_rename: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: MvPolynomial.weightedTotalDegree_rename_of_injective.

privDegree_rename: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: MvPolynomial.weightedTotalDegree_rename_of_injective.

Params_D_pos: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Nat.div_pos_iff; Nat.succ_le_succ.

Params_noiseWidth_pos: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _).

Params_noiseDenAt_pos: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: pow_pos; noiseWidth_pos reader.

Params_W_pos: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: W_eq_noiseDenAt; noiseDenAt_pos.

Params_B_pos_bounded: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: B_eq; lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _).

Params_kappaOf_pow: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: PadQuad.nu_eq, nu_pow_le, le_nu; Nat.pow_le_pow_iff_left.

Params_kappaOf_le: exact=CLOSED, apply=CLOSED. Reuse: PadQuad.nu_le via nu_eq and kappaOf_eq.

Params_kappaOfN_n: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: PadQuad.nu_eq, nu_pow_le, le_nu; Nat.pow_mul and pow_le_pow_iff_left.

Params_kappaOfN_le: exact=CLOSED, apply=CLOSED. Reuse: PadQuad.nu_le via nu_eq and kappaOfN_eq.

Params_lpnModulus_le_pow: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: PrimeParam.le_two_pow, kappaOf_le; Nat.pow_le_pow_right.

Params_lpnSamples_le: exact=CLOSED, apply=CLOSED. Reuse: PolyExpr.eval_pow, PolyExpr.eval_var.

Params_le_n: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Nat.le_pow for the positive E and D exponents.

Params_Gamma_le_B: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Real.isLittleO_logb_id_atTop; Asymptotics little-o closures; Real.natLog_le_logb; Nat.div_le_div_right.

Params_le_log_n: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Nat.le_log_of_pow_le; Params.le_n at the explicit cutoff 2^c.

Basic_encodeList_injective_of_fixedWidth: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: BoolCircuit.encodeList_nil/cons; List.append_inj; private prefix-free overlap disclosed.

Basic_encodeList_length_of_fixedWidth: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: BoolCircuit.encodeList_nil/cons; List.length_cons/append; Nat.succ_mul; private variable-block bound overlap disclosed.

Encoding_ell_le_ellBound: exact=CLOSED, apply=CLOSED. Reuse: Params.ℓ_eq; ellBound_eq; PolyExpr.eval_pow/eval_var.

Encoding_n_le_nBound: exact=CLOSED, apply=CLOSED. Reuse: Params.n_eq; nBound_eq; Nat.pow_le_pow_left and ell_le_ellBound.

Encoding_m_le_mBound: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: BoolPRG.outLen_le; PolyExpr.eval_subst/eval_mono.

Encoding_W_le_ell_add_one: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: Nat.floor_le; Real.one_le_rpow; Real.rpow_le_rpow_of_exponent_le; Real.rpow_mul_natCast.

Encoding_W_le_two_pow_ell_add_one: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: W_le_ell_add_one; Nat.lt_two_pow_self.

Encoding_B_le_bucketBound: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Nat.div_lt_iff_lt_mul; Nat.le_mul_of_pos_right; rounded quotient and m_le_mBound.

Encoding_rc_le_rcBound: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Nat.le_pow; W_le_ell_add_one; Nat.mul_le_mul_left.

Encoding_sLen_le_sVarBound: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Nat.pow_le_pow_left/add_le_add/mul_le_mul; previous component bounds.

Encoding_pubLen_le_seedBound: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: pubLen_eq/seedBound_eq/pubBound_eq; Nat.add_le_add_right.

Encoding_privLen_le_seedBound: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: sLen_le_sVarBound; Nat.add_le_add and Nat.mul_le_mul_left.

Encoding_encBuckets_injective: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Internal.encodeList_injective_of_fixedWidth; Candidates.natToList_injOn; List.ofFn_injective.

Encoding_encIdx'_injective: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: pairEncode_injective; BoolPRG.encIdx_injective; encBuckets_injective; Encoding.Modular.encodeMatrix_injective.

Encoding_encIdDraw_injective: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: pairEncode_injective; BoolPRG.encIdDraw_injective; encBuckets_injective; modular matrix injectivity.

Encoding_encOneDraw_injective: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: pairEncode_injective; modular vector injection; natToList_injOn; Basic fixed-width list injection.

Encoding_encDraw_injective: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: encOneDraw_injective; Basic fixed-width exact length and injection; pairEncode_injective; List.ofFn_injective.

Encoding_encSeed'_injective: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: pairEncode_injective; Encoding.Modular.encodeVector_injective at pp.le_two_pow.

Encoding_encIdx'_length_le: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: Basic exact list length; length_pairEncode; encodeMatrix_length; BoolPRG.encIdx_length_le; PolyExpr.eval_mono.

LPN_lpnNoise_law: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: OneWay.uprob_eq_one_div_card/uprob_congr; HardcoreBit.uprob_prod_and; uprob_not; ZMod cast readers.

LPN_raw_encDraw_injective: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: pairEncode_eq_dbl/pairEncode_injective; LogProg.bits_injective; modular matrix/vector and numeral injectivity; closed-pair variable-width list recovery disclosed.

LPN_raw_encSample_injective: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: pairEncode_injective; Encoding.Modular.encodeMatrix_injective and encodeVector_injective.

BucketsSparse_rank_lt_load: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Finset.card_lt_card; Finset.ssubset_iff_of_subset; filter membership.

BucketsSparse_eq_of_rank_eq: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Finset.card_lt_card and strict subset; lt_trichotomy in the specific filtered rank.

BucketsSparse_indexMap_some_of_not_overfull: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: rank_lt_load; overfull_iff; finProdFinEquiv and dif_pos.

BucketsSparse_indexMap_none_of_overfull: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: overfull_iff; indexMap_eq; dif_neg.

BucketsSparse_indexMap_injective_on_bucket: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: eq_of_rank_eq; indexMap_eq; finProdFinEquiv.symm.injective; Option.some.inj.

BucketsSparse_bucketMatrix_apply_indexMap: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: Finset.sum_eq_single; indexMap_injective_on_bucket; bucketMatrix_eq.

BucketsSparse_bucketMatrix_nonzero_card_le: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: Finset.exists_ne_zero_of_sum_ne_zero; Finset.card_image_of_injective/card_le_card/card_image_le; bucketMatrix_eq.

BucketsSparse_sparseEntries_nodup: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: List.nodup_finRange; List.Nodup.product/filter.

BucketsSparse_mem_sparseEntries_iff: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: List.mem_filter/product/finRange; decide_eq_true_eq.

BucketsSparse_sparseEntries_length_eq_card: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: List.toFinset_card_of_nodup; Finset.ext; mem_sparseEntries_iff.

BucketsSparse_sparseFactor_mul: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: Matrix.mul_apply; Finset.sum_eq_zero/sum_eq_single; List.mem_iff_getElem/getElem?_eq_some_iff/getElem?_inj; sparse support readers.

BucketsSparse_sparseFactor_mul_of_card_le: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: sparseFactor_mul and sparseEntries_length_eq_card.

Algebra_Internal.monomialSlot_two_halves_card_le: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Finset.card_union_of_disjoint/card_image_of_injective/card_le_card; Finset.length_sort; isSome_getElem?.

Algebra_halfForm_pubDegree_le: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: pubDegree_C/zero/X and finite sum/product/mul degree bounds; Finset.sum_boole.

Algebra_halfForm_privDegree_le: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: privDegree_C/zero/X; privDegree_finset_prod_le/sum_le/mul_le; Finset.sum_const_zero.

Algebra_prgPoly_degrees: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: Finset.card_nsmul_le_sum; Finsupp.mem_support_iff; MvPolynomial.le_totalDegree; half-form degree bounds and monomialSlot_two_halves_card_le.

Algebra_correctionPoly_degrees: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: pubDegree_X_inr/privDegree_X_inr; zero and finite-sum/multiplication degree bounds.

Algebra_G3_degrees: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: prgPoly_degrees; correctionPoly_degrees; public/private addition max bounds.

Algebra_G4_degrees: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: pubDegree_rename/privDegree_rename; G3_degrees; finite-sum degree bounds.

Algebra_halfForm_eval: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: Fintype.prod_sum; Fin.sum_univ_castSucc; MvPolynomial.eval_sum/prod/mul/X; Finset.prod_mul_distrib.

Algebra_G1_eval: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: MvPolynomial.mem_restrictDegree/le_totalDegree/eval₂_eq; Fin.prod_univ_add/prod_univ_eq_prod_range/prod_univ_fun_getElem; Finset.prod_subset; List.prod_toFinset; halfForm_eval.

Algebra_G3_eval_of_scaled: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: MvPolynomial evaluation readers; Finset.mul_sum/sum_congr; half-form first-copy scaling; ring normalization.

Algebra_firstGood_none_iff: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: List.find?_eq_none; List.mem_finRange; Bool.eq_false_iff.

Algebra_firstGood_some_flag: exact=DIAGNOSTIC_FAILURE, apply=DIAGNOSTIC_FAILURE. Reuse: List.find?_some via firstGood_eq.

AlgebraV2_firstGood_some_flag: exact=CLOSED, apply=CLOSED. Reuse: List.find?_some h (exact existing public theorem).

AlgebraV2_firstGood_none_iff: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: List.find?_eq_none; List.mem_finRange; Bool.eq_false_iff.

Algebra_firstGood_some_minimal: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: List.ofFn_id; List.find?_ofFn_eq_some_of_injective; Bool.eq_false_iff.

Algebra_packSeed_public_block: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: packSeed_fst; Equiv.symm_apply_apply.

Algebra_packSeed_error: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: packSeed_fst; Equiv.symm_apply_apply.

Algebra_packSeed_flag: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: packSeed_snd; Equiv.symm_apply_apply.

Algebra_packSeed_unscaled: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: packSeed_snd; Equiv.symm_apply_apply.

Algebra_packSeed_scaled: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: packSeed_snd; Equiv.symm_apply_apply.

Algebra_oneFlag_bounds: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: oneFlag_eq; of_decide_eq_true; cap_eq/pow_two; Buckets.overfull_iff.

Algebra_corr_zero_of_not_bad: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: MvPolynomial.eval₂Hom_congr'/eval₂_comp; BoolPRG.MultilinearRep.eval_poly; badSet/errSet/corr readers.

Algebra_oneSd_factors_mul: exact=INVALID_ELABORATION, apply=INVALID_ELABORATION. Reuse: Invalid HMul search template, superseded by AlgebraMatrixV2_oneSd_factors_mul; actual proof reuses sparseFactor_mul_of_card_le.

AlgebraMatrixV2_oneSd_factors_mul: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Structural core isolated; actual theorem applies proved sparseFactor_mul_of_card_le and Buckets.bucketMatrix_nonzero_card_le plus oneFlag_bounds.

BucketsSparseV2_sparseFactor_mul: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Corrected Matrix.of elaboration; Matrix.mul_apply; finite sums; sparse list uniqueness/membership.

BucketsSparseV2_sparseFactor_mul_of_card_le: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: Corrected Matrix.of elaboration; sparse list length/cardinality and reconstruction core.

Algebra_G1_eval_of_good: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: G1_eval; corr_zero_of_not_bad; oneSd_pub/priv; sub_eq_zero.

Algebra_correctionPoly_eval_oneSd: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: oneFlag_bounds; Buckets.indexMap_some_of_not_overfull/bucketMatrix_apply_indexMap; oneSd_factors_mul; Matrix.mul_apply/of_apply; polynomial eval readers.

Algebra_G2_eval_of_flag: exact=NO_CLOSING_PROOF, apply=DIAGNOSTIC_FAILURE. Reuse: G1_eval; correctionPoly_eval_oneSd; oneSd_pub/priv; G2_eq/corr_eq; ring cancellation.

Algebra_G4_eval_sdCore: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: packing projection lemmas; G3_eval_of_scaled; firstGood_some_flag; G2_eval_of_flag; eval_rename/eval_sum; finite indicator-sum simplification.

Algebra_G4_eval_eq: exact=INVALID_ELABORATION, apply=INVALID_ELABORATION. Reuse: sdSampFull_eq; OracleComp.map_eq_bind; AllOutputs.bind/allOutputs_true/allOutputs_pure; sdCore_σ; G4_eval_sdCore.

AlgebraSupportV2_G4_eval_eq: exact=DIAGNOSTIC_FAILURE, apply=DIAGNOSTIC_FAILURE. Reuse: Corrected Type0 core composition; OracleComp.map_eq_bind and AllOutputs.bind/allOutputs_pure; G4_eval_sdCore.

AlgebraSupportV2_eval'_correct: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: G4_eval_eq; AllOutputs.mono; eval'_eq; prime-field zero/one distinction and Boolean cases.

AlgebraSupportV2_Params.G4_seed_allOutputs: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: G4_eval_eq and eval_correct; published AllOutputs pure/query/bind readers; specialized joint-support theorem shared by both complexity links.

AlgebraSupportV2_jls_hasComplexity: exact=CLOSED, apply=CLOSED. Reuse: SPRG.Raw.hasComplexity_iff; jlsSPRG_raw_eq/sdSamp; G4_degrees; specific G4_seed_allOutputs witness.

Bridges_HasComplexityEff.hasComplexity: exact=NO_CLOSING_PROOF, apply=PARTIAL_NOT_PROOF. Reuse: hasComplexityEff_iff and hasComplexity_iff; retain polynomial/degrees/support witnesses.

Bridges_primeWidthBound: exact=CLOSED, apply=CLOSED. Reuse: PolyExpr.eval_add/eval_var/eval_const; PrimeParam.le_two_pow.
