/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- Pass–shelat Chapters 2–4 verification: axiom prints for every headline theorem.
-- Append `#print axioms <decl>` lines (with the import of the facade) as workstreams land.
-- Compile with: lake env lean audits/pass-shelat/Checks.lean
import TCSlib.Complexity.Randomized
import TCSlib.Cryptography.Asymptotic
import TCSlib.Cryptography.NumberTheory
import TCSlib.Cryptography.Candidates
import TCSlib.Cryptography.ZeroKnowledge

/-!
# Pass–shelat Chapters 2–4 verification (run 2, statement phase)

Axiom prints for the sanity theorems and for every headline theorem of the campaign
(every theorem whose name corresponds to a numbered result of [PS10]). In the statement
phase most headlines are sorried under their proof sketches and print `sorryAx`; proved
results must print exactly `[propext, Classical.choice, Quot.sound]`.
-/

-- ## Sanity theorems (plan §6, workstream A)
#print axioms Complexity.NUPPT.nonempty
#print axioms Complexity.PPT.nonempty
#print axioms TCSlib.Cryptography.not_strongOneWay_id
#print axioms TCSlib.Cryptography.FunFamily.StrongOneWay.weak
#print axioms TCSlib.Cryptography.Ensemble.Indist.refl
#print axioms TCSlib.Cryptography.OracleEnsemble.Indist.refl
#print axioms TCSlib.Cryptography.npProtocol_interactiveProof
#print axioms TCSlib.Cryptography.hybrid_lemma

-- ## Machine layer (M1–M3; D11 admission `polyTimeComputable_iterateFind`)
#print axioms Complexity.polyTimeComputable_unaryPoly
#print axioms Complexity.NUPPT.decides_of_decidesWithAdviceInTime
#print axioms Turing.FinTM.computesFunInTime_pairSplitAt
#print axioms Turing.FinTM.computesFunInTime_unaryMul
#print axioms Complexity.polyTimeComputable_pairTakePoly
#print axioms Complexity.polyTimeComputable_pairDropPoly
#print axioms Complexity.NUPPT.exists_comp
#print axioms Complexity.NUPPT.exists_reparam
#print axioms Complexity.NUPPT.exists_reparam_advice
#print axioms Complexity.NUPPT.exists_withAdvice
#print axioms Complexity.NUPPT.exists_split
#print axioms Complexity.NUPPT.exists_seq
#print axioms Complexity.polyTimeComputable_iterateFind
#print axioms Complexity.polyTimeComputable_iterate
#print axioms Complexity.polyTimeComputable_iterateEmit
#print axioms Complexity.polyTimeComputable_majority
#print axioms Complexity.polyTimeComputable_pairXor
#print axioms Complexity.polyTimeComputable_pairEq
#print axioms Complexity.polyTimeComputable_blockMap

-- ## Sampling device (S, D10)
#print axioms TCSlib.Cryptography.distAdv_le_of_statClose
#print axioms TCSlib.Cryptography.StatClose.prod
#print axioms TCSlib.Cryptography.StatClose.map
#print axioms TCSlib.Cryptography.rejectionSample_uniform_of_some
#print axioms TCSlib.Cryptography.uprob_rejectionSample_none
#print axioms TCSlib.Cryptography.statClose_rejectionSample
#print axioms TCSlib.Cryptography.permFromCoins_uniform_of_some
#print axioms TCSlib.Cryptography.uprob_permFromCoins_none_le

-- ## Chapter 2: one-way functions (C2a: Thm 35.1, Thm 35.2, Claim 38.2)
#print axioms TCSlib.Cryptography.FunFamily.Easy.prod
#print axioms TCSlib.Cryptography.OneWay.invProb_prodFun_le_yaoTry
#print axioms TCSlib.Cryptography.claim_38_2
#print axioms TCSlib.Cryptography.weak_to_strong
#print axioms TCSlib.Cryptography.strong_prod_two

-- ## Chapter 2: collections (C2b: Thm 42.2)
#print axioms TCSlib.Cryptography.FunFamily.StrongOneWay.toCollection_oneWay
#print axioms TCSlib.Cryptography.FunFamily.StrongOneWay.exists_collection_oneWay
#print axioms TCSlib.Cryptography.Collection.OneWay.owfFamily_strongOneWay
#print axioms TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay

-- ## Chapter 2: universal one-way function (C2c: Thm 63.1, Lem 64.3, Claims 65.1, 65.2)
#print axioms TCSlib.Cryptography.fUniversal_easy
#print axioms TCSlib.Cryptography.lemma_64_3
#print axioms TCSlib.Cryptography.claim_65_1
#print axioms TCSlib.Cryptography.claim_65_2
#print axioms TCSlib.Cryptography.claim_65_2_cond
#print axioms TCSlib.Cryptography.fUniversal_hard
#print axioms TCSlib.Cryptography.fUniversal_weakOneWay
#print axioms TCSlib.Cryptography.theorem_63_1

-- ## Chapter 2: number theory (NT)
#print axioms TCSlib.Cryptography.NumberTheory.two_pow_le_pow_primeCounting
#print axioms TCSlib.Cryptography.NumberTheory.chebyshev_two_mul
#print axioms TCSlib.Cryptography.NumberTheory.chebyshev
#print axioms TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime_pair
#print axioms TCSlib.Cryptography.NumberTheory.extEuclid_spec
#print axioms TCSlib.Cryptography.NumberTheory.extEuclid_inv
#print axioms TCSlib.Cryptography.NumberTheory.extEuclidCalls_le
#print axioms TCSlib.Cryptography.NumberTheory.modExpMults_le
#print axioms TCSlib.Cryptography.NumberTheory.totient_prime_mul_prime
#print axioms TCSlib.Cryptography.NumberTheory.card_units_zmod_prime_mul_prime
#print axioms TCSlib.Cryptography.NumberTheory.units_pow_mod_totient
#print axioms TCSlib.Cryptography.NumberTheory.pow_mod_totient_modEq
#print axioms TCSlib.Cryptography.NumberTheory.rsa_pow_pow
#print axioms TCSlib.Cryptography.NumberTheory.rsa_pow_bijective
#print axioms TCSlib.Cryptography.NumberTheory.exists_rsa_inverse
#print axioms TCSlib.Cryptography.NumberTheory.le_totient_mul_log_succ
#print axioms TCSlib.Cryptography.NumberTheory.mrLiar_iff_of_prime
#print axioms TCSlib.Cryptography.NumberTheory.card_mrLiars_of_prime
#print axioms TCSlib.Cryptography.NumberTheory.two_mul_card_mrLiars_le
#print axioms TCSlib.Cryptography.NumberTheory.millerRabin_of_prime
#print axioms TCSlib.Cryptography.NumberTheory.uprob_millerRabin_le
#print axioms TCSlib.Cryptography.NumberTheory.samplePrime_uniform_of_some
#print axioms TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le
#print axioms TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_exp
#print axioms TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_two_pow
#print axioms TCSlib.Cryptography.NumberTheory.statClose_samplePrime
#print axioms TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt
#print axioms TCSlib.Cryptography.NumberTheory.card_QR_prime
#print axioms TCSlib.Cryptography.NumberTheory.card_sqrt_eq_two
#print axioms TCSlib.Cryptography.NumberTheory.sqrtMod3_sq
#print axioms TCSlib.Cryptography.NumberTheory.pow_div_four_succ_mem_QR
#print axioms TCSlib.Cryptography.NumberTheory.mem_QR_mul_iff
#print axioms TCSlib.Cryptography.NumberTheory.card_sqrt_mul_eq_four
#print axioms TCSlib.Cryptography.NumberTheory.card_QR_mul
#print axioms TCSlib.Cryptography.NumberTheory.pushesUniform_sqTo
#print axioms TCSlib.Cryptography.NumberTheory.gcd_sub_eq_prime_of_sq_eq_sq
#print axioms TCSlib.Cryptography.NumberTheory.blumSqrt_sq
#print axioms TCSlib.Cryptography.NumberTheory.sqTo_bijective_of_blum

-- ## Chapter 2: candidates — factoring (Cand1: Thms 33.5, 36.3, 51.1, Claim 34.1)
#print axioms TCSlib.Cryptography.Candidates.invProb_prodFun_le_plant
#print axioms TCSlib.Cryptography.Candidates.one_div_le_uprob_prime_pair_bits
#print axioms TCSlib.Cryptography.Candidates.fmultNat_eq_mul_prime
#print axioms TCSlib.Cryptography.Candidates.fmult_inv_factor
#print axioms TCSlib.Cryptography.Candidates.fmult_easy
#print axioms TCSlib.Cryptography.Candidates.fmult_weakOneWay
#print axioms TCSlib.Cryptography.Candidates.fmult_prod_strongOneWay
#print axioms TCSlib.Cryptography.Candidates.factoringCollection_sampleClose
#print axioms TCSlib.Cryptography.Candidates.factoringCollection_invProbAt_le
#print axioms TCSlib.Cryptography.Candidates.factoringCollection_oneWay

-- ## Chapter 2: candidates — RSA and Rabin (Cand2: Thms 53.2, 55.2, 57.2, 61.7, 61.8, 63.10)
#print axioms TCSlib.Cryptography.Candidates.rsaPerm_symm_apply
#print axioms TCSlib.Cryptography.Candidates.pushesUniform_rsaPerm
#print axioms TCSlib.Cryptography.Candidates.rsaInv_spec
#print axioms TCSlib.Cryptography.Candidates.rsaCollection_sampleClose
#print axioms TCSlib.Cryptography.Candidates.rsaCollection_invProbAt_le
#print axioms TCSlib.Cryptography.Candidates.rsaCollection_oneWay
#print axioms TCSlib.Cryptography.Candidates.rsaTrapdoor_oneWay
#print axioms TCSlib.Cryptography.Candidates.factorProb_le_rsaProb
#print axioms TCSlib.Cryptography.Candidates.rsa_imp_factoring
#print axioms TCSlib.Cryptography.Candidates.rabin_symmetry
#print axioms TCSlib.Cryptography.Candidates.rabinCollection_sampleClose
#print axioms TCSlib.Cryptography.Candidates.rabinCollection_invProbAt_le
#print axioms TCSlib.Cryptography.Candidates.blumInv_spec
#print axioms TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_sampleClose
#print axioms TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_invProbAt_le
#print axioms TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay
#print axioms TCSlib.Cryptography.Candidates.blumFactorProb_le_invProbAt
#print axioms TCSlib.Cryptography.Candidates.blumFactoring_of_rabinBlum_oneWay

-- ## Chapter 2–3: candidates — discrete log, its hard-core bit, El Gamal
-- (Cand3: Thm 52.3, Lem 84.1, Thm 107.3)
#print axioms TCSlib.Cryptography.Candidates.expF_injective
#print axioms TCSlib.Cryptography.Candidates.expCollection_sampleClose
#print axioms TCSlib.Cryptography.Candidates.expCollection_invProbAt_le
#print axioms TCSlib.Cryptography.Candidates.expCollection_oneWay
#print axioms TCSlib.Cryptography.Candidates.dlCollection_oneWay
#print axioms TCSlib.Cryptography.Candidates.uprob_majOracle_ne_le
#print axioms TCSlib.Cryptography.Candidates.invProb_dlInverter_ge
#print axioms TCSlib.Cryptography.Candidates.fullDLCollection_oneWay
#print axioms TCSlib.Cryptography.Candidates.fullDLCollection_hardCore
#print axioms TCSlib.Cryptography.Candidates.statClose_sq_generator
#print axioms TCSlib.Cryptography.Candidates.GroupPKScheme.Secure.const
#print axioms TCSlib.Cryptography.Candidates.elGamal_correct
#print axioms TCSlib.Cryptography.Candidates.elGamal_secure

-- ## Chapter 3: ensembles and indistinguishability (C3a: Lems 71.5, 71.6, 73.8)
#print axioms TCSlib.Cryptography.not_negligible_iff_exists_polyExpr
#print axioms TCSlib.Cryptography.Ensemble.Indist.toLit
#print axioms TCSlib.Cryptography.Ensemble.IndistLit.toIndist
#print axioms TCSlib.Cryptography.Ensemble.Indist.symm
#print axioms TCSlib.Cryptography.Ensemble.Indist.trans
#print axioms TCSlib.Cryptography.Ensemble.Indist.push
#print axioms TCSlib.Cryptography.Ensemble.Indist.copies
#print axioms TCSlib.Cryptography.predict_eq
#print axioms TCSlib.Cryptography.prediction_lemma

-- ## Chapter 3: pseudorandomness and the next-bit test (C3b: Thm 75.4)
#print axioms TCSlib.Cryptography.Ensemble.uniform_pseudorandom
#print axioms TCSlib.Cryptography.PRG.stretch_pos
#print axioms TCSlib.Cryptography.acceptProb_nextBitHybrid_mix
#print axioms TCSlib.Cryptography.nextBitProb_nextBitPred_false
#print axioms TCSlib.Cryptography.exists_nextBitPred
#print axioms TCSlib.Cryptography.Ensemble.NextBitUnpredictable.pseudorandom
#print axioms TCSlib.Cryptography.Ensemble.Pseudorandom.nextBitUnpredictable

-- ## Chapter 3: hard-core predicates (C3c: Thm 79.4, Lem 80.5, Cor 81.7, Thm 87.3)
#print axioms TCSlib.Cryptography.exists_owpPredictorSnoc
#print axioms TCSlib.Cryptography.owp_hardcore_prg
#print axioms TCSlib.Cryptography.exists_expandRed_ge
#print axioms TCSlib.Cryptography.prg_expand
#print axioms TCSlib.Cryptography.cor_81_7
#print axioms TCSlib.Cryptography.FunFamily.glPad_f_bijective
#print axioms TCSlib.Cryptography.FunFamily.StrongOneWay.glPad
#print axioms TCSlib.Cryptography.FunFamily.StrongOneWay.glPad_hardCore
#print axioms TCSlib.Cryptography.goldreich_levin
#print axioms TCSlib.Cryptography.Collection.OneWay.glPad
#print axioms TCSlib.Cryptography.Collection.OneWay.glPad_hardCore
#print axioms TCSlib.Cryptography.goldreich_levin_coll
#print axioms TCSlib.Cryptography.PermCollection.OneWay.glPad
#print axioms TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad
#print axioms TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_hardCore

-- ## Chapter 3: private-key encryption (C3d: Thms 92.2, 94.2, 112.2)
#print axioms TCSlib.Cryptography.distAdv_padXor_le
#print axioms TCSlib.Cryptography.prgScheme_singleMessageSecure
#print axioms TCSlib.Cryptography.PrivateKeyScheme.not_multiMessageSecure_of_deterministic
#print axioms TCSlib.Cryptography.PrivateKeyScheme.ZeroKnowledge.singleMessageSecure
#print axioms TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure.zeroKnowledge
#print axioms TCSlib.Cryptography.PrivateKeyScheme.singleMessageSecure_iff_zeroKnowledge

-- ## Chapter 3: pseudorandom functions and multi-message encryption (C3e: Thms 97.3, 99.2)
#print axioms Complexity.NUPPT.toOracleAdversary_boundedBy
#print axioms TCSlib.Cryptography.oracle_hybrid_lemma
#print axioms TCSlib.Cryptography.two_mul_add_one_expands
#print axioms TCSlib.Cryptography.PRG.Secure.doubling
#print axioms TCSlib.Cryptography.thm_97_3_1
#print axioms TCSlib.Cryptography.thm_97_3_2
#print axioms TCSlib.Cryptography.exists_ggmBitsDist_nuppt
#print axioms TCSlib.Cryptography.ggmPRF_prf
#print axioms TCSlib.Cryptography.exists_prf_of_exists_prg
#print axioms TCSlib.Cryptography.uprob_not_injective_le
#print axioms TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le
#print axioms TCSlib.Cryptography.acceptProb_otpEnc
#print axioms TCSlib.Cryptography.distAdv_prfEncReal_le
#print axioms TCSlib.Cryptography.prfScheme_multiMessageSecure

-- ## Chapter 3: public-key encryption (C3f: Thm-103.d, Thm-103.f, Thm 104.4)
#print axioms TCSlib.Cryptography.distAdv_multi_le_sum
#print axioms TCSlib.Cryptography.BitPublicKeyScheme.singleBitSecure_iff
#print axioms TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun_poly
#print axioms TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise
#print axioms TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure
#print axioms TCSlib.Cryptography.predProb_pkPredictor_false
#print axioms TCSlib.Cryptography.exists_pkPredictor
#print axioms TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme_singleBitSecure
#print axioms TCSlib.Cryptography.TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure

-- ## Chapter 4: the model (C4a: Defs 116.1, 119.5, 121.1, 121.2, 191.11; Inf-4.2, Inf-4.4)
#print axioms TCSlib.Cryptography.WitnessRelation.mem_NP
#print axioms TCSlib.Cryptography.exists_witnessRelation_of_mem_NP
#print axioms TCSlib.Cryptography.StatZK.zk
#print axioms TCSlib.Cryptography.StatZK.hvzk
#print axioms TCSlib.Cryptography.ZK.hvzk
#print axioms TCSlib.Cryptography.PerfectZK.zk
#print axioms TCSlib.Cryptography.negligible_inv_pow_sqrt_div
#print axioms TCSlib.Cryptography.pushesUniform_coinTable
#print axioms TCSlib.Cryptography.polyTimeComputable_encPermGraph
#print axioms TCSlib.Cryptography.polyTimeComputable_encPermMulInv
#print axioms TCSlib.Cryptography.polyTimeComputable_encPermFromCoins

-- ## Chapter 4: graph non-isomorphism and graph isomorphism
-- (C4b: Props 118.4, 120.7, Thm 122.3, Lem 123.5)
#print axioms TCSlib.Cryptography.Riso_witnessRelation
#print axioms TCSlib.Cryptography.uprob_gi_cheat_le_half
#print axioms TCSlib.Cryptography.uprob_gi_rep_cheat_le
#print axioms TCSlib.Cryptography.uprob_gni_rep_cheat
#print axioms TCSlib.Cryptography.gni_interactiveProofErr
#print axioms TCSlib.Cryptography.gni_interactiveProof
#print axioms TCSlib.Cryptography.gi_efficientProverProofErr
#print axioms TCSlib.Cryptography.gi_rep_efficientProverProof
#print axioms TCSlib.Cryptography.gi_rep_interactiveProof
#print axioms TCSlib.Cryptography.gi_sim_H_dist
#print axioms TCSlib.Cryptography.gi_sim_half
#print axioms TCSlib.Cryptography.statClose_giSimTrunc
#print axioms TCSlib.Cryptography.exists_giSimulator
#print axioms TCSlib.Cryptography.gi_statZK
#print axioms TCSlib.Cryptography.gi_zk
#print axioms TCSlib.Cryptography.gi_hvzk

-- ## Chapter 4: commitments (C4c: Thm 126.4)
#print axioms TCSlib.Cryptography.exists_pairRed_ge
#print axioms TCSlib.Cryptography.owpComStr_binding
#print axioms TCSlib.Cryptography.exists_bitComPredictor
#print axioms TCSlib.Cryptography.HardCore.bitHiding
#print axioms TCSlib.Cryptography.BitHiding.owpComStr_hides
#print axioms TCSlib.Cryptography.owpComStr_polyTimeComputable
#print axioms TCSlib.Cryptography.owp_commitment
#print axioms TCSlib.Cryptography.exists_commitment_of_owp_hardCore

-- ## Chapter 4: graph 3-colouring and NP (C4d: Props 127.6, 128.8, Thm 124.1)
#print axioms TCSlib.Cryptography.one_sub_inv_pow_mul_le_exp
#print axioms TCSlib.Cryptography.colVerify_honest
#print axioms TCSlib.Cryptography.exists_bad_edge
#print axioms TCSlib.Cryptography.uprob_col_cheat_le
#print axioms TCSlib.Cryptography.R3COL_witnessRelation
#print axioms TCSlib.Cryptography.col_efficientProverProofErr
#print axioms TCSlib.Cryptography.colRep_efficientProverProof
#print axioms TCSlib.Cryptography.colRep_interactiveProof
#print axioms TCSlib.Cryptography.statClose_colSimTruncH
#print axioms TCSlib.Cryptography.exists_colSimRed_ge
#print axioms TCSlib.Cryptography.col_zk
#print axioms TCSlib.Cryptography.col_hvzk
#print axioms TCSlib.Cryptography.col_zeroKnowledgeProof
#print axioms TCSlib.Cryptography.zk_proof_of_levinReduction
#print axioms TCSlib.Cryptography.zk_proof_of_owp_levinReduction
#print axioms TCSlib.Cryptography.zk_proof_of_mem_NP
#print axioms TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp

-- ## Run-3 repairs, pack P2 (sampling, ensembles, pseudorandom): audit P2-1 / P2-2
#print axioms TCSlib.Cryptography.statClose_getD_of_uniform_of_some
#print axioms TCSlib.Cryptography.StatClose.comp_pushesUniform
#print axioms TCSlib.Cryptography.one_sub_inv_pow_le_half
#print axioms TCSlib.Cryptography.statClose_permFromCoins
#print axioms TCSlib.Cryptography.uprob_permFromCoins_none_le_two_pow
#print axioms TCSlib.Cryptography.statClose_permFromCoins_two_pow
#print axioms TCSlib.Cryptography.statClose_samplePerm
#print axioms TCSlib.Cryptography.negligible_mul_permFailBound

-- ## Run 3 (statement audit): pack P3 repairs (OneWay, Collections, Universal)
-- P3-1: `Collection.sample_spec` field; Thm 42.2 (⇒) headline proved from the explicit form.
#print axioms TCSlib.Cryptography.Collection.evalSampled
#print axioms TCSlib.Cryptography.Candidates.factoringSampler_spec
#print axioms TCSlib.Cryptography.Candidates.rsaSampler_spec
#print axioms TCSlib.Cryptography.Candidates.rabinSampler_spec
#print axioms TCSlib.Cryptography.Candidates.blumSampler_spec
#print axioms TCSlib.Cryptography.Candidates.expSampler_spec
-- P3-2: Def 26.1 in its `1^n` form (headline) and literal form, with the two bridges.
#print axioms TCSlib.Cryptography.FunFamily.WorstCaseOneWay.toLit
#print axioms TCSlib.Cryptography.FunFamily.WorstCaseOneWayLit.toParam
-- P3-4: `fUniversal_easy`, `fUniversal_hard`, `fUniversal_weakOneWay` and `theorem_63_1` are
-- conditional on `CanonizerExp c` (no instance proved); the open problem:
#print axioms TCSlib.Cryptography.exists_canonizerExp

-- ## Run-3 audit repairs, pack P4 (hardcore-encryption-publickey): P4-1, P4-2
#print axioms TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc
#print axioms TCSlib.Cryptography.HardcoreBit.invProb_guessInverter_enc_pad
#print axioms TCSlib.Cryptography.PermFamily.glHalf_f_even
#print axioms TCSlib.Cryptography.PermFamily.glHalf_f_odd
#print axioms TCSlib.Cryptography.glHalfBit_even
#print axioms TCSlib.Cryptography.glHalfBit_odd
#print axioms TCSlib.Cryptography.predProb_glHalf_even
#print axioms TCSlib.Cryptography.predProb_glHalf_odd
#print axioms TCSlib.Cryptography.invProb_glHalf_even
#print axioms TCSlib.Cryptography.invProb_glHalf_odd_le
#print axioms TCSlib.Cryptography.Negligible.comp_div_two
#print axioms TCSlib.Cryptography.OneWayPermutation.glHalf
#print axioms TCSlib.Cryptography.exists_owp_hardCore
#print axioms TCSlib.Cryptography.exists_securePRG_of_owp

-- Run-3 audit P7 (candidates-factoring-rsa-rabin) repairs: the shared block rejection sampler
-- (P7-6; `statClose_rejectBlocksL` is a statement-phase stub), the new bundle functions (P7-1),
-- the one-call reduction at parameter `n` (P7-2) and the repaired error term (P7-3).
#print axioms TCSlib.Cryptography.Candidates.rejectBlocksL_spec
#print axioms TCSlib.Cryptography.Candidates.statClose_rejectBlocksL
#print axioms TCSlib.Cryptography.Candidates.listToNat_addStr
#print axioms TCSlib.Cryptography.Candidates.listToNat_subStr
#print axioms TCSlib.Cryptography.Candidates.oneCallFactorer_runAtL
#print axioms TCSlib.Cryptography.Candidates.negligible_rabinErr

-- Run-3 audit P9 repairs (pack P9, zk-model)
#print axioms TCSlib.Cryptography.WitnessRelation.mem_IP
#print axioms TCSlib.Cryptography.NP_subset_IP
#print axioms TCSlib.Cryptography.Protocol.outV_eq_getLast_of_moverIsV
#print axioms TCSlib.Cryptography.Strategy.ReadsPrefix.mono
#print axioms TCSlib.Cryptography.uprob_adaptive_guess

-- Run-3 audit P11 repairs (pack P11, zk-commitment-3col-np): P11-1 adds `hLR : ∀ x ∈ L, ∃ y, R x y`
-- to the Claim-124.d transfer lemmas and both forms of Theorem 124.1 (printed above); P11-2 keeps
-- the explicit soundness error `1 - 1/p(N) + (1/2)^{p(N)}` in `zk_proof_of_mem_NP(_of_owp)`, shown
-- below `1` by the proved sanity lemma.
#print axioms TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one

-- ## Run-3 re-check (integration): prints for the pack P8 / P9 repairs not yet listed above
-- P8-1 / P8-2 (candidates-dl-elgamal): the DDH exponent sampler's closeness (proved from the
-- shared stub `statClose_sampleBelowL`), the two `FullLength → FullLengthExcept` bridges (proved).
#print axioms TCSlib.Cryptography.Candidates.ddhExpo_statClose
#print axioms TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.fullLengthExcept
#print axioms TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.exists_fullLengthExcept
#print axioms TCSlib.Cryptography.Candidates.statClose_sampleBelowL
-- P9-1 (zk-model): the prefix-reading verifier of the sanity protocol (proved).
#print axioms TCSlib.Cryptography.npProtocol_readsPrefix
