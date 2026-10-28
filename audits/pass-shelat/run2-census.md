# Pass–shelat Chapters 2–4 — run 2 (statement phase) census

Integrator (workstream A), 2026-10-28, worktree `/Users/dehmelf/Research/tcslib-pass-shelat`
(branch `cryptography/pass-shelat-ch2-4`).

* Full build: `lake build` from the worktree root (see "Build" below).
* `sorry` counts: the number of `declaration uses 'sorry'` warnings per file in the full-build log
  (Lake replays the cached log of every module, so the count is complete even for modules that
  were already up to date).
* Lint: `python3 scripts/style_lint.py <file>`; "clean" = the script prints nothing.
* Axiom prints: `audits/pass-shelat/Checks.lean`, output in `audits/pass-shelat/run2-axioms.log`.

## Build

* `lake build` (full library, run by the integrator after the facade registration): exit 0,
  `Build completed successfully (4120 jobs)`, **0 `error:` lines**; 221 `declaration uses 'sorry'`
  warnings in the whole library, of which **157 in the 52 campaign files** (the remaining 64 are
  pre-existing, in `ErrorCorrectingCodes/MRRW.lean` and `BooleanAnalysis/*`).
* `lake env lean audits/pass-shelat/Checks.lean`: exit 0, 0 errors, 243 axiom prints
  (`audits/pass-shelat/run2-axioms.log`).

### Integration edits (workstream A)

1. `TCSlib/Cryptography/Asymptotic.lean` — imports every child (`OneWay`, `Collections`, `Universal`,
   `Pseudorandom`, `NextBit`, `HardCore`, `Encryption`, `PRF`, `MultiMessage`, `BlockEncryptor`,
   `PublicKey` added); `BlockEncryptor` listed under `## Contents`; integration note removed.
2. `TCSlib/Cryptography/Candidates.lean` — imports `RSA`, `Rabin`, `DiscreteLog`, `DiscreteLogHardcore`,
   `ElGamal` added; integration note removed.
3. `TCSlib/Cryptography/ZeroKnowledge.lean` — imports `GraphIsomorphism`, `GraphIsomorphismZK`,
   `Commitment`, `ThreeColoring` (sub-facade), `NP`, `Encryption` added; "(planned …)" markers and
   integration note removed.
4. `TCSlib/Complexity/Randomized.lean`, `TCSlib/Cryptography/NumberTheory.lean` — already complete.
5. `TCSlib.lean` — `import TCSlib.Complexity.Randomized` (Complexity block, after `PolyHierarchy`) and
   `import TCSlib.Cryptography.{Asymptotic,Candidates,NumberTheory,ZeroKnowledge}` (Cryptography block).
6. `TCSlib/ComputationalModels.lean` — `import TCSlib.Complexity.Randomized.PPT`, the `## Models`
   bullet `Complexity.NUPPT` (alphabetical, between `CNF n / DNF n` and `DecisionTree n`), and the
   `[PS10]` reference. (The file's five pre-existing `style_lint` findings — missing `set_option`s and
   `## Main definitions/results` headings — predate the campaign and were left alone.)
7. `TCSlib/Cryptography/Candidates/ElGamal.lean` (Cand3; reported unverified) — four proof repairs,
   no statement changed: `constSelector_unique` (unsynthesizable placeholder in
   `Nat.not_lt_zero _` → `absurd i.2 (by simp …)`); `GroupPKScheme.Secure.const` (`congr 2 <;> funext`
   hit non-function goals → two explicit `have` equations then `rw`); `egGroupGen_valid`
   (`rw [← ha]` had an ill-typed motive → rewrite only in a local `have`; the occurrence of
   `dlP …` inside `ZMod (…)` is not reached by `simp`, now abstracted by `rw [pairFstD_pairEncode]`);
   `polyTimeComputable_egDecStr` (the unifier unfolds `xgcdStr`/`modExpStr` when matching the
   `∘`-chain against `egDecStr` and does not terminate — bisected to this one proof; the chain is now
   transported pointwise by the private `polyTimeComputable_of_forall_eq` with
   `simp only [Function.comp_apply, egDecStr]`). The module now compiles in 8 s with the expected
   7 sorries; `TCSlib.Cryptography.Candidates.DiscreteLogHardcore` (stale olean) was rebuilt unchanged.
8. `audits/pass-shelat/Checks.lean` — imports of the five facades and 243 `#print axioms` lines
   (sanity theorems, every frozen stub of DESIGN.md §9, every theorem whose docstring cites a numbered
   [PS10] result).
9. New: `audits/pass-shelat/run2-axioms.log`, `audits/pass-shelat/run2-census.md` (this file).

No duplicate declaration names across the new files were found (syntactic scan of every public
declaration with its namespace; confirmed by the import of all five facades in `Checks.lean`).

## Census of the campaign files

| File | Module | Lines | `sorry` warnings | Errors | style_lint |
| --- | --- | ---: | ---: | ---: | --- |
| `TCSlib/Complexity/Randomized/Closure.lean` | `TCSlib.Complexity.Randomized.Closure` | 398 | 0 | 0 | clean |
| `TCSlib/Complexity/Randomized/NonUniform.lean` | `TCSlib.Complexity.Randomized.NonUniform` | 182 | 1 | 0 | clean |
| `TCSlib/Complexity/Randomized/PolyExpr.lean` | `TCSlib.Complexity.Randomized.PolyExpr` | 194 | 0 | 0 | clean |
| `TCSlib/Complexity/Randomized/PPT.lean` | `TCSlib.Complexity.Randomized.PPT` | 337 | 0 | 0 | clean |
| `TCSlib/Complexity/Randomized/Primitives.lean` | `TCSlib.Complexity.Randomized.Primitives` | 212 | 2 | 0 | clean |
| `TCSlib/Complexity/Randomized/Repetition.lean` | `TCSlib.Complexity.Randomized.Repetition` | 321 | 7 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/Adversary.lean` | `TCSlib.Cryptography.Asymptotic.Adversary` | 219 | 0 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/BlockEncryptor.lean` | `TCSlib.Cryptography.Asymptotic.BlockEncryptor` | 379 | 0 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/Collections.lean` | `TCSlib.Cryptography.Asymptotic.Collections` | 599 | 2 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/Encryption.lean` | `TCSlib.Cryptography.Asymptotic.Encryption` | 532 | 2 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/Ensembles.lean` | `TCSlib.Cryptography.Asymptotic.Ensembles` | 495 | 5 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/HardCore.lean` | `TCSlib.Cryptography.Asymptotic.HardCore` | 905 | 6 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/MultiMessage.lean` | `TCSlib.Cryptography.Asymptotic.MultiMessage` | 486 | 4 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/NextBit.lean` | `TCSlib.Cryptography.Asymptotic.NextBit` | 470 | 6 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/OneWay.lean` | `TCSlib.Cryptography.Asymptotic.OneWay` | 606 | 3 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/PRF.lean` | `TCSlib.Cryptography.Asymptotic.PRF` | 575 | 5 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/Pseudorandom.lean` | `TCSlib.Cryptography.Asymptotic.Pseudorandom` | 182 | 0 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/PublicKey.lean` | `TCSlib.Cryptography.Asymptotic.PublicKey` | 714 | 4 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/Sampling.lean` | `TCSlib.Cryptography.Asymptotic.Sampling` | 825 | 1 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic/Universal.lean` | `TCSlib.Cryptography.Asymptotic.Universal` | 599 | 3 | 0 | clean |
| `TCSlib/Cryptography/Candidates/Arithmetic.lean` | `TCSlib.Cryptography.Candidates.Arithmetic` | 235 | 0 | 0 | clean |
| `TCSlib/Cryptography/Candidates/Concrete.lean` | `TCSlib.Cryptography.Candidates.Concrete` | 430 | 0 | 0 | clean |
| `TCSlib/Cryptography/Candidates/DiscreteLog.lean` | `TCSlib.Cryptography.Candidates.DiscreteLog` | 534 | 4 | 0 | clean |
| `TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean` | `TCSlib.Cryptography.Candidates.DiscreteLogHardcore` | 558 | 7 | 0 | clean |
| `TCSlib/Cryptography/Candidates/ElGamal.lean` | `TCSlib.Cryptography.Candidates.ElGamal` | 801 | 7 | 0 | clean |
| `TCSlib/Cryptography/Candidates/Factoring.lean` | `TCSlib.Cryptography.Candidates.Factoring` | 586 | 8 | 0 | clean |
| `TCSlib/Cryptography/Candidates/Rabin.lean` | `TCSlib.Cryptography.Candidates.Rabin` | 924 | 17 | 0 | clean |
| `TCSlib/Cryptography/Candidates/RSA.lean` | `TCSlib.Cryptography.Candidates.RSA` | 922 | 8 | 0 | clean |
| `TCSlib/Cryptography/NumberTheory/Chebyshev.lean` | `TCSlib.Cryptography.NumberTheory.Chebyshev` | 308 | 0 | 0 | clean |
| `TCSlib/Cryptography/NumberTheory/Euclid.lean` | `TCSlib.Cryptography.NumberTheory.Euclid` | 211 | 0 | 0 | clean |
| `TCSlib/Cryptography/NumberTheory/ModExp.lean` | `TCSlib.Cryptography.NumberTheory.ModExp` | 184 | 0 | 0 | clean |
| `TCSlib/Cryptography/NumberTheory/Primality.lean` | `TCSlib.Cryptography.NumberTheory.Primality` | 436 | 2 | 0 | clean |
| `TCSlib/Cryptography/NumberTheory/QuadraticResidues.lean` | `TCSlib.Cryptography.NumberTheory.QuadraticResidues` | 498 | 0 | 0 | clean |
| `TCSlib/Cryptography/NumberTheory/Units.lean` | `TCSlib.Cryptography.NumberTheory.Units` | 216 | 0 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge/Commitment.lean` | `TCSlib.Cryptography.ZeroKnowledge.Commitment` | 600 | 4 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge/Defs.lean` | `TCSlib.Cryptography.ZeroKnowledge.Defs` | 256 | 1 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge/Encoding.lean` | `TCSlib.Cryptography.ZeroKnowledge.Encoding` | 342 | 4 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge/Encryption.lean` | `TCSlib.Cryptography.ZeroKnowledge.Encryption` | 175 | 1 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean` | `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism` | 785 | 17 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean` | `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphismZK` | 438 | 3 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean` | `TCSlib.Cryptography.ZeroKnowledge.Interaction` | 356 | 0 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean` | `TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs` | 343 | 2 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge/NP.lean` | `TCSlib.Cryptography.ZeroKnowledge.NP` | 388 | 3 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean` | `TCSlib.Cryptography.ZeroKnowledge.ThreeColoring` | 44 | 0 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean` | `TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Language` | 338 | 2 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean` | `TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol` | 534 | 9 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean` | `TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Simulator` | 572 | 7 | 0 | clean |
| `TCSlib/Complexity/Randomized.lean` | `TCSlib.Complexity.Randomized` | 52 | 0 | 0 | clean |
| `TCSlib/Cryptography/Asymptotic.lean` | `TCSlib.Cryptography.Asymptotic` | 75 | 0 | 0 | clean |
| `TCSlib/Cryptography/Candidates.lean` | `TCSlib.Cryptography.Candidates` | 60 | 0 | 0 | clean |
| `TCSlib/Cryptography/NumberTheory.lean` | `TCSlib.Cryptography.NumberTheory` | 48 | 0 | 0 | clean |
| `TCSlib/Cryptography/ZeroKnowledge.lean` | `TCSlib.Cryptography.ZeroKnowledge` | 67 | 0 | 0 | clean |

Totals: 52 files, 21546 lines, 157 `declaration uses 'sorry'` warnings.

All 52 files: `style_lint` clean; every file ≤ 1000 lines (over the 600-line target: `HardCore`
905, `Rabin` 924, `RSA` 922, `Sampling` 825, `ElGamal` 801, `GraphIsomorphism` 785, `PublicKey` 714,
`OneWay` 606 — split candidates for run 4).

## Axiom prints (`run2-axioms.log`)

* 101 declarations print exactly `[propext, Classical.choice, Quot.sound]`;
  142 print `sorryAx` (statement-phase stubs or dependence on a stub); 0 print anything else.
* All seven sanity theorems are clean: `Complexity.NUPPT.nonempty`, `not_strongOneWay_id`,
  `FunFamily.StrongOneWay.weak`, `Ensemble.Indist.refl`, `OracleEnsemble.Indist.refl`,
  `npProtocol_interactiveProof`, `hybrid_lemma`.

Clean (101): `Complexity.NUPPT.nonempty`, `Complexity.PPT.nonempty`, `not_strongOneWay_id`, `FunFamily.StrongOneWay.weak`, `Ensemble.Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof`, `hybrid_lemma`, `Complexity.NUPPT.exists_comp`, `Complexity.NUPPT.exists_withAdvice`, `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`, `rejectionSample_uniform_of_some`, `uprob_rejectionSample_none`, `statClose_rejectionSample`, `uprob_permFromCoins_none_le`, `OneWay.invProb_prodFun_le_yaoTry`, `claim_38_2`, `FunFamily.StrongOneWay.toCollection_oneWay`, `FunFamily.StrongOneWay.exists_collection_oneWay`, `claim_65_1`, `claim_65_2`, `claim_65_2_cond`, `NumberTheory.two_pow_le_pow_primeCounting`, `NumberTheory.chebyshev_two_mul`, `NumberTheory.chebyshev`, `NumberTheory.one_div_le_uprob_prime_pair`, `NumberTheory.extEuclid_spec`, `NumberTheory.extEuclid_inv`, `NumberTheory.extEuclidCalls_le`, `NumberTheory.modExpMults_le`, `NumberTheory.totient_prime_mul_prime`, `NumberTheory.card_units_zmod_prime_mul_prime`, `NumberTheory.units_pow_mod_totient`, `NumberTheory.pow_mod_totient_modEq`, `NumberTheory.rsa_pow_pow`, `NumberTheory.rsa_pow_bijective`, `NumberTheory.exists_rsa_inverse`, `NumberTheory.le_totient_mul_log_succ`, `NumberTheory.mrLiar_iff_of_prime`, `NumberTheory.card_mrLiars_of_prime`, `NumberTheory.millerRabin_of_prime`, `NumberTheory.samplePrime_uniform_of_some`, `NumberTheory.uprob_samplePrime_none_le`, `NumberTheory.uprob_samplePrime_none_le_exp`, `NumberTheory.uprob_samplePrime_none_le_two_pow`, `NumberTheory.statClose_samplePrime`, `NumberTheory.card_QR_prime`, `NumberTheory.card_sqrt_eq_two`, `NumberTheory.sqrtMod3_sq`, `NumberTheory.pow_div_four_succ_mem_QR`, `NumberTheory.mem_QR_mul_iff`, `NumberTheory.card_sqrt_mul_eq_four`, `NumberTheory.card_QR_mul`, `NumberTheory.pushesUniform_sqTo`, `NumberTheory.gcd_sub_eq_prime_of_sq_eq_sq`, `NumberTheory.blumSqrt_sq`, `NumberTheory.sqTo_bijective_of_blum`, `Candidates.invProb_prodFun_le_plant`, `Candidates.one_div_le_uprob_prime_pair_bits`, `Candidates.fmultNat_eq_mul_prime`, `Candidates.fmult_inv_factor`, `Candidates.rsaPerm_symm_apply`, `Candidates.pushesUniform_rsaPerm`, `Candidates.rabin_symmetry`, `Candidates.expF_injective`, `Candidates.GroupPKScheme.Secure.const`, `not_negligible_iff_exists_polyExpr`, `Ensemble.Indist.symm`, `Ensemble.Indist.trans`, `predict_eq`, `Ensemble.uniform_pseudorandom`, `PRG.stretch_pos`, `exists_owpPredictorSnoc`, `exists_expandRed_ge`, `FunFamily.glPad_f_bijective`, `distAdv_padXor_le`, `PrivateKeyScheme.ZeroKnowledge.singleMessageSecure`, `Complexity.NUPPT.toOracleAdversary_boundedBy`, `oracle_hybrid_lemma`, `two_mul_add_one_expands`, `thm_97_3_1`, `thm_97_3_2`, `acceptProb_otpEnc`, `BitPublicKeyScheme.singleBitSecure_iff`, `predProb_pkPredictor_false`, `exists_pkPredictor`, `StatZK.zk`, `StatZK.hvzk`, `ZK.hvzk`, `PerfectZK.zk`, `uprob_gi_cheat_le_half`, `gi_sim_H_dist`, `gi_sim_half`, `exists_pairRed_ge`, `owpComStr_binding`, `exists_bitComPredictor`, `one_sub_inv_pow_mul_le_exp`, `colVerify_honest`, `exists_bad_edge`.

`sorryAx` (142): `Complexity.polyTimeComputable_unaryPoly`, `Complexity.NUPPT.decides_of_decidesWithAdviceInTime`, `Turing.FinTM.computesFunInTime_pairSplitAt`, `Turing.FinTM.computesFunInTime_unaryMul`, `Complexity.polyTimeComputable_pairTakePoly`, `Complexity.polyTimeComputable_pairDropPoly`, `Complexity.NUPPT.exists_reparam`, `Complexity.NUPPT.exists_reparam_advice`, `Complexity.NUPPT.exists_split`, `Complexity.NUPPT.exists_seq`, `Complexity.polyTimeComputable_iterateFind`, `Complexity.polyTimeComputable_iterate`, `Complexity.polyTimeComputable_iterateEmit`, `Complexity.polyTimeComputable_majority`, `Complexity.polyTimeComputable_pairXor`, `Complexity.polyTimeComputable_pairEq`, `Complexity.polyTimeComputable_blockMap`, `permFromCoins_uniform_of_some`, `FunFamily.Easy.prod`, `weak_to_strong`, `strong_prod_two`, `Collection.OneWay.owfFamily_strongOneWay`, `Collection.OneWay.exists_strongOneWay`, `fUniversal_easy`, `lemma_64_3`, `fUniversal_hard`, `fUniversal_weakOneWay`, `theorem_63_1`, `NumberTheory.two_mul_card_mrLiars_le`, `NumberTheory.uprob_millerRabin_le`, `NumberTheory.exists_samplePrime_nuppt`, `Candidates.fmult_easy`, `Candidates.fmult_weakOneWay`, `Candidates.fmult_prod_strongOneWay`, `Candidates.factoringCollection_sampleClose`, `Candidates.factoringCollection_invProbAt_le`, `Candidates.factoringCollection_oneWay`, `Candidates.rsaInv_spec`, `Candidates.rsaCollection_sampleClose`, `Candidates.rsaCollection_invProbAt_le`, `Candidates.rsaCollection_oneWay`, `Candidates.rsaTrapdoor_oneWay`, `Candidates.factorProb_le_rsaProb`, `Candidates.rsa_imp_factoring`, `Candidates.rabinCollection_sampleClose`, `Candidates.rabinCollection_invProbAt_le`, `Candidates.blumInv_spec`, `Candidates.rabinBlumTrapdoor_sampleClose`, `Candidates.rabinBlumTrapdoor_invProbAt_le`, `Candidates.rabinBlumTrapdoor_oneWay`, `Candidates.blumFactorProb_le_invProbAt`, `Candidates.blumFactoring_of_rabinBlum_oneWay`, `Candidates.expCollection_sampleClose`, `Candidates.expCollection_invProbAt_le`, `Candidates.expCollection_oneWay`, `Candidates.dlCollection_oneWay`, `Candidates.uprob_majOracle_ne_le`, `Candidates.invProb_dlInverter_ge`, `Candidates.fullDLCollection_oneWay`, `Candidates.fullDLCollection_hardCore`, `Candidates.statClose_sq_generator`, `Candidates.elGamal_correct`, `Candidates.elGamal_secure`, `Ensemble.Indist.toLit`, `Ensemble.IndistLit.toIndist`, `Ensemble.Indist.push`, `Ensemble.Indist.copies`, `prediction_lemma`, `acceptProb_nextBitHybrid_mix`, `nextBitProb_nextBitPred_false`, `exists_nextBitPred`, `Ensemble.NextBitUnpredictable.pseudorandom`, `Ensemble.Pseudorandom.nextBitUnpredictable`, `owp_hardcore_prg`, `prg_expand`, `cor_81_7`, `FunFamily.StrongOneWay.glPad`, `FunFamily.StrongOneWay.glPad_hardCore`, `goldreich_levin`, `Collection.OneWay.glPad`, `Collection.OneWay.glPad_hardCore`, `goldreich_levin_coll`, `PermCollection.OneWay.glPad`, `TrapdoorCollection.OneWay.glPad`, `TrapdoorCollection.OneWay.glPad_hardCore`, `prgScheme_singleMessageSecure`, `PrivateKeyScheme.not_multiMessageSecure_of_deterministic`, `PrivateKeyScheme.SingleMessageSecure.zeroKnowledge`, `PrivateKeyScheme.singleMessageSecure_iff_zeroKnowledge`, `PRG.Secure.doubling`, `exists_ggmBitsDist_nuppt`, `ggmPRF_prf`, `exists_prf_of_exists_prg`, `uprob_not_injective_le`, `distAdv_prfEncReal_random_otp_le`, `distAdv_prfEncReal_le`, `prfScheme_multiMessageSecure`, `distAdv_multi_le_sum`, `BitPublicKeyScheme.bitwiseEncFun_poly`, `BitPublicKeyScheme.SingleBitSecure.bitwise`, `PublicKeyScheme.Secure.multiMessageSecure`, `TrapdoorCollection.tdpBitScheme_singleBitSecure`, `TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure`, `WitnessRelation.mem_NP`, `exists_witnessRelation_of_mem_NP`, `negligible_inv_pow_sqrt_div`, `pushesUniform_coinTable`, `polyTimeComputable_encPermGraph`, `polyTimeComputable_encPermMulInv`, `polyTimeComputable_encPermFromCoins`, `Riso_witnessRelation`, `uprob_gi_rep_cheat_le`, `uprob_gni_rep_cheat`, `gni_interactiveProofErr`, `gni_interactiveProof`, `gi_efficientProverProofErr`, `gi_rep_efficientProverProof`, `gi_rep_interactiveProof`, `statClose_giSimTrunc`, `exists_giSimulator`, `gi_statZK`, `gi_zk`, `gi_hvzk`, `HardCore.bitHiding`, `BitHiding.owpComStr_hides`, `owpComStr_polyTimeComputable`, `owp_commitment`, `exists_commitment_of_owp_hardCore`, `uprob_col_cheat_le`, `R3COL_witnessRelation`, `col_efficientProverProofErr`, `colRep_efficientProverProof`, `colRep_interactiveProof`, `statClose_colSimTruncH`, `exists_colSimRed_ge`, `col_zk`, `col_hvzk`, `col_zeroKnowledgeProof`, `zk_proof_of_levinReduction`, `zk_proof_of_owp_levinReduction`, `zk_proof_of_mem_NP`, `zk_proof_of_mem_NP_of_owp`.

## Inventory coverage and items reported missing

* Coverage check (integrator): every core inventory id of the workstream table (plan §6 / DESIGN.md §6)
  was looked up in its owning files, either verbatim (`Def-124.f`, `Inf-4.2`, …) or in citation form
  (`[PS10, Theorem 35.1]`, …); the eleven ids that matched neither were checked by hand against their
  concept: `Def-29.3` (`Primes n`, Chebyshev.lean), `Def-49.1` (`mrLiars`/`MRLiar`, Primality.lean),
  `Def-57.0`/`Def-59.3` (`QR N`, QuadraticResidues.lean), `Claim-73.a`/`Claim-73.b` (p. 73 "show this",
  `not_negligible_iff_exists_polyExpr`, Ensembles.lean), `Ineq-189.a` (`pairwise_sampling_ineq`,
  Ensembles.lean), `Def-95.a` (reused `randomFunction`, PRF.lean), `Def-103.c`/`Def-103.e`/`Thm-103.f`
  (p. 103 definitions and `BitPublicKeyScheme.SingleBitSecure.bitwise`, PublicKey.lean). **No core id
  is missing.**
* Items reported by workstreams as not stated / deferred (none is a core id):
  `Lem-50.15b` (`two_mul_card_mrLiars_le`, deferred by the plan, sorried under a sketch; makes
  `uprob_millerRabin_le`'s composite case print `sorryAx`); the non-vacuity of `ExpGroupGen` (Cand3,
  no inventory id; left to the fill phase); the optional modules of D11 (`NUPPTSeq`,
  `NUPPT.ofPartial`, `exists_queryTree`).
* Statement-level issues flagged for the run-3 audit: C2b — the frozen `Collection.OneWay.exists_strongOneWay`
  (Thm 42.2 ⇒) is not provable from the frozen `Collection` fields (sampler outputs need not decode);
  the provable form `owfFamily_strongOneWay` adds `Collection.EvalSampled`. S/C4b — the frozen
  `permFromCoins n n n` in `giProver` cannot give a negligible failure probability; C4b uses
  `Nat.size n` bits and `n²` trials locally and asks the maintainer to ratify and propagate to
  `Encoding.polyTimeComputable_encPermFromCoins` and C4d. C4b — verifiers gained `wellFormedInstance`.
  Cand1 — `oneCallFactorer` parameter `2n` versus `fmult`'s inverter at `n` (fill detail).
