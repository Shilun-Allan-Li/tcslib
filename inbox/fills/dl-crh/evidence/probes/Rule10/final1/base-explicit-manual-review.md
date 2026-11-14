# Base explicit scan manual review draft

Status: `PENDING_NATIVE_KIND_HOME`. This draft grants no global clearance.

All 208 rows retained; 32 source-reviewed local/inline proof rows, 176 global rows pending native kind/home review.

| ID | Source | Tactic item | Source disposition | Native state |
|---|---|---|---|---|
| B001 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:158 | `dlW` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B002 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:158 | `ha` | LOCAL_PROOF | NOT_RUN |
| B003 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:164 | `length_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B004 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:164 | `ha` | LOCAL_PROOF | NOT_RUN |
| B005 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:164 | `hb` | LOCAL_PROOF | NOT_RUN |
| B006 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:164 | `hc` | LOCAL_PROOF | NOT_RUN |
| B007 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:192 | `expOrd` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B008 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:205 | `expOrd` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B009 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:228 | `← orderOf_units` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B010 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:228 | `coe_expUnit` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B011 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:249 | `expDec` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B012 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:249 | `if_pos ⟨by simp [expEnc], by rw [hl]; exact ZMod.val_lt x⟩` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B013 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:249 | `hl` | LOCAL_PROOF | NOT_RUN |
| B014 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:250 | `ZMod.natCast_zmod_val` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B015 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:249 | `expEnc` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B016 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:249 | `hl` | LOCAL_PROOF | NOT_RUN |
| B017 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:257 | `expDec` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B018 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:259 | `← Option.some.inj h` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B019 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:259 | `expEnc` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B020 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:259 | `natToList_val_natCast hw.1 hw.2` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B021 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `expEval` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B022 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `expF` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B023 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `expEnc` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B024 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `dlG` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B025 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `dlP` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B026 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `dlW` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B027 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `pairFstD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B028 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `pairSndD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B029 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:283 | `modExpStr_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B030 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:284 | `hl` | LOCAL_PROOF | NOT_RUN |
| B031 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:306 | `Units.val_pow_eq_pow_val` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B032 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:306 | `Units.val_pow_eq_pow_val` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B033 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:306 | `coe_expUnit` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B034 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:306 | `← Nat.cast_pow` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B035 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:307 | `← Nat.cast_pow` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B036 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:307 | `← ZMod.natCast_mod` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B037 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:307 | `h1` | LOCAL_PROOF | NOT_RUN |
| B038 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:307 | `ZMod.natCast_mod` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B039 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:309 | `orderOf_expUnit h` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B040 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:415 | `dlProb` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B041 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:416 | `uexp_def` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B042 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:422 | `dlProb` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B043 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:432 | `← uprob_false (α := G.gen.Coins n)` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B044 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:442 | `abs_zero` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B045 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:460 | `dlP` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B046 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:460 | `dlDefaultIndex` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B047 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:460 | `listToNat_natToList (by norm_num : 3 < 2 ^ 2)` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B048 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:462 | `dlM` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B049 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:462 | `dlDefaultIndex` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B050 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:462 | `listToNat_natToList (by norm_num : 2 < 2 ^ 2)` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B051 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:464 | `dlG` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B052 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:464 | `dlDefaultIndex` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B053 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:464 | `listToNat_natToList (by norm_num : 2 < 2 ^ 2)` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B054 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:466 | `h3` | LOCAL_PROOF | NOT_RUN |
| B055 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:467 | `h2` | LOCAL_PROOF | NOT_RUN |
| B056 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:468 | `h2` | LOCAL_PROOF | NOT_RUN |
| B057 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:468 | `h3` | LOCAL_PROOF | NOT_RUN |
| B058 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:469 | `hg` | LOCAL_PROOF | NOT_RUN |
| B059 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:470 | `hg` | LOCAL_PROOF | NOT_RUN |
| B060 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:470 | `h3` | LOCAL_PROOF | NOT_RUN |
| B061 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:471 | `hg` | LOCAL_PROOF | NOT_RUN |
| B062 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:471 | `h2` | LOCAL_PROOF | NOT_RUN |
| B063 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:471 | `h3` | LOCAL_PROOF | NOT_RUN |
| B064 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:493 | `Function.comp_apply` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B065 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:493 | `pairFstD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B066 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:493 | `pairSndD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B067 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:502 | `expGenFun` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B068 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:502 | `decide_eq_true_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B069 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:513 | `expGen` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B070 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:520 | `NUPPT.coinLen_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B071 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:520 | `NUPPT.coinLen_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B072 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:520 | `expGen_coins` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B073 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:558 | `NUPPT.runAt_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B074 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:558 | `NUPPT.runAt_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B075 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:558 | `expGen_coinsEquiv_ofFn` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B076 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:558 | `NUPPT.Uniform.runAtL_eq G.gen_uniform` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B077 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:559 | `expGen` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B078 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:560 | `NUPPT.runAtL_ofPolyTimeUniform` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B079 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:561 | `expGenFun` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B080 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:561 | `NUPPT.inParam_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B081 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:561 | `NUPPT.inCoins_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B082 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:561 | `NUPPT.advInput_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B083 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:561 | `NUPPT.layout_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B084 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:562 | `pairFstD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B085 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:562 | `pairSndD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B086 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:562 | `List.length_replicate` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B087 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:579 | `rejectBlocksL_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B088 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:585 | `sampleBelowL` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B089 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:586 | `List.findSome?_eq_some_iff` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B090 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:589 | `Option.some.injEq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B091 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:627 | `← uprob_comp_equiv (bitsEquiv (Nat.size m)) (fun v : Fin (2 ^ Nat.size m) => (v : ℕ) < m)` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B092 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:628 | `bitsEquiv_val` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B093 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:630 | `hacc` | LOCAL_PROOF | NOT_RUN |
| B094 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:632 | `← uprob_rejectionSample_none m (Nat.size m) n hm hmk.le` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B095 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:634 | `sampleBelowL_eq_rejectBlocksL` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B096 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:660 | `dla_belowAcc` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B097 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:660 | `pairFstD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B098 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:660 | `pairSndD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B099 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:660 | `← decide_not` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B100 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:660 | `decide_eq_decide` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B101 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:661 | `Nat.not_le` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B102 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:699 | `Function.comp_apply` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B103 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:699 | `pairFstD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B104 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:699 | `pairSndD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B105 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:699 | `PolyExpr.eval_var` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B106 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:700 | `subStr_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B107 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:700 | `Nat.sub_self` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B108 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:701 | `natToList_zero_append_drop` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B109 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:702 | `expSampleRaw` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B110 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:702 | `dlW` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B111 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:704 | `dlM_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B112 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:704 | `← length_sizeStr` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B113 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:704 | `sampleBelowL_eq_rejectBlocksL` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B114 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:705 | `show rejectBlocksL (· < listToNat (pairFstD (pairSndD (NUPPT.inArg z))))         (sizeStr (pairFstD (pairSndD (NUPPT.inArg z)))).length (NUPPT.inParam z).length         (NUPPT.inParam z).length (NUPPT.inCoins z) =       if g z = [] then none else some (listToNat (g z).tail) from (hs z).2` | INLINE_LOCAL_PROOF | NOT_RUN |
| B115 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:710 | `he` | LOCAL_PROOF | NOT_RUN |
| B116 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:710 | `List.tail_nil` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B117 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:710 | `listToNat_nil` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B118 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:723 | `NUPPT.runAt_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B119 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:724 | `expSampler` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B120 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:725 | `NUPPT.runAtL_ofPolyTimeUniform` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B121 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:726 | `expSampleRaw` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B122 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:726 | `NUPPT.inArg_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B123 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:726 | `NUPPT.inParam_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B124 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:726 | `NUPPT.inCoins_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B125 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:726 | `NUPPT.advInput_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B126 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:746 | `expGen_runAt` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B127 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:748 | `pairFstD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B128 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:750 | `pairFstD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B129 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:753 | `expSampler_runAt` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B130 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:758 | `hvdef` | LOCAL_PROOF | NOT_RUN |
| B131 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:758 | `hs` | LOCAL_PROOF | NOT_RUN |
| B132 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:758 | `Option.getD_none` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B133 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:760 | `hvdef` | LOCAL_PROOF | NOT_RUN |
| B134 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:760 | `hs` | LOCAL_PROOF | NOT_RUN |
| B135 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:760 | `Option.getD_some` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B136 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:765 | `expEnc_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B137 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:765 | `ZMod.val_natCast` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B138 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:765 | `Nat.mod_eq_of_lt hvo` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B139 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:767 | `← henc` | LOCAL_PROOF | NOT_RUN |
| B140 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:767 | `expDec_expEnc` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B141 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:768 | `← henc` | LOCAL_PROOF | NOT_RUN |
| B142 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:768 | `expEval_spec` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B143 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:879 | `Collection.index_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B144 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:880 | `if_pos hn` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B145 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:880 | `pairFstD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B146 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:887 | `Collection.index_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B147 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:889 | `if_neg (not_le.mpr hn)` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B148 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:889 | `pairFstD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B149 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:918 | `expSampler` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B150 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:921 | `PolyExpr.eval_mul` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B151 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:921 | `PolyExpr.eval_var` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B152 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:926 | `← NUPPT.coinsEquivPoly_ofFn hcoins n s` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B153 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:935 | `ZMod.val_natCast` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B154 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:935 | `Nat.mod_eq_of_lt (lt_of_lt_of_eq x.2 hord.symm)` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B155 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:942 | `hofn` | LOCAL_PROOF | NOT_RUN |
| B156 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:942 | `expSampler_runAt` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B157 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:946 | `← expEnc_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B158 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:946 | `expDec_expEnc` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B159 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:947 | `hX` | LOCAL_PROOF | NOT_RUN |
| B160 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:947 | `hY` | LOCAL_PROOF | NOT_RUN |
| B161 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:971 | `if_neg (not_lt.2 hn)` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B162 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:971 | `one_div` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B163 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:972 | `Collection.sampleClose_iff` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B164 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:975 | `if_pos hn` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B165 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:977 | `if_neg hn` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B166 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:985 | `expCollection_sample` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B167 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:986 | `expCollection_decD` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B168 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:994 | `Option.map_some` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B169 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:994 | `Equiv.symm_apply_apply` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B170 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:995 | `hY` | LOCAL_PROOF | NOT_RUN |
| B171 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1006 | `expDec` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B172 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1009 | `hw` | LOCAL_PROOF | NOT_RUN |
| B173 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1010 | `decodeFin_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B174 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1010 | `dif_pos hlen` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B175 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1012 | `bitsToNat_eq_listToNat` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B176 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1012 | `← List.ofFn_congr hlen w.get` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B177 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1012 | `List.ofFn_get` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B178 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1012 | `← Option.some.inj hdec` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B179 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1013 | `ZMod.val_natCast` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B180 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1013 | `Nat.mod_eq_of_lt hlt` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B181 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1031 | `Collection.invProbAt_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B182 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1031 | `ExpGroupGen.dlProb_eq` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B183 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1036 | `expCollection_index H G hV n r hn` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B184 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1039 | `← uprob_comp_equiv     (Equiv.prodCongr (expCollection_domEquiv H G hV i).symm (Equiv.refl (A.Coins n)))` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B185 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1043 | `Equiv.prodCongr_apply` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B186 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1043 | `Prod.map_fst` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B187 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1043 | `Prod.map_snd` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B188 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1043 | `Equiv.refl_apply` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B189 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1044 | `expCollection_f` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B190 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1044 | `expCollection_decD` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B191 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1044 | `Equiv.apply_symm_apply` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B192 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1046 | `Equiv.apply_symm_apply` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B193 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1060 | `abs_of_nonneg (Collection.invProbAt_nonneg _ A n)` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B194 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1060 | `abs_of_nonneg (G.dlProb_nonneg A n)` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B195 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:137 | `Function.comp_apply` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B196 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:153 | `dlHashGenFun` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B197 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:153 | `Function.comp_apply` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B198 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:153 | `pairFstD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B199 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:153 | `pairSndD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B200 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:162 | `Function.comp_apply` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B201 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:167 | `dlHashPow` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B202 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:167 | `Function.comp_apply` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B203 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:180 | `dlHashMul` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B204 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:180 | `Function.comp_apply` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B205 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:192 | `Function.comp_apply` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B206 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:192 | `pairFstD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B207 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:192 | `pairSndD_pairEncode` | GLOBAL_PENDING_NATIVE | NOT_RUN |
| B208 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:192 | `PolyExpr.eval_var` | GLOBAL_PENDING_NATIVE | NOT_RUN |

The JSON retains exact source hashes, context lines, local-binding evidence, provisional own-declaration hints, and every native candidate when available.
All global hints are provisional. After native review, preserve every foreign definition hit and every unresolved/ambiguous-row disposition, and record inherited base findings separately from new final findings.
