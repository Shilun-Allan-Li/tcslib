# Complete base explicit scan manual review

Status: `COMPLETE`; all 208 rows reviewed, zero pending rows, zero foreign ordinary-definition heads.

The exact final2 plan/native table and original source hashes are bound in the JSON. The final1 inventory is byte-for-byte identical by row.

Categories: 31 local proofs, one inline local proof, 36 own-definition body uses and 140 theorem readers.

## Individual lexical corrections

| Row | Item | Source evidence and completed disposition |
|---|---|---|
| B002 | `ha` | Binding at original line 157:   obtain ⟨a, b, c, rfl, ha, -, -⟩ := h |
| B004 | `ha` | Binding at original line 163:   obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := h |
| B005 | `hb` | Binding at original line 163:   obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := h |
| B006 | `hc` | Binding at original line 163:   obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := h |
| B114 | `show` | Binding at original line 686:   obtain ⟨g, hg, hs⟩ := polyTimeComputable_rejectBlocksL (fun a v => v < a) (dla_belowAcc_poly H) |
| B115 | `he` | Binding at original line 709:   split_ifs with he |
| B130 | `hvdef` | Binding at original line 755:   set v := (sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn s)).getD 0 with hvdef |
| B131 | `hs` | Binding at original line 757:     rcases hs : sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn s) with _ \| w |
| B133 | `hvdef` | Binding at original line 755:   set v := (sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn s)).getD 0 with hvdef |
| B134 | `hs` | Binding at original line 757:     rcases hs : sampleBelowL (dlM i) (Nat.size (dlM i)) n n (List.ofFn s) with _ \| w |
| B153 | `ZMod.val_natCast` | The binder regex misclassified ZMod from the type at line 929. No local declaration binds the name ZMod; line 935 uses the qualified global theorem. Exact native identity/kind/home is recorded. |

## Every source item

| ID | Source | Head | Completed disposition | Native constant kind/home |
|---|---|---|---|---|
| B001 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:158 | `dlW` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.dlW; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B002 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:158 | `ha` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B003 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:164 | `length_pairEncode` | THEOREM_READER_CONFIRMED | Turing.length_pairEncode; theorem; TCSlib.Complexity.TuringMachine.Encoding |
| B004 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:164 | `ha` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B005 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:164 | `hb` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B006 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:164 | `hc` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B007 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:192 | `expOrd` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expOrd; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B008 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:205 | `expOrd` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expOrd; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B009 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:228 | `orderOf_units` | THEOREM_READER_CONFIRMED | orderOf_units; theorem; Mathlib.GroupTheory.OrderOfElement |
| B010 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:228 | `coe_expUnit` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.coe_expUnit; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B011 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:249 | `expDec` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expDec; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B012 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:249 | `if_pos` | THEOREM_READER_CONFIRMED | if_pos; theorem; Init.Core |
| B013 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:249 | `hl` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B014 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:250 | `ZMod.natCast_zmod_val` | THEOREM_READER_CONFIRMED | ZMod.natCast_zmod_val; theorem; Mathlib.Data.ZMod.Basic |
| B015 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:249 | `expEnc` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expEnc; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B016 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:249 | `hl` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B017 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:257 | `expDec` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expDec; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B018 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:259 | `Option.some.inj` | THEOREM_READER_CONFIRMED | Option.some.inj; theorem; Init.Core |
| B019 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:259 | `expEnc` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expEnc; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B020 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:259 | `natToList_val_natCast` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.natToList_val_natCast; theorem; TCSlib.Cryptography.Candidates.Arithmetic |
| B021 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `expEval` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expEval; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B022 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `expF` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expF; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B023 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `expEnc` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expEnc; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B024 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `dlG` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.dlG; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B025 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `dlP` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.dlP; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B026 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `dlW` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.dlW; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B027 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `pairFstD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairFstD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B028 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:282 | `pairSndD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairSndD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B029 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:283 | `modExpStr_pairEncode` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.modExpStr_pairEncode; theorem; TCSlib.Cryptography.Candidates.Arithmetic |
| B030 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:284 | `hl` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B031 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:306 | `Units.val_pow_eq_pow_val` | THEOREM_READER_CONFIRMED | Units.val_pow_eq_pow_val; theorem; Mathlib.Algebra.Group.Units.Defs |
| B032 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:306 | `Units.val_pow_eq_pow_val` | THEOREM_READER_CONFIRMED | Units.val_pow_eq_pow_val; theorem; Mathlib.Algebra.Group.Units.Defs |
| B033 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:306 | `coe_expUnit` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.coe_expUnit; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B034 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:306 | `Nat.cast_pow` | THEOREM_READER_CONFIRMED | Nat.cast_pow; theorem; Mathlib.Data.Nat.Cast.Basic |
| B035 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:307 | `Nat.cast_pow` | THEOREM_READER_CONFIRMED | Nat.cast_pow; theorem; Mathlib.Data.Nat.Cast.Basic |
| B036 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:307 | `ZMod.natCast_mod` | THEOREM_READER_CONFIRMED | ZMod.natCast_mod; theorem; Mathlib.Data.ZMod.Basic |
| B037 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:307 | `h1` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B038 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:307 | `ZMod.natCast_mod` | THEOREM_READER_CONFIRMED | ZMod.natCast_mod; theorem; Mathlib.Data.ZMod.Basic |
| B039 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:309 | `orderOf_expUnit` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.orderOf_expUnit; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B040 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:415 | `dlProb` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B041 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:416 | `uexp_def` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.uexp_def; theorem; TCSlib.Cryptography.Foundations.Probability |
| B042 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:422 | `dlProb` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B043 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:432 | `uprob_false` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.uprob_false; theorem; TCSlib.Cryptography.Foundations.Probability |
| B044 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:442 | `abs_zero` | THEOREM_READER_CONFIRMED | abs_zero; theorem; Mathlib.Algebra.Order.Group.Unbundled.Abs |
| B045 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:460 | `dlP` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.dlP; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B046 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:460 | `dlDefaultIndex` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.dlDefaultIndex; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B047 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:460 | `listToNat_natToList` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.listToNat_natToList; theorem; TCSlib.Cryptography.Candidates.Arithmetic |
| B048 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:462 | `dlM` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.dlM; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B049 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:462 | `dlDefaultIndex` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.dlDefaultIndex; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B050 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:462 | `listToNat_natToList` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.listToNat_natToList; theorem; TCSlib.Cryptography.Candidates.Arithmetic |
| B051 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:464 | `dlG` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.dlG; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B052 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:464 | `dlDefaultIndex` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.dlDefaultIndex; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B053 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:464 | `listToNat_natToList` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.listToNat_natToList; theorem; TCSlib.Cryptography.Candidates.Arithmetic |
| B054 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:466 | `h3` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B055 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:467 | `h2` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B056 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:468 | `h2` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B057 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:468 | `h3` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B058 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:469 | `hg` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B059 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:470 | `hg` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B060 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:470 | `h3` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B061 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:471 | `hg` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B062 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:471 | `h2` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B063 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:471 | `h3` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B064 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:493 | `Function.comp_apply` | THEOREM_READER_CONFIRMED | Function.comp_apply; theorem; Init.Core |
| B065 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:493 | `pairFstD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairFstD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B066 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:493 | `pairSndD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairSndD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B067 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:502 | `expGenFun` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expGenFun; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B068 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:502 | `decide_eq_true_eq` | THEOREM_READER_CONFIRMED | decide_eq_true_eq; theorem; Init.SimpLemmas |
| B069 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:513 | `expGen` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expGen; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B070 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:520 | `NUPPT.coinLen_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.coinLen_eq; theorem; TCSlib.Complexity.Randomized.PPT |
| B071 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:520 | `NUPPT.coinLen_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.coinLen_eq; theorem; TCSlib.Complexity.Randomized.PPT |
| B072 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:520 | `expGen_coins` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expGen_coins; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B073 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:558 | `NUPPT.runAt_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.runAt_eq; theorem; TCSlib.Complexity.Randomized.PPT |
| B074 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:558 | `NUPPT.runAt_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.runAt_eq; theorem; TCSlib.Complexity.Randomized.PPT |
| B075 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:558 | `expGen_coinsEquiv_ofFn` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expGen_coinsEquiv_ofFn; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B076 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:558 | `NUPPT.Uniform.runAtL_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.Uniform.runAtL_eq; theorem; TCSlib.Complexity.Randomized.NonUniform |
| B077 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:559 | `expGen` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expGen; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B078 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:560 | `NUPPT.runAtL_ofPolyTimeUniform` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.runAtL_ofPolyTimeUniform; theorem; TCSlib.Complexity.Randomized.PPT |
| B079 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:561 | `expGenFun` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expGenFun; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B080 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:561 | `NUPPT.inParam_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.inParam_eq; theorem; TCSlib.Complexity.Randomized.Closure |
| B081 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:561 | `NUPPT.inCoins_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.inCoins_eq; theorem; TCSlib.Complexity.Randomized.Closure |
| B082 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:561 | `NUPPT.advInput_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.advInput_eq; theorem; TCSlib.Complexity.Randomized.PPT |
| B083 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:561 | `NUPPT.layout_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.layout_eq; theorem; TCSlib.Complexity.Randomized.Closure |
| B084 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:562 | `pairFstD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairFstD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B085 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:562 | `pairSndD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairSndD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B086 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:562 | `List.length_replicate` | THEOREM_READER_CONFIRMED | List.length_replicate; theorem; Init.Data.List.Basic |
| B087 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:579 | `rejectBlocksL_eq` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.rejectBlocksL_eq; theorem; TCSlib.Cryptography.Candidates.Concrete |
| B088 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:585 | `sampleBelowL` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.sampleBelowL; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B089 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:586 | `List.findSome?_eq_some_iff` | THEOREM_READER_CONFIRMED | List.findSome?_eq_some_iff; theorem; Init.Data.List.Find |
| B090 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:589 | `Option.some.injEq` | THEOREM_READER_CONFIRMED | Option.some.injEq; theorem; Init.Core |
| B091 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:627 | `uprob_comp_equiv` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.uprob_comp_equiv; theorem; TCSlib.Cryptography.Foundations.Probability |
| B092 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:628 | `bitsEquiv_val` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.bitsEquiv_val; theorem; TCSlib.Cryptography.Asymptotic.Sampling |
| B093 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:630 | `hacc` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B094 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:632 | `uprob_rejectionSample_none` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.uprob_rejectionSample_none; theorem; TCSlib.Cryptography.Asymptotic.Sampling |
| B095 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:634 | `sampleBelowL_eq_rejectBlocksL` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B096 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:660 | `dla_belowAcc` | OWN_DEFINITION_BODY_ALLOWED | _private.TCSlib.Cryptography.Candidates.DiscreteLog.0.TCSlib.Cryptography.Candidates.dla_belowAcc; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B097 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:660 | `pairFstD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairFstD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B098 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:660 | `pairSndD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairSndD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B099 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:660 | `decide_not` | THEOREM_READER_CONFIRMED | decide_not; theorem; Init.SimpLemmas |
| B100 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:660 | `decide_eq_decide` | THEOREM_READER_CONFIRMED | decide_eq_decide; theorem; Init.PropLemmas |
| B101 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:661 | `Nat.not_le` | THEOREM_READER_CONFIRMED | Nat.not_le; theorem; Init.Data.Nat.Basic |
| B102 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:699 | `Function.comp_apply` | THEOREM_READER_CONFIRMED | Function.comp_apply; theorem; Init.Core |
| B103 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:699 | `pairFstD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairFstD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B104 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:699 | `pairSndD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairSndD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B105 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:699 | `PolyExpr.eval_var` | THEOREM_READER_CONFIRMED | Complexity.PolyExpr.eval_var; theorem; TCSlib.Complexity.Randomized.PolyExpr |
| B106 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:700 | `subStr_pairEncode` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.subStr_pairEncode; theorem; TCSlib.Cryptography.Candidates.Arithmetic |
| B107 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:700 | `Nat.sub_self` | THEOREM_READER_CONFIRMED | Nat.sub_self; theorem; Init.Data.Nat.Basic |
| B108 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:701 | `natToList_zero_append_drop` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.natToList_zero_append_drop; theorem; TCSlib.Cryptography.Candidates.Arithmetic |
| B109 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:702 | `expSampleRaw` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expSampleRaw; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B110 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:702 | `dlW` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.dlW; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B111 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:704 | `dlM_eq` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.dlM_eq; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B112 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:704 | `length_sizeStr` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.length_sizeStr; theorem; TCSlib.Cryptography.Candidates.Arithmetic |
| B113 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:704 | `sampleBelowL_eq_rejectBlocksL` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B114 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:705 | `show` | INLINE_LOCAL_PROOF_CONFIRMED | Source-local proof/syntax |
| B115 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:710 | `he` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B116 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:710 | `List.tail_nil` | THEOREM_READER_CONFIRMED | List.tail_nil; theorem; Init.Data.List.Basic |
| B117 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:710 | `listToNat_nil` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.NumberTheory.listToNat_nil; theorem; TCSlib.Cryptography.NumberTheory.Primality |
| B118 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:723 | `NUPPT.runAt_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.runAt_eq; theorem; TCSlib.Complexity.Randomized.PPT |
| B119 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:724 | `expSampler` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expSampler; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B120 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:725 | `NUPPT.runAtL_ofPolyTimeUniform` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.runAtL_ofPolyTimeUniform; theorem; TCSlib.Complexity.Randomized.PPT |
| B121 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:726 | `expSampleRaw` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expSampleRaw; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B122 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:726 | `NUPPT.inArg_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.inArg_eq; theorem; TCSlib.Complexity.Randomized.Closure |
| B123 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:726 | `NUPPT.inParam_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.inParam_eq; theorem; TCSlib.Complexity.Randomized.Closure |
| B124 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:726 | `NUPPT.inCoins_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.inCoins_eq; theorem; TCSlib.Complexity.Randomized.Closure |
| B125 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:726 | `NUPPT.advInput_eq` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.advInput_eq; theorem; TCSlib.Complexity.Randomized.PPT |
| B126 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:746 | `expGen_runAt` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expGen_runAt; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B127 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:748 | `pairFstD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairFstD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B128 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:750 | `pairFstD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairFstD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B129 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:753 | `expSampler_runAt` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expSampler_runAt; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B130 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:758 | `hvdef` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B131 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:758 | `hs` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B132 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:758 | `Option.getD_none` | THEOREM_READER_CONFIRMED | Option.getD_none; theorem; Init.Data.Option.Basic |
| B133 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:760 | `hvdef` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B134 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:760 | `hs` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B135 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:760 | `Option.getD_some` | THEOREM_READER_CONFIRMED | Option.getD_some; theorem; Init.Data.Option.Basic |
| B136 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:765 | `expEnc_eq` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expEnc_eq; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B137 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:765 | `ZMod.val_natCast` | THEOREM_READER_CONFIRMED | ZMod.val_natCast; theorem; Mathlib.Data.ZMod.Basic |
| B138 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:765 | `Nat.mod_eq_of_lt` | THEOREM_READER_CONFIRMED | Nat.mod_eq_of_lt; theorem; Init.Data.Nat.Div.Basic |
| B139 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:767 | `henc` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B140 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:767 | `expDec_expEnc` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expDec_expEnc; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B141 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:768 | `henc` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B142 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:768 | `expEval_spec` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expEval_spec; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B143 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:879 | `Collection.index_eq` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Collection.index_eq; theorem; TCSlib.Cryptography.Asymptotic.Collections |
| B144 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:880 | `if_pos` | THEOREM_READER_CONFIRMED | if_pos; theorem; Init.Core |
| B145 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:880 | `pairFstD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairFstD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B146 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:887 | `Collection.index_eq` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Collection.index_eq; theorem; TCSlib.Cryptography.Asymptotic.Collections |
| B147 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:889 | `if_neg` | THEOREM_READER_CONFIRMED | if_neg; theorem; Init.Core |
| B148 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:889 | `pairFstD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairFstD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B149 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:918 | `expSampler` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expSampler; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B150 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:921 | `PolyExpr.eval_mul` | THEOREM_READER_CONFIRMED | Complexity.PolyExpr.eval_mul; theorem; TCSlib.Complexity.Randomized.PolyExpr |
| B151 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:921 | `PolyExpr.eval_var` | THEOREM_READER_CONFIRMED | Complexity.PolyExpr.eval_var; theorem; TCSlib.Complexity.Randomized.PolyExpr |
| B152 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:926 | `NUPPT.coinsEquivPoly_ofFn` | THEOREM_READER_CONFIRMED | Complexity.NUPPT.coinsEquivPoly_ofFn; theorem; TCSlib.Complexity.Randomized.PPT |
| B153 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:935 | `ZMod.val_natCast` | THEOREM_READER_CONFIRMED | ZMod.val_natCast; theorem; Mathlib.Data.ZMod.Basic |
| B154 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:935 | `Nat.mod_eq_of_lt` | THEOREM_READER_CONFIRMED | Nat.mod_eq_of_lt; theorem; Init.Data.Nat.Div.Basic |
| B155 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:942 | `hofn` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B156 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:942 | `expSampler_runAt` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expSampler_runAt; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B157 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:946 | `expEnc_eq` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expEnc_eq; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B158 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:946 | `expDec_expEnc` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expDec_expEnc; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B159 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:947 | `hX` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B160 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:947 | `hY` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B161 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:971 | `if_neg` | THEOREM_READER_CONFIRMED | if_neg; theorem; Init.Core |
| B162 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:971 | `one_div` | THEOREM_READER_CONFIRMED | one_div; theorem; Mathlib.Algebra.Group.Defs |
| B163 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:972 | `Collection.sampleClose_iff` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Collection.sampleClose_iff; theorem; TCSlib.Cryptography.Asymptotic.Collections |
| B164 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:975 | `if_pos` | THEOREM_READER_CONFIRMED | if_pos; theorem; Init.Core |
| B165 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:977 | `if_neg` | THEOREM_READER_CONFIRMED | if_neg; theorem; Init.Core |
| B166 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:985 | `expCollection_sample` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expCollection_sample; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B167 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:986 | `expCollection_decD` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expCollection_decD; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B168 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:994 | `Option.map_some` | THEOREM_READER_CONFIRMED | Option.map_some; theorem; Init.Data.Option.Basic |
| B169 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:994 | `Equiv.symm_apply_apply` | THEOREM_READER_CONFIRMED | Equiv.symm_apply_apply; theorem; Mathlib.Logic.Equiv.Defs |
| B170 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:995 | `hY` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B171 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1006 | `expDec` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Candidates.expDec; def; TCSlib.Cryptography.Candidates.DiscreteLog |
| B172 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1009 | `hw` | LOCAL_PROOF_BINDING_CONFIRMED | Source-local proof/syntax |
| B173 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1010 | `decodeFin_eq` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.decodeFin_eq; theorem; TCSlib.Cryptography.Asymptotic.Adversary |
| B174 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1010 | `dif_pos` | THEOREM_READER_CONFIRMED | dif_pos; theorem; Init.Core |
| B175 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1012 | `bitsToNat_eq_listToNat` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.NumberTheory.bitsToNat_eq_listToNat; theorem; TCSlib.Cryptography.NumberTheory.Primality |
| B176 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1012 | `List.ofFn_congr` | THEOREM_READER_CONFIRMED | List.ofFn_congr; theorem; Mathlib.Data.List.OfFn |
| B177 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1012 | `List.ofFn_get` | THEOREM_READER_CONFIRMED | List.ofFn_get; theorem; Mathlib.Data.List.OfFn |
| B178 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1012 | `Option.some.inj` | THEOREM_READER_CONFIRMED | Option.some.inj; theorem; Init.Core |
| B179 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1013 | `ZMod.val_natCast` | THEOREM_READER_CONFIRMED | ZMod.val_natCast; theorem; Mathlib.Data.ZMod.Basic |
| B180 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1013 | `Nat.mod_eq_of_lt` | THEOREM_READER_CONFIRMED | Nat.mod_eq_of_lt; theorem; Init.Data.Nat.Div.Basic |
| B181 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1031 | `Collection.invProbAt_eq` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Collection.invProbAt_eq; theorem; TCSlib.Cryptography.Asymptotic.Collections |
| B182 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1031 | `ExpGroupGen.dlProb_eq` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb_eq; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B183 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1036 | `expCollection_index` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expCollection_index; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B184 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1039 | `uprob_comp_equiv` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.uprob_comp_equiv; theorem; TCSlib.Cryptography.Foundations.Probability |
| B185 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1043 | `Equiv.prodCongr_apply` | THEOREM_READER_CONFIRMED | Equiv.prodCongr_apply; theorem; Mathlib.Logic.Equiv.Prod |
| B186 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1043 | `Prod.map_fst` | THEOREM_READER_CONFIRMED | Prod.map_fst; theorem; Init.Core |
| B187 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1043 | `Prod.map_snd` | THEOREM_READER_CONFIRMED | Prod.map_snd; theorem; Init.Core |
| B188 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1043 | `Equiv.refl_apply` | THEOREM_READER_CONFIRMED | Equiv.refl_apply; theorem; Mathlib.Logic.Equiv.Defs |
| B189 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1044 | `expCollection_f` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expCollection_f; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B190 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1044 | `expCollection_decD` | THEOREM_READER_CONFIRMED | TCSlib.Cryptography.Candidates.expCollection_decD; theorem; TCSlib.Cryptography.Candidates.DiscreteLog |
| B191 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1044 | `Equiv.apply_symm_apply` | THEOREM_READER_CONFIRMED | Equiv.apply_symm_apply; theorem; Mathlib.Logic.Equiv.Defs |
| B192 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1046 | `Equiv.apply_symm_apply` | THEOREM_READER_CONFIRMED | Equiv.apply_symm_apply; theorem; Mathlib.Logic.Equiv.Defs |
| B193 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1060 | `abs_of_nonneg` | THEOREM_READER_CONFIRMED | abs_of_nonneg; theorem; Mathlib.Algebra.Order.Group.Unbundled.Abs |
| B194 | TCSlib/Cryptography/Candidates/DiscreteLog.lean:1060 | `abs_of_nonneg` | THEOREM_READER_CONFIRMED | abs_of_nonneg; theorem; Mathlib.Algebra.Order.Group.Unbundled.Abs |
| B195 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:137 | `Function.comp_apply` | THEOREM_READER_CONFIRMED | Function.comp_apply; theorem; Init.Core |
| B196 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:153 | `dlHashGenFun` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Authentication.dlHashGenFun; def; TCSlib.Cryptography.Hashing.FromDiscreteLog |
| B197 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:153 | `Function.comp_apply` | THEOREM_READER_CONFIRMED | Function.comp_apply; theorem; Init.Core |
| B198 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:153 | `pairFstD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairFstD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B199 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:153 | `pairSndD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairSndD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B200 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:162 | `Function.comp_apply` | THEOREM_READER_CONFIRMED | Function.comp_apply; theorem; Init.Core |
| B201 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:167 | `dlHashPow` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Authentication.dlHashPow; def; TCSlib.Cryptography.Hashing.FromDiscreteLog |
| B202 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:167 | `Function.comp_apply` | THEOREM_READER_CONFIRMED | Function.comp_apply; theorem; Init.Core |
| B203 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:180 | `dlHashMul` | OWN_DEFINITION_BODY_ALLOWED | TCSlib.Cryptography.Authentication.dlHashMul; def; TCSlib.Cryptography.Hashing.FromDiscreteLog |
| B204 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:180 | `Function.comp_apply` | THEOREM_READER_CONFIRMED | Function.comp_apply; theorem; Init.Core |
| B205 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:192 | `Function.comp_apply` | THEOREM_READER_CONFIRMED | Function.comp_apply; theorem; Init.Core |
| B206 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:192 | `pairFstD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairFstD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B207 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:192 | `pairSndD_pairEncode` | THEOREM_READER_CONFIRMED | Complexity.pairSndD_pairEncode; theorem; TCSlib.Complexity.ClassNP.PolyTimePairing |
| B208 | TCSlib/Cryptography/Hashing/FromDiscreteLog.lean:192 | `PolyExpr.eval_var` | THEOREM_READER_CONFIRMED | Complexity.PolyExpr.eval_var; theorem; TCSlib.Complexity.Randomized.PolyExpr |

All native scanner open-row classifications remain preserved in JSON, alongside exact binding evidence or the qualified ZMod theorem correction. No source item received a blanket clearance.
