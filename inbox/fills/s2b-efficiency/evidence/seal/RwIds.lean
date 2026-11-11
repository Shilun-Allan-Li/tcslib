import TCSlib.Cryptography.Games.Efficiency
open Lean Elab Command

/-! Explicit readings of the efficiency fill: every identifier that the new code passes to `rw`,
`rwa`, `simp`, `simp only`, `simp_rw`, `dsimp` or `unfold` (collected from the added lines of the
patch series), resolved in the files' namespace with their `open`s. A definition may be passed
only when it is the scanned file's own; every other name must be a theorem or a local
hypothesis. -/

namespace TCSlib.Cryptography.Games.EffFill
open Complexity Turing

def idsToCheck : List String := ["Bool.and_eq_true","Bool.and_true","Bool.or_eq_true","Bool.or_true","Bool.true_or","EffFill.fixLen_nil","EffFill.iCall_eq","EffFill.iFinish_eq","EffFill.iImpl_apply","EffFill.iRaw_spec","EffFill.iX_eq","EffFill.logHist_eq","EffFill.ofFn_getD_decodeFin","Fin.fin_one_eq_zero","Fin.val_succ","Fin.val_zero","Function.comp_apply","Function.iterate_succ_apply'","GGMRed.pairEncode_append_right","GGMRed.stateLoopFun_eval","InteractiveHandler.advInput_eq","InteractiveHandler.call_eq","InteractiveHandler.finInput_eq","InteractiveHandler.finish_eq","InteractiveHandler.impl_apply","InteractiveHandler.input_eq","List.append_assoc","List.append_nil","List.cons_append","List.drop_left'","List.drop_one","List.flatMap_cons","List.flatMap_eq_nil_iff","List.flatMap_map","List.length_append","List.length_cons","List.length_map","List.length_nil","List.length_ofFn","List.length_replicate","List.length_singleton","List.map_append","List.map_cons","List.map_nil","List.map_singleton","List.nil_append","List.ofFn_add","List.ofFn_congr","List.ofFn_fin_append","List.ofFn_succ","List.ofFn_zero","List.range_succ_eq_map","List.replicate_add","List.replicate_succ","List.replicate_zero","List.singleton_append","List.tail_cons","List.take_left'","MachineCodec.encodeLog_cons","MachineCodec.encodeLog_nil","NUPPT.advInput_eq","NUPPT.coinLen_eq","NUPPT.coins_ofPolyTime","NUPPT.inAdvice_layout","NUPPT.inArg_layout","NUPPT.inCoins_layout","NUPPT.inParam_layout","NUPPT.layout_eq","NUPPT.runAtL_eq_output_layout","NUPPT.runAtL_ofPolyTime","NUPPT.runAt_coinsCongr","NUPPT.runAt_eq","NUPPT.toCompOn_eq","NUPPT.toComp_eq","NUPPT.toOracleAdversary_eq","Nat.add_mul","Nat.add_sub_cancel","Nat.add_zero","Nat.le_zero.1","Nat.mul_add","Nat.mul_one","Nat.one_mul","Nat.sub_one_mul","Nat.succ_le_iff","Nat.zero_add","Option.getD_none","Option.getD_some","OracleComp.bind_assoc","OracleComp.pure_bind","OracleComp.query_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","PolyHandler.advInput_eq","PolyHandler.answer_of_pairDecode_eq_none","PolyHandler.answer_of_pairDecode_eq_some","PolyHandler.input_eq","PolyHandler.result_eq","StateLoop.orbit_succ","StateLoop.orbit_zero","actAcc_eq","actLoop_eq","actStep_eq","advNext_eq","bitCodec_decodeMove","bitCodec_encodeEntry","bitCodec_timeout","bridgePost_eq","bridgePre_eq","buildComp_succ_of_query","buildComp_succ_of_ret","buildComp_zero_of_query","buildComp_zero_of_ret","buildTree_succ_of_query","buildTree_succ_of_ret","buildTree_zero_of_query","buildTree_zero_of_ret","canonFun","canonQ_eq","canonR_eq","canonWord_eq","canonWord_eq_ite","decide_eq_false","decide_eq_true","decide_eq_true_eq","decide_true","decodeBitMove_of_not_canonical","decodeBitMove_query","decodeBitMove_ret","decodeFin_eq","decodeFin_eq_some_iff","decodeOracleMove_pairEncode_false_of_length_ne","decodeOracleMove_true_two","dif_pos","e","encodeBitMove_query","encodeBitMove_ret","encodeHist_cons","encodeHist_nil","encodeLog_append_single","encodeLog_bitCodec","entryPoly_eq","eq_pairEncode_of_pairDecode","fixLen_eq","fixLen_of_length_eq","fixLen_of_length_ne","gB","gB_iSt","gC","gC_iSt","gCur","gCur_iSt","gLc","gLc_iSt","gLin","gLin_iSt","gO","gO_iSt","gPh","gPh_iSt","gS","gS_iSt","h","h'","h0","hA'","hAct_eq","hAct_of_query","hAct_of_ret","hAct_of_timeout","hB","hB'","hBc","hBound_eq","hCtx_eq","hMove_eq","hMove_state","hNext_eq","hO","hRes_eq","hRounds_eq","hS","hStart_eq","hState_eq","hT","hX","hXctx","hXu","ha","hact","hcodec","hf","hfin","hh","himpl","hiw","hlen","hm","hnext","hofFn","horb","hq","hr","hraw","hs","hstart","hx","hxe","hφ","i.isLt","iAct_eq","iAdvAct_eq","iAdvMove_eq","iAdvMove_iSt","iAdvMove_iX","iAnsLen_eq","iAsk_eq","iBound_eq","iCallAct_eq","iCallEnd_eq","iCallEnd_iSt","iCallMove_eq","iCallMove_iSt","iCallMove_iX","iCallNext_eq","iCall_eq_buildComp","iCtx_eq","iCurBound_eq","iFinAct_eq","iFinMove_eq","iFinMove_iSt","iFinMove_iX","iFinNext_eq","iFinish_eq_buildComp","iFixBound_eq","iImpl_apply","iInv_stop","iNext_eq","iOuter_eq","iRaw_eq","iRounds_eq","iSt_eq","iStart_eq","iTree_eq","iX_ctx","iX_eq","iX_inAdvice","iX_inCoins","iX_inParam","iX_outer","id_eq","if_neg","if_pos","if_true","ih","length_pairEncode","logHist_eq","not_or","ofFn_take_drop_add","ofFn_zeroBits","pairFstD_of_pairDecode_eq_none","pairFstD_pairEncode","pairSndD_of_pairDecode_eq_none","pairSndD_pairEncode","relabelEmit_eq","relabelN_encodeHist","relabelN_eq","relabelN_nil","relabelN_succ","relabel_eq","replaysFrom_pure_iff","replaysFrom_query_iff","runsTo_stop","seedIn_eq","selLen_eq","sides.","simulate_pure","simulate_query","sumPoly_succ","the","toCompOn_eq_advNext","two","zeroBits_apply"]

#eval show CommandElabM Unit from do
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (do
      let r ← realizeGlobalConstWithInfos (mkIdent n)
      return r) <|> pure []
    let env ← getEnv
    let modOf (c : Name) : String :=
      ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!.toString).getD "?"
    if cands.isEmpty then IO.println s!"{s}: (local hypothesis)"
    else for c in cands do
      let k := match env.find? c with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) => "DEF"
        | some _ => "other"
        | none => "?"
      IO.println s!"{s}: {c}: {k} ({modOf c})"

end TCSlib.Cryptography.Games.EffFill
