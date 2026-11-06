import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol
open Lean Elab Command
open TCSlib.Cryptography Complexity Turing TCSlib.Cryptography.EncodingMachines TCSlib.Cryptography.ColMachines TCSlib.Cryptography.ColRep
def idsToCheck : List String := ["Bool.and_eq_false_iff","Bool.and_eq_true","Bool.eq_iff_iff","Bool.not_eq_false","Bool.or_eq_false_iff","Bool.or_false","Bool.true_and","Bool.xor_self","ColMachines.edgeCount_eq","ColRep.drop_take_ofFn_blockRead","Fin.coe_castLE","List.cons.injEq","List.getD_append","List.getD_eq_getElem","List.getElem_drop","List.getElem_ofFn","List.getElem_take","List.length_append","List.length_cons","List.length_drop","List.length_ofFn","List.length_singleton","List.length_take","Nat.add_mul_div_left","Nat.add_mul_mod_self_left","Nat.div_eq_of_lt","Nat.div_one","Nat.mod_eq_of_lt","Nat.mul_zero","Nat.sqrt_eq","OneWay.uprob_congr","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_normal","PolyExpr.eval_var","ProperColoring_iff","Protocol.withV_self","R3COL_iff","Strategy.coinLen_eq","and_assoc","and_true","badEntry","badVertex","blockRead_eq","chView_congr","chView_succ","colCoinSlice_eq","colIterations_eq","colRep_outV","colRep_proverRep_next","colRep_verifierRep_next_end","colWellFormed_encGraph","decColoring_encColoring","decColoring_val","decGraph_apply","decGraph_fst","decide_eq_false_iff_not","decide_eq_true_eq","decide_eq_true_iff","dif_pos","divNum_eq","edgeIdxOfMsg_edgeMsg","encGraph_decGraph_eq_take","enc_iff","exec_zero","finProdFinEquiv_apply_val","firstIdx_eq_iff","h","h0","h1","h2","hG","hK","hPi","hb","hbit0","hbit1","hcoin","hcom","hcur","hdiv","he","heq","hlast","hlen","hlv","hm","hmid","hmod","hodd","hopn","hpre","hsqrt","hstep","huv","hwf","hx","hxG","hΦ","if_neg","if_pos","length_chView","length_encColoring","length_encGraph","modNum_eq","moverIsV_false","ne_eq","not_not","one_div","one_mul","pairFstD_pairEncode","pairSndD_pairEncode","proper_iff","r3colTest_eq","scanTest","scanTest_iff","sq","this","true_and","uprob_false","uprob_not","wf_iff","zero_add"]
#eval show CommandElabM Unit from do
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (do
      let r ← realizeGlobalConstWithInfos (mkIdent n)
      return r) <|> pure []
    let env ← getEnv
    let kinds := cands.map fun c => match env.find? c with
      | some (.thmInfo _) => s!"{c}: theorem"
      | some (.defnInfo _) => s!"{c}: DEF"
      | some _ => s!"{c}: other"
      | none => s!"{c}: ?"
    if cands.isEmpty then IO.println s!"{s}: (local hypothesis or private)"
    else for k in kinds do IO.println k
