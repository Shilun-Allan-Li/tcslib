import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
open Lean Elab Command

namespace TCSlib.Cryptography.GGMRed
open Complexity Turing Finset QueryTree

def idsToCheck : List String := ["Bool.and_eq_true","Bool.false_eq_true","Bool.not_eq_false'","Bool.or_eq_false_iff","Equiv.apply_symm_apply","Equiv.symm_apply_apply","Equiv.trans_apply","Function.iterate_succ_apply","Function.iterate_succ_apply'","Function.iterate_zero","IsQ","List.drop_eq_getElem_cons","List.getElem?_eq_getElem","List.getElem_ofFn","List.headD_cons","List.idxOf_append_of_notMem","List.idxOf_cons_self","List.length_append","List.length_replicate","List.length_singleton","List.replicate_succ","NUPPT.coinLen_eq","NUPPT.coinsEquivPoly_ofFn","NUPPT.distinguisherL_eq","NUPPT.distinguisher_eq","NUPPT.layout_eq","NUPPT.runAtL_ofPolyTime","NUPPT.runAt_eq","Nat.add_sub_cancel'","Nat.add_zero","Nat.sub_eq_zero_of_le","Nat.zero_add","Option.eq_none_iff_forall_ne_some","Option.getD_some","Option.map_some","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","StateLoop.orbit_succ","Turing.pairEncode_ne_nil","acc_def","acc_eq","advD_def","advD_eq","advPoly","adviceOf","ansMap","ans_def","bound_def","buildTreeQ_succ","buildTreeQ_zero","chal_def","chal_eq","challengeStream_def","cnt'_def","cnt_def","cnt_eq","coinPoly_eq","coinStr","coinsAll_def","coinsAll_eq","coinsD_def","coinsD_eq","coinsRest_def","coinsRest_eq","concrete","concrete_succ","concrete_zero","decide_eq_false_iff_not","decide_eq_true_eq","decide_not","decodeFin_eq_some_iff","drop_take_ofFn_blocks","encState","eqJ_def","exists_queryOf_iff","extendStream_def","fresh_def","fresh_eq","ggmEval_ofFn_walk","ggmFrom_eq_walk","ggmRedMachine","ggmRedMachine_coinsEquiv","h","hG","hQ","hans","hbit","hc","hconc","hd","hdist","heq","hidx","hist'_def","histEnc_append_single","hist_def","hist_eq","hk","hlook","hlt","hmem","hnf","hnone","horbN","hpfx","hpure","hquery","hraw","hrest","hrhs","hstream","hsum","hv","hx","hx'","id_eq","if_false","if_neg","if_pos","if_true","ih","inS_def","inX_def","isQ_def","lab_def","length_encState","length_histEnc","length_pairEncode","length_tblEnc_tblOf","look_def","lookup_tblOf","ltJ_def","min_eq_left","move_def","move_eq","mul1_def","mul1_length","mul2_def","mul2_length","notFound_def","not_le","noteQuery_of_mem","noteQuery_of_not_mem","ofFn_padFin_of_length","ofFn_prefixAt","orbit_eq_encState","out_def","out_eq","padFin_def","pairFstD_eq","pairSndD_eq","pairSndD_of_queryOf","pairs_def","pairs_eq","paramU_def","paramU_eq","pfx_def","pureAt_succ","pureStep","queryOf_eq","queryOf_eq_some_iff","query_def","rawFun_def","rawFun_rawInput","rawInput","rnd_def","rnd_eq","runAt_ggmRedMachine","seeds_def","seeds_eq","selHalf_ofFn","show","stateLoopFun_eval","step_def","step_eq","stream","tbl'_def","tblEnc_append_single","tblOf_append_single","tbl_def","tbl_eq","un2_def","un2_length","unI_def","unI_eq","unJ_def","unJ_eq","unQ_def","valStr","vstr_def","zero_add"]
def scannedModule : Name := `TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Name :=
    ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!).getD scannedModule
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> pure []
    if cands.isEmpty then IO.println s!"{s}\t-\tlocal/unresolved\t-"
    else for c in cands do
      let k := match env.find? c with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) => "DEF"
        | some (.opaqueInfo _) => "opaque"
        | some (.inductInfo _) => "inductive"
        | some (.ctorInfo _) => "ctor"
        | some _ => "other"
        | none => "?"
      let m := modOf c
      let tag := if k == "DEF" then
          (if m == scannedModule then "own-def" else if (`TCSlib).isPrefixOf m then "FOREIGN-TCSLIB-DEF" else "core/mathlib-def")
        else k
      IO.println s!"{s}\t{c}\t{tag}\t{m}"

end TCSlib.Cryptography.GGMRed
