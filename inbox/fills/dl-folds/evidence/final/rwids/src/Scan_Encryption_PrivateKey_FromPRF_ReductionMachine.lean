import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
open Lean Elab Command

namespace TCSlib.Cryptography.MultiMsg
open Complexity Turing Finset

def idsToCheck : List String := ["Bool.xor_false","Equiv.apply_symm_apply","Fin.coe_castSucc","Fin.val_last","Function.comp_apply","List.append_assoc","List.append_nil","List.concat_eq_append","List.cons_append","List.drop_append","List.drop_left'","List.drop_of_length_le","List.drop_zero","List.flatMap_cons","List.flatMap_def","List.flatMap_map","List.flatMap_nil","List.flatten_cons","List.length_append","List.length_cons","List.length_nil","List.length_ofFn","List.length_replicate","List.map_ofFn","List.nil_append","List.ofFn_fin_append","List.ofFn_succ","List.ofFn_succ'","List.range_succ_eq_map","List.replicate_add","List.replicate_succ","List.take_left'","List.take_of_length_le","List.zipWith_append","List.zipWith_cons_cons","List.zipWith_nil_left","List.zipWith_nil_right","NUPPT.advInput_eq","NUPPT.coinLen_eq","NUPPT.coins_ofPolyTimeUniform","NUPPT.layout_eq","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","NUPPT.toOracleAdversary_eq","Nat.add_sub_cancel","Nat.add_zero","Nat.mul_div_cancel","Nat.sub_self","Nat.sub_zero","Nat.succ_mul","Nat.zero_mul","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","QueryTree.eval_query","QueryTree.eval_ret","add_comm","adviceBound","blockMapFun","buildTree_succ_of_query","buildTree_zero_of_ret","dbl_append","dbl_cons","dbl_nil","decodeFin_ofFn","decodeOracleMove_pairEncode_false","decodeOracleMove_query","decodeOracleMove_ret","dropPolyFun","encodeHist_cons","encodeHist_eq_flatMap","encodeHist_nil","eval_histBlockLen","flatMap_const_replicate","flatMap_const_singleton","flatMap_ofFn","flatMap_range_blocks","h","h0","h1","h2","hB","hBc","hC","hCc","hC₂'","hC₂c","hD₁","hD₁c","hD₁len","hPstr","hans","harg","hbudget","hcoins","hcount","hist","histBlock","histBlockLen","hist_len","hist_succ","hist_top","hlen","hnext","hoffset","hp","hpar","hpoints","hrun","hx","hy","hyw","hρ'","hφ","id_eq","if_neg","if_pos","ih","le_refl","length_dbl","length_flatMap_of_length","length_flatten_of_length","length_histBlock","length_maskBlock","length_maskOf","length_pairEncode","maskBlock","maskOf","pairEncode_eq","pairEncode_eq_dbl","pairFstD_pairEncode","pairFstD_pairFstD_histBlock","pairSndD_pairEncode","postAns","postBudget","postCount","postFun","postFun_layout","postHist","postOffset","postPoints","postQuery","postVerdict","preFun","preFun_encodeHist","show","takePolyFun","take_drop_ofFn_blocks","zipWith_xor_dbl","zipWith_xor_flatten_ofFn","zipWith_xor_ofFn_add","zipWith_xor_replicate_false"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Name :=
    ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!).getD scannedModule
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> (Pure.pure [] : CoreM (List Name))
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

end TCSlib.Cryptography.MultiMsg
