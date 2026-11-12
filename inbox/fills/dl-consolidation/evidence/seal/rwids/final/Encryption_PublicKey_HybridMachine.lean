import TCSlib.Cryptography.Encryption.PublicKey.HybridMachine
open Lean Elab Command

namespace TCSlib.Cryptography
open Complexity Turing
open PrivateKeyScheme (encodeList)

def idsToCheck : List String := ["Equiv.symm_apply_apply","Fin.coe_castLE","Fin.val_mk","Fin.val_succ","Function.comp_apply","List.cons.injEq","List.drop_drop","List.drop_left'","List.drop_take","List.flatMap_append","List.flatMap_cons","List.flatten_cons","List.getElem_append","List.getElem_cons","List.getElem_drop","List.getElem_ofFn","List.getElem_take","List.length_append","List.length_cons","List.length_drop","List.length_nil","List.length_ofFn","List.length_replicate","List.length_take","List.ofFn_fin_append","List.ofFn_succ","List.take_left'","List.take_take","NUPPT.coinLen_eq","NUPPT.runAt_eq","Nat.succ_mul","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","acceptProb_def","blockEncFun_eq","blockEncFun_flatten","blockEncFun_spec","blockList_flatten","blockList_succ","blockList_zero","blockState_eq","coinBlock_drop","coinBlock_eq","coinBlock_ofFn_coinBlocks","coinBlock_take","coinBlocks_apply","dif_neg","dif_pos","encodeList_eq_flatMap","encodeList_ofFn_split","finProdFinEquiv_apply_val","h","hB","hBc","hD₁","hD₁c","hD₂","hD₂c","hEnc.runAtL_eq","hi","hidx","hne","hx","hx'","hybridPre","id_eq","if_false","if_neg","if_true","ih","length_flatten_ofFn","length_pairEncode","ofFn_eq_append_cons","pairEncode_nil_append","pairFstD_pairEncode","pairSndD_pairEncode","show","uprob_comp_equiv","β"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.HybridMachine

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

end TCSlib.Cryptography
