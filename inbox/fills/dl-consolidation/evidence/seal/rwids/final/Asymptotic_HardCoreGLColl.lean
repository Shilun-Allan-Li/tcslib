import TCSlib.Cryptography.Asymptotic.HardCoreGLColl
open Lean Elab Command

namespace TCSlib.Cryptography
open Complexity Turing Finset

def idsToCheck : List String := ["Bool.xor_self","Equiv.coe_refl","Equiv.prodAssoc_apply","Equiv.prodCongr_apply","Equiv.trans_apply","F.decD_encD","Fin.coe_cast","List.getD_eq_getElem?_getD","List.getElem?_eq_getElem","List.getElem?_eq_none","List.getElem_append_left","List.getElem_append_right","List.getElem_ofFn","List.getElem_take","List.getElem_zipWith","List.length_ofFn","NUPPT.coinLen_eq","NUPPT.coins_wrap","NUPPT.distinguisherL_eq","NUPPT.precomp_coinsEquiv_ofFn","NUPPT.runAtL_precomp","NUPPT.runAt_eq","NUPPT.runAt_wrap","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_pow","PolyExpr.eval_var","Prod.map_apply","abs_of_nonneg","coe_finCastEquiv","coins_glMachine","collPre","div_le_div_iff₀","eC","glCollMachine","glCollMachine_runAt","glCollPost","glCollPre","glKc","glKcBound","glMachine_coinsEquiv_symm_ofFn","glMachine_runAt_guessRecover","glPadDecode_pairEncode_ofFn","glPredictorOf_apply","hq","hr'","hrec","hsq","hw","hε","id_eq","inv_mul_eq_div","ipFun_ofFn","ip_cast'","le_div_iff₀","max_eq_left","max_eq_right","ofFn_finCastEquiv","ofFn_padFin_of_length","one_div","one_mul","padFin_def","padToLen","padToLen_pairEncode_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","pow_mul","uexp_def","uprob_comp_equiv","zero_add"]
def scannedModule : Name := `TCSlib.Cryptography.Asymptotic.HardCoreGLColl

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
