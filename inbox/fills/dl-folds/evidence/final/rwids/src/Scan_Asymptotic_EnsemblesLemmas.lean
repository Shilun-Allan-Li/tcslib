import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
open Lean Elab Command

namespace TCSlib.Cryptography.EnsembleLemmas
open Complexity Turing Finset
open TCSlib.Cryptography.EnsembleLemmas.CopiesLoop

def idsToCheck : List String := ["CopiesLoop.loopOut_st","CopiesLoop.st","Equiv.apply_symm_apply","Equiv.prodCongr_apply","Equiv.refl_apply","Equiv.symm_apply_eq","Equiv.trans_apply","Fin.tail_cons","Fin.tail_def","FunFamily.blocks_symm_apply","FunFamily.ofFn_blocks","Function.comp_apply","Function.iterate_succ_apply'","List.drop_drop","List.drop_left'","List.flatMap_append","List.flatMap_def","List.flatMap_singleton","List.getD_eq_getElem?_getD","List.getElem?_eq_getElem","List.getElem?_eq_none_iff.2","List.getElem_append","List.getElem_ofFn","List.getElem_take","List.length_append","List.length_cons","List.length_replicate","List.map_coe_finRange","List.map_map","List.ofFn_eq_map","List.ofFn_fin_append","List.ofFn_mul","List.range_add","List.range_succ","List.replicate_succ","List.take_left'","NUPPT.advInput_eq","NUPPT.coinLen_eq","NUPPT.coinsEquivPoly_ofFn","NUPPT.distinguisherL_eq","NUPPT.distinguisher_eq","NUPPT.inAdvice_eq","NUPPT.inArg_eq","NUPPT.inCoins_eq","NUPPT.inParam_eq","NUPPT.layout_eq","NUPPT.runAtL_eq","NUPPT.runAtL_ofPolyTime","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","Nat.succ_mul","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_subst","PolyExpr.eval_var","Prod.map_fst","Prod.map_snd","abs_mul","abs_nonpos_iff","abs_of_nonneg","abs_zero","acceptProb_bind","acceptProb_coins_equiv","acceptProb_coins_fst","acceptProb_def","acceptProb_not","add_zero","blocks_eq","blocks_symm_apply","consSplit","copiesInit","copiesSampler","copies_def","drop_ofFn_coinsEquiv","emit","emit_st","finProdFinEquiv_apply_val","finProdFinEquiv_symm_apply","finProdFinEquiv_symm_mk","h","h1","h2","hA","hAc","hB","hBc","hC","hCc","hD₂","hD₂c","hF","hX","hX'","hY","hY'","hofn","id_eq","if_neg","if_pos","ih","iterate_step","le_refl","length_padL","length_pairEncode","loopOut","ofFn_coinsEquiv","padFin_def","padL","padL_eq","pairFstD_eq","pairFstD_pairEncode","pairSndD_eq","pairSndD_pairEncode","p₁","p₂","p₃","p₄","p₅","p₆","seedEquiv","seedEquivPoly","st","step","sub_eq_zero","sub_self","take_drop_ofFn_blocks","take_flatMap_range","take_ofFn_coinsEquiv","this","uprob_const","uprob_false","uprob_not","uprob_true"]
def scannedModule : Name := `TCSlib.Cryptography.Asymptotic.EnsemblesLemmas

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

end TCSlib.Cryptography.EnsembleLemmas
