import lean_proof.canon.base.UniversalBase
open Lean Elab Command

namespace TCSlib.Cryptography
open Complexity Turing Finset

def idsToCheck : List String := ["Fin.coe_cast","Fintype.card_bool","Fintype.card_fin","Fintype.card_fun","FunFamily.invProbAt_eq_uprob","List.cons_append","List.length_append","List.length_cons","List.length_ofFn","List.length_replicate","List.ofFn_fin_append","List.ofFn_inj","List.take_left'","NUPPT.advInput_eq","NUPPT.coinLen_eq","NUPPT.runAt_eq","Nat.cast_add","Nat.cast_one","Nat.cast_pow","Nat.log_le_self","OneWay.uprob_eq_one_div_card","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_normal","PolyExpr.eval_pow","PolyExpr.eval_subst","PolyExpr.eval_var","abs_of_nonneg","clockedAnswer","clockedAnswer_eq_cons_of_computesInTime","clockedAnswer_eq_false_of_not_computesInTime","code","dif_pos","eval_univOutLen","fUniversalStr","fUniversalStr_ofFn_eq","fUniversal_inLen_eval","h1","hB","hBc","hBrun","hInv","hK","hP","hcd","hcf","hcode","hcoins","hdec","ho'","hofn","hsum","hx'","hy","hy'","hy₀","hα","hφm","id_eq","if_neg","if_pos","length_pairEncode","length_tail_bits","length_univCode","mul_comm","mul_div_cancel₀","ofFn_fUniversal_f","one_mul","padStr_eq","padStr_eq_ofFn_fUniversal_f","pairFstD_pairEncode","pairSndD_pairEncode","pow_mul","pow_one","show","take_append_replicate_of_le","uexp_def","univArg","univArg_append","univCode","univCode_append","univCoeff","universalBlockBound_def","uprob_comp_equiv","uprob_fst","uprob_not","uprob_prod","β","φ"]
def scannedModule : Name := `lean_proof.canon.base.UniversalBase

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
