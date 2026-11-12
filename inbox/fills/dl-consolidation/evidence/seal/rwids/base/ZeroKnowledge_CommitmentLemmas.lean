import TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas
open Lean Elab Command

namespace TCSlib.Cryptography.CommitmentLemmas
open Complexity Turing Finset
open TCSlib.Cryptography.CommitmentLemmas.ComLoop

def idsToCheck : List String := ["EnsembleLemmas.acceptProb_coins_equiv","Fin.coe_castLE","Finset.card_univ","Finset.sum_const","Finset.sum_sub_distrib","FunFamily.ofFn_blocks_symm","Function.iterate_succ_apply'","Function.update_of_ne","Function.update_self","List.append_assoc","List.append_nil","List.drop_drop","List.drop_eq_nil_iff","List.drop_eq_nil_of_le","List.flatMap_append","List.flatMap_map","List.flatten_append","List.flatten_cons","List.getD_eq_getElem?_getD","List.getElem_append","List.getElem_cons","List.getElem_ofFn","List.head?_drop","List.headD_eq_head?","List.length_append","List.length_cons","List.length_drop","List.length_flatten","List.length_ofFn","List.length_replicate","List.length_tail","List.range_add","List.sum_ofFn","List.tail_drop","NUPPT.advInput_eq","NUPPT.coinLen_eq","NUPPT.distinguisherL_eq","NUPPT.distinguisher_eq","NUPPT.runAt_eq","Nat.add_mul","Nat.one_mul","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","Strategy.encodeMsgs_cons","abs_div","abs_of_pos","acceptProb_def","acceptProb_eq_uexp_fst","arg","distAdv_def","emit","encodeMsgs_append","h","h2","hB","hB₁","hblock","hc","headD_drop","hm'","hne","hofn","hrun","h₁","h₂","if_false","ih","init","iterate_step","length_pairEncode","loopOut","mul_div_cancel₀","ne_eq","nsmul_eq_mul","ofFn_eq_append_cons","ofFn_update_eq","pairEncode_eq","pairFstD_pairEncode","pairSndD_pairEncode","pairSpliceFun","pairSpliceFun_pairEncode","p₁","p₁_st","p₂","p₂_st","p₃","p₃_st","spliceFun","spliceFun_pairEncode","st","step","sub_div","uexp_def","uprob_prod"]
def scannedModule : Name := `TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas

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

end TCSlib.Cryptography.CommitmentLemmas
