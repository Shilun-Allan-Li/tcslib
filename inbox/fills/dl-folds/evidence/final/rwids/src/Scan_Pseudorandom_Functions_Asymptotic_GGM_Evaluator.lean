import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Evaluator
open Lean Elab Command

namespace TCSlib.Cryptography
open Complexity Turing Finset

def idsToCheck : List String := ["Bool.false_eq_true","Equiv.symm_apply_apply","FunFamily.ofFn_blocks","Function.iterate_succ_apply","Function.iterate_succ_apply'","List.drop_eq_getElem_cons","List.drop_of_length_le","List.drop_succ_cons","List.drop_zero","List.foldl_cons","List.getElem_drop","List.getElem_ofFn","List.headD_cons","List.length_tail","List.tail_cons","List.take_of_length_le","List.take_succ_cons","Nat.mul_comm","PolyExpr.eval_var","dite_true","drop_ofFn_splitHalves","ggmBits_def","ggmEval","ggmFrom_eq_walk","ggmFrom_of_le","ggmFrom_of_lt","ggmStep","ggmStep_iterate","ggm_apply","h0","h1","hG","hd","hk","hu","if_false","if_neg","if_true","length_pairEncode","pairFstD_pairEncode","pairSel_false","pairSel_true","pairSndD_pairEncode","prefixAt_apply","selHalf","selHalf_ofFn","splitHalves_apply_snd","take_ofFn_castLE","take_ofFn_splitHalves","walk"]
def scannedModule : Name := `TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Evaluator

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

end TCSlib.Cryptography
