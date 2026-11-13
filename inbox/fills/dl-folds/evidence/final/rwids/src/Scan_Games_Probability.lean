import TCSlib.Cryptography.Games.Probability
open Lean Elab Command

namespace TCSlib.Cryptography.Games
open Finset TCSlib.InformationTheory
open TCSlib.Cryptography.Games.ProbComp

def idsToCheck : List String := ["Equiv.sum_comp","Fintype.card_congr","Fintype.card_fin","Fintype.card_unique","Fintype.sum_prod_type'","Fintype.sum_unique","Function.update_eq_self","Function.update_idem","Function.update_self","OracleComp.map_eq_bind","OracleComp.pure_bind","OracleComp.query_bind","abs_le","card_univ","eq_sub_iff_add_eq","expect_add","expect_bind","expect_const","expect_const_mul","expect_map","expect_pure","expect_query","expect_sample","expect_sampleFin","expect_sample_comm","expect_sample_update","expect_sum","h","hF","hp","hpair","hq","if_false","ih","inv_mul_cancel_left₀","mul_add","mul_sum","neg_one_mul","nsmul_eq_mul","prob","prob_eq_expect","sample","sub_eq_add_neg","sum_add_distrib","sum_comm","sum_const"]
def scannedModule : Name := `TCSlib.Cryptography.Games.Probability

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

end TCSlib.Cryptography.Games
