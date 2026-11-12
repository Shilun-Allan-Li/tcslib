import TCSlib.Cryptography.Games.Hopping
open Lean Elab Command

namespace TCSlib.Cryptography.Games
open Finset
open TCSlib.Cryptography.Games.ProbComp

def idsToCheck : List String := ["Finset.sum_boole","OracleComp.allOutputs_pure","ProbComp.expect_add","ProbComp.expect_const","ProbComp.expect_const_mul","ProbComp.prob_bind","ProbComp.prob_split","abs_le","and_self","expect_add","expect_bind","expect_const","expect_ite_one_split","expect_pure","expect_query","expect_sample","funext","h","h1","hA","hB","hF","hK","ha","hagree","hsum","hy","if_neg","if_pos","inv_mul_eq_div","prob_bind","prob_eq_expect","prob_eq_one_of_allOutputs","prob_pure","simulate_pure","simulate_query","this.1","zero_add"]
def scannedModule : Name := `TCSlib.Cryptography.Games.Hopping

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

end TCSlib.Cryptography.Games
