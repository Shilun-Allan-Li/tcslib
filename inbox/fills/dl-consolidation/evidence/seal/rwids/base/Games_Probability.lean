import TCSlib.Cryptography.Games.Probability
open Lean Elab Command

namespace TCSlib.Cryptography.Games
open Finset TCSlib.InformationTheory
open TCSlib.Cryptography.Games.ProbComp

def idsToCheck : List String := ["Fintype.card_fin","OracleComp.map_eq_bind","OracleComp.pure_bind","OracleComp.query_bind","card_univ","eq_sub_iff_add_eq","expect_add","expect_bind","expect_const","expect_map","expect_pure","expect_query","expect_sampleFin","expect_sum","h","hp","hq","if_false","ih","mul_add","mul_sum","nsmul_eq_mul","prob","prob_eq_expect","sample","sum_add_distrib","sum_const"]
def scannedModule : Name := `TCSlib.Cryptography.Games.Probability

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
