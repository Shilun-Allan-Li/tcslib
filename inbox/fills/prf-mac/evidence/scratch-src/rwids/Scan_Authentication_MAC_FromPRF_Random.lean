import TCSlib.Cryptography.Authentication.MAC.FromPRF.Random
open Lean Elab Command

namespace TCSlib.Cryptography.Authentication.PRFMAC
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp
open TCSlib.Cryptography.Composability.ETTGame (ovr ovr_nil ovr_of_mem ovr_of_not_mem expect_sample_ovr)

def idsToCheck : List String := ["Fintype.card_bool","Fintype.card_fin","Fintype.card_fun","List.length_singleton","List.map_cons","List.map_nil","List.mem_cons","List.mem_singleton","OracleComp.pure_bind","QueryImpl.withLog_apply","e","expect_const","expect_pure","expect_sample_coord","fnImpl_apply","h0","hF","if_neg","if_pos","one_div","ovr_nil","ovr_of_not_mem","queried_append","simulate_pure","simulate_query"]
def scannedModule : Name := `TCSlib.Cryptography.Authentication.MAC.FromPRF.Random

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

end TCSlib.Cryptography.Authentication.PRFMAC
