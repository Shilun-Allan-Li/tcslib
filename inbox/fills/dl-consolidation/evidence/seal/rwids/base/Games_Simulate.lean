import TCSlib.Cryptography.Games.Simulate
open Lean Elab Command

namespace TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.QueryImpl

def idsToCheck : List String := ["Nat.add_sub_cancel'","OracleComp.bind_assoc","OracleComp.bind_pure","OracleComp.call_bind","OracleComp.pure_bind","OracleComp.query_bind","QueryImpl.comp","QueryImpl.withLog","ih","ofComp_apply","passthrough","simulate_bind","simulate_pure","simulate_query"]
def scannedModule : Name := `TCSlib.Cryptography.Games.Simulate

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
