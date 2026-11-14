import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Tools
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.ETTGame
open TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

def idsToCheck : List String := ["Function.update_eq_self","Function.update_idem","Function.update_of_ne","Function.update_self","List.map_cons","List.mem_cons","OracleComp.bind_assoc","OracleComp.pure_bind","expect_bind","expect_expect_sample","expect_pure","freshImpl_apply","h","hT","ih","not_or","ovr_cons","ovr_of_not_mem","ovr_update","simulate_pure","simulate_query","tapeImpl_apply"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Tools

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

end TCSlib.Cryptography.Composability.ETTGame
