import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Games
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.PRFGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

def idsToCheck : List String := ["List.length_ofFn","List.length_zipWith","Nat.min_self","OracleComp.bind_assoc","OracleComp.pure_bind","ctOf_eq","eImpl_challenge_none","eImpl_challenge_some","eImpl_dec","eImpl_enc","expect_bind","expect_pure","fImpl_challenge_none","fImpl_challenge_some","fImpl_dec","fImpl_enc","h","hT","hm","length_pairEncode","simulate_pure","simulate_query"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Games

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

end TCSlib.Cryptography.Composability.PRFGame
