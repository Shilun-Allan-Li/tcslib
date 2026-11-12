import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
open Lean Elab Command

namespace TCSlib.Cryptography.Composability
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability.FixedLengthScheme

def idsToCheck : List String := ["S.inLens_one","S.inLens_two","S.inLens_zero","S.indSpec_eq","S.outLens_one","S.outLens_two","S.outLens_zero","bitSpec_dom","bitSpec_rng","cast_eq","decOpen","indImpl"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity

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

end TCSlib.Cryptography.Composability
