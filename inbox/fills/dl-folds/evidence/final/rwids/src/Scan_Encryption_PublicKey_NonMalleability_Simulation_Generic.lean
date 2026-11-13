import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

def idsToCheck : List String := ["Function.comp_apply","List.append_eq_nil_iff","List.drop_left","List.drop_nil","List.flatMap_def","List.flatten_cons","List.flatten_nil","List.length_cons","List.length_drop","List.length_flatten","List.length_nil","List.length_replicate","List.map_cons","List.sum_cons","List.take_left","chunkEmit_eq","chunkMap","chunkStep_eq","eq_pairEncode_of_pairDecode","h.1","hl","hlen","if_neg","if_pos","iterEmit_encode","iterEmit_eq","length_pairEncode","pairFstD_of_pairDecode_eq_none","pairFstD_pairEncode","pairSndD_of_pairDecode_eq_none","pairSndD_pairEncode"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic

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

end TCSlib.Cryptography.Composability.NMSim
