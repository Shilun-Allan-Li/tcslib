import TCSlib.Cryptography.Games.BitCodec
open Lean Elab Command

namespace TCSlib.Cryptography.Games
open Complexity Turing

def idsToCheck : List String := ["List.ofFn_const","MachineCodec.encodeLog_cons","MachineCodec.encodeLog_nil","Option.some.injEq","bitCodec_encodeEntry","decodeBitMove","decodeBitMove_encodeBitMove","decodeFin_eq_some_iff","decodeFin_ofFn","decodeIdx","decodeIdx_eq_some_iff.1","decodeIdx_eq_some_iff.2","decodeIdx_replicate","dif_pos","eq_pairEncode_of_pairDecode","h","ih","pairDecode_pairEncode","show"]
def scannedModule : Name := `TCSlib.Cryptography.Games.BitCodec

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
