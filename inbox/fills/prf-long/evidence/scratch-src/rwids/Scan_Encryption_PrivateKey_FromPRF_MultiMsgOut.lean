import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.MultiMsgOut
open Lean Elab Command

namespace TCSlib.Cryptography
open Complexity Turing Finset

def idsToCheck : List String := ["List.flatMap_cons","List.flatMap_nil","MultiMsg.encodeList_eq_flatMap","MultiMsg.flatMap_ofFn","NUPPT.distinguisherL_eq","PolyExpr.eval_add","PolyExpr.eval_const","PrivateKeyScheme.encodeList_cons","PrivateKeyScheme.encodeList_nil","encodeTupleOut_eq","encodeTupleOut_eq_flatten","eval_multiMsgAdvOut","hadv","hφ","pairEncode_eq"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.MultiMsgOut

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

end TCSlib.Cryptography
