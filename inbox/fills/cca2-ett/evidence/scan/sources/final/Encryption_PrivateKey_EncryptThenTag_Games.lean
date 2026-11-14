import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.ETTGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

def idsToCheck : List String := ["Bool.and_eq_true","List.length_append","List.length_nil","List.length_ofFn","List.length_zipWith","Nat.min_self","OracleComp.pure_bind","ctW_eq","decAnsW_eq","decide_eq_true_eq","encW_eq","eq_pairEncode_of_pairFstD_ne","ettAcc_eq","ettImpl_apply","ettImpl_eq_freshImpl","ettTape","freshImpl_apply","h","hc","hc'","hitW_eq","hm","hr","hr'","length_maskL","length_pairEncode","maskL_eq","ofFn_padFin_of_length","pairFstD_pairEncode","pairSndD_pairEncode","pairV_eq","tagL_eq","tapeImpl_apply","wC_ctW","wC_eq","wR_ctW","wR_eq","wT_eq","wfW_eq"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games

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
