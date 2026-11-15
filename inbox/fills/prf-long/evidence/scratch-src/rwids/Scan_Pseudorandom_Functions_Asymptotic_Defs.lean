import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
open Lean Elab Command

namespace TCSlib.Cryptography
open Complexity Turing Finset

def idsToCheck : List String := ["List.flatMap_cons","List.length_append","List.length_cons","List.length_nil","NUPPT.toOracleAdversary_eq","OracleEnsemble.random_O","abs_abs","acceptProb_def","buildTree","buildTree_succ_of_query","buildTree_succ_of_ret","buildTree_zero_of_query","buildTree_zero_of_ret","decodeFin_ofFn","decodeOracleMove","decodeOracleMove_pairEncode_false","distAdv_def","e","h","lazyDist_apply","oracleDist_apply","pairDecode_pairEncode","pairDecode_true_two","pairEncode_eq","prfAdv_def","uprob_prod","uprob_prod_comm"]
def scannedModule : Name := `TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs

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
