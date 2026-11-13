import TCSlib.Cryptography.Foundations.BitLists
open Lean Elab Command

namespace TCSlib.Cryptography

def idsToCheck : List String := ["List.drop_left'","List.drop_nil","List.drop_succ_cons","List.drop_zero","List.flatMap_cons","List.flatMap_map","List.flatMap_nil","List.flatten_cons","List.getD_eq_getElem?_getD","List.getElem_map","List.getElem_ofFn","List.getElem_range","List.getElem_zipWith","List.head?_drop","List.headD_cons","List.headD_eq_head?","List.length_cons","List.length_flatten","List.length_map","List.length_ofFn","List.length_range","List.map_congr_left","List.map_const'","List.map_map","List.ofFn_add","List.ofFn_inj","List.ofFn_succ","List.range_succ_eq_map","List.sum_replicate_nat","h","hcons","hnil","ih","show"]
def scannedModule : Name := `TCSlib.Cryptography.Foundations.BitLists

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
