import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Chain
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.ComposeProb
open Finset

def idsToCheck : List String := ["Fin.eta","Function.update_of_ne","Function.update_self","List.getD_eq_getElem?_getD","List.getElem?_append_left","List.getElem?_append_right","List.getElem?_cons_succ","List.getElem?_cons_zero","List.getElem?_map","List.getElem?_range","List.length_map","List.length_range","Nat.sub_self","Option.getD_some","Option.map_some","acceptProb_comp_equiv","acceptProb_fst","acceptProb_snd","card_range","dif_neg","dif_pos","h0","hL","hk","hlt","hybV_eq","hybV_succ_update","hybV_update","if_neg","if_pos","nsmul_eq_mul","plugV_eq","show","sum_const"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Chain

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

end TCSlib.Cryptography.SecureComputation.ComposeProb
