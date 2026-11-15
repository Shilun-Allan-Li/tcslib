import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.ComposeSim
open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines ComposeMachines

def idsToCheck : List String := ["Bool.eq_iff_iff","List.append_assoc","List.filter_append","List.filter_nil","List.filter_singleton","List.getD_eq_getElem?_getD","List.getElem?_append_right","List.getElem?_cons_zero","List.length_append","List.length_map","List.length_nil","List.length_singleton","List.map_append","List.map_singleton","List.range_add","List.range_succ","List.range_zero","List.singleton_append","List.take_append_of_le_length","List.take_of_length_le","Nat.sub_self","Option.getD_some","asmView_eq","asmW_eq","cond_false","cond_true","divNum_eq","getD_filter_map_mover","h","hfilt","hp","h₁","h₂","if_neg","if_pos","length_filter_mod_two","length_filter_mover","moverIsV_beq_iff","moverIsV_def","msgAt_encodeMsgs","padTo_eq","pairFstD_pairEncode","pairSndD_pairEncode","segW_eq","show"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly

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

end TCSlib.Cryptography.SecureComputation.ComposeSim
