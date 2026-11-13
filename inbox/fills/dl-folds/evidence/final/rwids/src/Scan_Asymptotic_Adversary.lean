import TCSlib.Cryptography.Asymptotic.Adversary
open Lean Elab Command

namespace TCSlib.Cryptography
open Complexity Turing Finset

def idsToCheck : List String := ["FunFamily.ofFn_blocks","List.append_assoc","List.drop_append","List.drop_append_of_le_length","List.drop_eq_nil_of_le","List.drop_of_length_le","List.flatten_append","List.flatten_cons","List.flatten_singleton","List.getD_eq_getElem?_getD","List.getElem?_eq_getElem","List.getElem_cons_succ","List.getElem_drop","List.getElem_map","List.getElem_ofFn","List.getElem_range","List.getElem_take","List.length_drop","List.length_map","List.length_ofFn","List.length_range","List.length_take","List.map_append","List.map_singleton","List.nil_append","List.ofFn_get","List.range_succ","List.take_append_of_le_length","List.take_left'","NUPPT.computes_iff","NUPPT.inverter","Nat.add_mul","Nat.add_sub_cancel_left","Nat.mul_comm","Nat.one_mul","Nat.succ_mul","Option.some.injEq","coinBlock_eq","coinBlock_flatten","decodeFin","decodeFin_ofFn","dif_pos","finProdFinEquiv_apply_val","h","h'","hblk","hc","hd","hf","hp","hrest","hw","hx'","invProbOpt","invProbOpt_def","invProb_def","length_flatten_map_range","padFin","padFin_def","show","uprob_true"]
def scannedModule : Name := `TCSlib.Cryptography.Asymptotic.Adversary

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
