import TCSlib.Cryptography.Asymptotic.Adversary
open Lean Elab Command

namespace TCSlib.Cryptography
open Complexity Turing Finset

def idsToCheck : List String := ["List.getD_eq_getElem?_getD","List.getElem?_eq_getElem","List.getElem_drop","List.getElem_ofFn","List.getElem_take","List.length_drop","List.length_ofFn","List.length_take","List.ofFn_get","NUPPT.computes_iff","NUPPT.inverter","Nat.add_mul","Nat.mul_comm","Nat.one_mul","Nat.succ_mul","Option.some.injEq","coinBlock_eq","decodeFin","decodeFin_ofFn","dif_pos","finProdFinEquiv_apply_val","h","h'","hf","hp","hw","hx'","invProbOpt","invProbOpt_def","invProb_def","padFin","padFin_def","uprob_true"]
def scannedModule : Name := `TCSlib.Cryptography.Asymptotic.Adversary

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

end TCSlib.Cryptography
