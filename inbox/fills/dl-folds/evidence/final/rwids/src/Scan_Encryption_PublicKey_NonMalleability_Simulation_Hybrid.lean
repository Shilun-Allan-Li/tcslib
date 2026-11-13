import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Hybrid
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.NMSim
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

def idsToCheck : List String := ["Bool.false_and","Bool.false_eq_true","FixedLengthScheme.decOpen_cpa","List.flatten_append","List.flatten_nil","List.flatten_singleton","List.length_cons","List.length_ofFn","List.length_replicate","List.map_append","List.map_nil","List.map_singleton","List.range_succ","List.range_zero","List.take_add","List.take_zero","Nat.add_zero","Nat.succ_mul","Nat.zero_mul","PolyExpr.eval_add","PolyExpr.eval_const","S.inLens_one","S.inLens_zero","S.outLens_one","S.outLens_zero","coinBlock_eq","entryL_eq","histImpl_eq","hsub","hv","hybAcc_eq","if_neg","if_pos","ih","rImpl_dec","rImpl_eq_of_msgLen_eq_zero","rImpl_false_coins","rImpl_none_eager","rImpl_none_lazy","realAcc_eq","reduceIte","snmDin_one","snmDin_zero","snmDout_one","snmDout_zero"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Hybrid

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
