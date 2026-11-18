import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
open Lean Elab Command

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit

def idsToCheck : List String := ["BranchingProgram.Instr.stepWith_of_isPermutation","BranchingProgram.barrington_yield_zero","BranchingProgram.evalWith_single","BranchingProgram.sigma1_eq","Nat.cast_one","Nat.cast_zero","Pi.single_eq_of_ne","Pi.single_eq_same","decide_eq_false","decide_eq_true","hm","homEvalFormula_eq","homEvalPBP_eq","hy","if_neg","if_pos","select_eq","show","zero_mul"]
def scannedModule : Name := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching

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

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
