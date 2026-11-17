import TCSlib.Complexity.BranchingPrograms.BarringtonConverse
import TCSlib.Complexity.BranchingPrograms.NC1
import TCSlib.Complexity.CircuitComplexity.NANDLayering
import TCSlib.Complexity.CircuitComplexity.FormulaArith.CarrySave
import TCSlib.Complexity.CircuitComplexity.FormulaArith.Compare
import TCSlib.Complexity.CircuitComplexity.FormulaArith.ModSum
open Lean Elab Command

/-! Axiom census and `sorryAx` dependency trace (gsw-6a-fills, check 4). For every stored constant of the six
owned modules (compiler auxiliaries included): `CENSUS <module> <name> <kind> <axioms>`. For every one that
reaches `sorryAx`: `TRACE <name> via [...]`, the constants of any TCSlib module whose own type or value
mentions `sorryAx` directly and that are reachable from it through TCSlib constants (the walk follows the
type and value of every TCSlib constant). Expected: only admitted declarations (or their auxiliaries) of the
in-house units (Defs, Eval, Barrington, NANDForm, Combinators). -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let owned : List Name := [
    `TCSlib.Complexity.BranchingPrograms.BarringtonConverse,
    `TCSlib.Complexity.BranchingPrograms.NC1,
    `TCSlib.Complexity.CircuitComplexity.NANDLayering,
    `TCSlib.Complexity.CircuitComplexity.FormulaArith.CarrySave,
    `TCSlib.Complexity.CircuitComplexity.FormulaArith.Compare,
    `TCSlib.Complexity.CircuitComplexity.FormulaArith.ModSum]
  let names := env.header.moduleNames
  let idxs := owned.filterMap env.getModuleIdx?
  let isLib (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => (`TCSlib).isPrefixOf names[i.toNat]! | none => false
  let mut direct : Std.HashSet Name := {}
  for (n, c) in env.constants.toList do
    if isLib n then
      let v := (c.value? (allowOpaque := true)).getD (mkConst `True)
      if (c.type.getUsedConstants ++ v.getUsedConstants).contains ``sorryAx then
        direct := direct.insert n
  let mut out : Array String := #[]
  for (n, c) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    if idxs.contains i then
      let axs ← liftCoreM (Lean.collectAxioms n)
      let kind := match c with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor" | .recInfo _ => "recursor" | .opaqueInfo _ => "opaque"
        | _ => "other"
      let axl := axs.qsort (·.toString < ·.toString) |>.toList
      out := out.push s!"CENSUS\t{names[i.toNat]!}\t{n}\t{kind}\t{axl}"
      if axs.contains ``sorryAx then
        let mut seen : Std.HashSet Name := {}
        let mut stack : Array Name := #[n]
        let mut via : Array Name := #[]
        while !stack.isEmpty do
          let m := stack.back!
          stack := stack.pop
          if seen.contains m then continue
          seen := seen.insert m
          if direct.contains m then via := via.push m
          let some cm := env.find? m | continue
          let v := (cm.value? (allowOpaque := true)).getD (mkConst `True)
          for d in cm.type.getUsedConstants ++ v.getUsedConstants do
            if isLib d && !seen.contains d then stack := stack.push d
        let vl := via.qsort (·.toString < ·.toString) |>.toList
        out := out.push s!"TRACE\t{n}\tvia {vl}"
  for l in out.qsort (· < ·) do
    IO.println l
