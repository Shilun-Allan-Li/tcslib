import TCSlib.Complexity.BranchingPrograms.Defs
import TCSlib.Complexity.BranchingPrograms.Eval
import TCSlib.Complexity.BranchingPrograms.Barrington
import TCSlib.Complexity.BranchingPrograms.BarringtonConverse
import TCSlib.Complexity.BranchingPrograms.NC1
import TCSlib.Complexity.BranchingPrograms
import TCSlib.Complexity.CircuitComplexity.FormulaArith.Combinators
import TCSlib.Complexity.CircuitComplexity.FormulaArith.CarrySave
import TCSlib.Complexity.CircuitComplexity.FormulaArith.Compare
import TCSlib.Complexity.CircuitComplexity.FormulaArith.ModSum
import TCSlib.Complexity.CircuitComplexity.FormulaArith
import TCSlib.Complexity.CircuitComplexity.NANDForm
import TCSlib.Complexity.CircuitComplexity.NANDLayering
import TCSlib.Complexity.CircuitComplexity.TreeNCAC
open Lean Elab Command Meta

/-! Statement dump (6a statement job): every constant of the new and changed modules, with its type
printed with full names, and the library constants its type mentions. -/

set_option pp.fullNames true in
set_option pp.funBinderTypes true in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : List Name := [
    `TCSlib.Complexity.BranchingPrograms.Defs,
    `TCSlib.Complexity.BranchingPrograms.Eval,
    `TCSlib.Complexity.BranchingPrograms.Barrington,
    `TCSlib.Complexity.BranchingPrograms.BarringtonConverse,
    `TCSlib.Complexity.BranchingPrograms.NC1,
    `TCSlib.Complexity.BranchingPrograms,
    `TCSlib.Complexity.CircuitComplexity.FormulaArith.Combinators,
    `TCSlib.Complexity.CircuitComplexity.FormulaArith.CarrySave,
    `TCSlib.Complexity.CircuitComplexity.FormulaArith.Compare,
    `TCSlib.Complexity.CircuitComplexity.FormulaArith.ModSum,
    `TCSlib.Complexity.CircuitComplexity.FormulaArith,
    `TCSlib.Complexity.CircuitComplexity.NANDForm,
    `TCSlib.Complexity.CircuitComplexity.NANDLayering,
    `TCSlib.Complexity.CircuitComplexity.TreeNCAC]
  let idxs := mods.filterMap env.getModuleIdx?
  let names := env.header.moduleNames
  let mut out : Array (String × String) := #[]
  for (n, c) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    if idxs.contains i && !n.isInternal then
      let fmt ← liftTermElabM <| ppExpr c.type
      let consts := c.type.getUsedConstants.filter fun d =>
        (`TCSlib).isPrefixOf d || (`BoolCircuit).isPrefixOf d || (`BranchingProgram).isPrefixOf d ||
          (`BranchingProgramFamily).isPrefixOf d || (`Language).isPrefixOf d
      let kind := match c with
        | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor" | .recInfo _ => "recursor" | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
      out := out.push (n.toString, s!"{n}\t{kind}\t{names[i.toNat]!}\n  : {fmt}\n  CONSTS {consts.toList}")
  for (_, s) in out.qsort (fun a b => a.1 < b.1) do
    IO.println s
