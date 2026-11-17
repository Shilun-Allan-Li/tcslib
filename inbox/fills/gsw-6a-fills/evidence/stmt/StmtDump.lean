import TCSlib.Complexity.BranchingPrograms.BarringtonConverse
import TCSlib.Complexity.BranchingPrograms.NC1
import TCSlib.Complexity.CircuitComplexity.NANDLayering
import TCSlib.Complexity.CircuitComplexity.FormulaArith.CarrySave
import TCSlib.Complexity.CircuitComplexity.FormulaArith.Compare
import TCSlib.Complexity.CircuitComplexity.FormulaArith.ModSum
open Lean Elab Command Meta

/-! Statement dump (gsw-6a-fills, check 3): the 41 targets with full names, kinds and types printed with
full names (`pp.fullNames`, `pp.funBinderTypes`, `pp.explicit` off), one per line block, sorted. Run at the
base and at the head; the two outputs must be identical. -/

set_option pp.fullNames true in
set_option pp.funBinderTypes true in
set_option pp.universes true in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let names : List Name := [
    `BranchingProgram.Instr.wire_eval,
    `BranchingProgram.Instr.depth_wire_le,
    `BranchingProgram.Instr.maxFanin_wire_le,
    `BranchingProgram.wireComp_eval,
    `BranchingProgram.depth_wireComp_le,
    `BranchingProgram.compTree_eval,
    `BranchingProgram.depth_compTree_le,
    `BranchingProgram.maxFanin_compTree_le,
    `BranchingProgram.toFormula_eval,
    `BranchingProgram.depth_toFormula_le,
    `BranchingProgram.maxFanin_toFormula_le,
    `BranchingProgram.exists_fiveCycleRecognizes_of_dagCircuit,
    `Language.InNC.inPBP_five,
    `Language.InBWBP.inNC_one,
    `Language.inNC_one_iff_inBWBP,
    `Language.inNC_one_iff_inPBP_five,
    `BoolCircuit.DAGCircuit.layerGates_acyclic,
    `BoolCircuit.DAGCircuit.layerOutput_lt,
    `BoolCircuit.DAGCircuit.layerNAND_eval,
    `BoolCircuit.DAGCircuit.layerNAND_isLayered,
    `BoolCircuit.DAGCircuit.layerNAND_isNANDForm,
    `BoolCircuit.DAGCircuit.layerNAND_depth,
    `BoolCircuit.DAGCircuit.layerNAND_size_le,
    `BoolCircuit.FormulaArith.csaStep_val,
    `BoolCircuit.FormulaArith.depth_csaStep_le,
    `BoolCircuit.FormulaArith.maxFaninL_csaStep_le,
    `BoolCircuit.FormulaArith.csaReduce_val,
    `BoolCircuit.FormulaArith.depth_csaReduce_le,
    `BoolCircuit.FormulaArith.maxFaninL_csaReduce_le,
    `BoolCircuit.FormulaArith.csaLevels_le,
    `BoolCircuit.FormulaArith.carryOut_eval,
    `BoolCircuit.FormulaArith.carryOut_eval_le,
    `BoolCircuit.FormulaArith.depth_carryOut_le,
    `BoolCircuit.FormulaArith.maxFanin_carryOut_le,
    `BoolCircuit.FormulaArith.geConst_eval,
    `BoolCircuit.FormulaArith.depth_geConst_le,
    `BoolCircuit.FormulaArith.maxFanin_geConst_le,
    `BoolCircuit.FormulaArith.modSumInterval_eval,
    `BoolCircuit.FormulaArith.depth_modSumInterval_le,
    `BoolCircuit.FormulaArith.modSumDepth_le,
    `BoolCircuit.FormulaArith.maxFanin_modSumInterval_le]
  let mut out : Array String := #[]
  for n in names do
    match env.find? n with
    | none => out := out.push s!"{n}\tMISSING"
    | some c =>
      let fmt ← liftTermElabM <| ppExpr c.type
      let kind := match c with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "other"
      out := out.push s!"{n}\t{kind}\t{c.levelParams}\n  : {fmt}"
  for s in out.qsort (· < ·) do
    IO.println s
