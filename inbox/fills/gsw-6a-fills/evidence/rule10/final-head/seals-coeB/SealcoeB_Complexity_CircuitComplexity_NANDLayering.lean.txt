/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Lean
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.MinMax
import TCSlib.Complexity.CircuitComplexity.NANDForm
/- G06-HARNESS INSTALL SealcoeB_Complexity_CircuitComplexity_NANDLayering -/
set_option maxHeartbeats 0
run_cmd do
  let label : String := "SealcoeB_Complexity_CircuitComplexity_NANDLayering"
  let payload : String := "BoolCircuit.CompileListSpec.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.CompileSpec.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.DAGCircuit.IsFaninTwo\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.IsNANDForm\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.DAGCircuit.IsWellFormed\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.decidableIsNANDForm\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.DAGCircuit.depth\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.depthAt\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.depths\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.eval\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.rewrite\tTCSlib.Complexity.CircuitComplexity.DAGTransform\nBoolCircuit.DAGCircuit.size\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.toNANDForm\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.DAGCircuit.toTree\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.DAGCircuit.values\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.Accepts\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.HasFaninTwo\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.HasPolylogDepth\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.IsPolySize\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.IsWellFormed\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.language\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate.FaninTwo\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate.IsNAND\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.DAGGate.WellFormed\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate.decidableIsNAND\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.DAGGate.depth\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate.eval\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate.remap\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.GadgetCorrect\tTCSlib.Complexity.CircuitComplexity.DAGTransform\nBoolCircuit.GadgetSpec.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.DAGTransform\nBoolCircuit.GateKind._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.GateKind._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.GateKind.enumList\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.GateKind.ofNat\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.GatesAcyclic\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.Lit._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.Lit._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.Lit.eval\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.Lit.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit._sizeOf_2\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit._sizeOf_3\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit._sizeOf_4\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.constTrue\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.depth\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.depth._mutual\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.depth._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.eval\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.eval._mutual\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.eval._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.eval.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.litCount\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.litCount._mutual\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.litCount._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.litCount.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.ofVar\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.size\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.size._mutual\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.size._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.toTreeCircuit\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.toTreeCircuit._mutual\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.toTreeCircuit._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.constFalse\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.depth\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.depth._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.eval\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.eval._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.eval.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.litCount\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.litCount._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.litCount.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.ofVar\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.size\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.size._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.toTreeCircuit\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.toTreeCircuit._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.RewriteInv.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.DAGTransform\nBoolCircuit.TreeCircuit._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit._sizeOf_2\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.depth\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.depth._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.eval\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.eval._unary\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.eval._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.eval.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.ind.match_1_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.length_le_sumSize.match_1_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.litCount\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.litCount._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.maxDepth\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.maxFanin\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.maxFanin._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.maxFaninL\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.size\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.size._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.sumSize\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toDAG\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.TreeCircuit.toNAnd\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toNAnd._mutual\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toNAnd._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toNAnd.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toNOr\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toNOr._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toNOr.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.compileTree\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTree._sunfold\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTree._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTree.match_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTrees\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTrees._sunfold\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTrees._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTrees.match_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTrees_spec.match_1_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.constCircuit\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.constGate\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instDecidableEqDAGGate\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instDecidableEqDAGGate.decEq\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instDecidableEqDAGGate.decEq.match_1\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instDecidableEqGateKind\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instDecidableEqLit\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instDecidableEqLit.decEq\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instDecidableEqLit.decEq.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instFintypeGateKind\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instHashableLit\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instHashableLit.hash\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instHashableLit.hash.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instReprDAGGate\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instReprDAGGate.repr\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instReprGateKind\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instReprGateKind.repr\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instReprGateKind.repr.match_1\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instReprLit\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instReprLit.repr\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instReprTreeCircuit\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instReprTreeCircuit.repr._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instReprTreeCircuit.repr.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.nandGadget\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.nandGadget.match_1\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.nodeKind\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.rewriteGates\tTCSlib.Complexity.CircuitComplexity.DAGTransform\nBoolCircuit.rewriteStep\tTCSlib.Complexity.CircuitComplexity.DAGTransform\nBoolCircuit.runWith\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.unfoldGate\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldGate.match_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldGate_eval.match_1_10\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldGate_eval.match_1_12\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldGate_eval.match_1_4\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldGate_eval.match_1_6\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldVertex\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldVertex._sunfold\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldVertex._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldVertex.match_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.vertexDepth\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.vertexValue\tTCSlib.Complexity.CircuitComplexity.TreeDAG\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NAndCircuit.eval.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NAndCircuit.litCount.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NOrCircuit.eval.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NOrCircuit.litCount.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.eval.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.sumSize_add_length_le.match_1_1\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.toNAnd.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.toNOr.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.instReprTreeCircuit.repr.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.List.map_unattach.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.DAGCircuit.0.BoolCircuit.instReprGateKind.repr.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\n_private.TCSlib.Complexity.CircuitComplexity.TreeDAG.0.BoolCircuit.compileTree.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.TreeDAG\n_private.TCSlib.Complexity.CircuitComplexity.TreeDAG.0.BoolCircuit.compileTrees.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.TreeDAG\n_private.TCSlib.Complexity.CircuitComplexity.TreeDAG.0.BoolCircuit.unfoldVertex.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.TreeDAG"
  let expectedRequests : Nat := 187
  let mut requests : Array (String × String) := #[]
  let payloadLines := if payload.isEmpty then [] else payload.splitOn "\n"
  for line in payloadLines do
    match line.splitOn "\t" with
    | [spelling, home] =>
      unless !spelling.isEmpty && !home.isEmpty do throwError "G06-HARNESS {label}: empty request field"
      requests := requests.push (spelling, home)
    | _ => throwError "G06-HARNESS {label}: malformed serialized request row"
  unless requests.size == expectedRequests do throwError "G06-HARNESS {label}: serialized request count differs: {requests.size} vs {expectedRequests}"
  let rec nameParts : Lean.Name → List (String × String)
    | .anonymous => []
    | .str p s => nameParts p ++ [("str", s)]
    | .num p n => nameParts p ++ [("num", toString n)]
  let nameKey (n : Lean.Name) : String := (Lean.toJson (nameParts n)).compress
  let componentPayload : String := "BoolCircuit.CompileListSpec.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"CompileListSpec\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\ttrue\nBoolCircuit.CompileSpec.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"CompileSpec\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGCircuit.IsFaninTwo\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"IsFaninTwo\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.IsNANDForm\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"IsNANDForm\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.IsWellFormed\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"IsWellFormed\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGCircuit._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\ttrue\nBoolCircuit.DAGCircuit.decidableIsNANDForm\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"decidableIsNANDForm\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\ttrue\tfalse\tfalse\nBoolCircuit.DAGCircuit.depth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"depth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.depthAt\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"depthAt\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.depths\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"depths\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.eval\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"eval\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGCircuit.rewrite\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"rewrite\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGTransform\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.size\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"size\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.toNANDForm\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"toNANDForm\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.toTree\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"toTree\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"unfoldVertex_depth_le\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"unfoldVertex_eval\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"unfoldVertex_maxFanin_le\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"unfoldVertex_size_le\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.DAGCircuit.values\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"values\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily.Accepts\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"Accepts\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily.HasFaninTwo\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"HasFaninTwo\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily.HasPolylogDepth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"HasPolylogDepth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily.IsPolySize\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"IsPolySize\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily.IsWellFormed\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"IsWellFormed\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGCircuitFamily._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\ttrue\nBoolCircuit.DAGCircuitFamily.language\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"language\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGGate.FaninTwo\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"FaninTwo\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGGate.IsNAND\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"IsNAND\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGGate.WellFormed\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"WellFormed\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGGate._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGGate._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\ttrue\nBoolCircuit.DAGGate.decidableIsNAND\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"decidableIsNAND\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\ttrue\tfalse\tfalse\nBoolCircuit.DAGGate.depth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"depth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGGate.eval\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"eval\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGGate.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGGate.remap\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"remap\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.GadgetCorrect\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GadgetCorrect\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGTransform\"]]\tfalse\tfalse\tfalse\nBoolCircuit.GadgetSpec.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GadgetSpec\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGTransform\"]]\tfalse\tfalse\ttrue\nBoolCircuit.GateKind._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GateKind\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.GateKind._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GateKind\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\ttrue\nBoolCircuit.GateKind.enumList\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GateKind\"],[\"str\",\"enumList\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.GateKind.ofNat\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GateKind\"],[\"str\",\"ofNat\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.GatesAcyclic\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GatesAcyclic\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.Lit._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"Lit\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.Lit._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"Lit\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\ttrue\nBoolCircuit.Lit.eval\t[[\"str\",\"BoolCircuit\"],[\"str\",\"Lit\"],[\"str\",\"eval\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.Lit.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"Lit\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.NAndCircuit._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.NAndCircuit._sizeOf_2\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"_sizeOf_2\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.NAndCircuit._sizeOf_3\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"_sizeOf_3\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.NAndCircuit._sizeOf_4\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"_sizeOf_4\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.NAndCircuit._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\ttrue\nBoolCircuit.NAndCircuit.constTrue\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"constTrue\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.depth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"depth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.depth._mutual\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"depth\"],[\"str\",\"_mutual\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.depth._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"depth\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.eval\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"eval\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.eval._mutual\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"eval\"],[\"str\",\"_mutual\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.eval._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"eval\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.eval.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"eval\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.NAndCircuit.litCount\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"litCount\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.litCount._mutual\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"litCount\"],[\"str\",\"_mutual\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.litCount._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"litCount\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.litCount.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"litCount\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.NAndCircuit.ofVar\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"ofVar\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.size\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"size\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.size._mutual\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"size\"],[\"str\",\"_mutual\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.size._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"size\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.toTreeCircuit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"toTreeCircuit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.toTreeCircuit._mutual\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"toTreeCircuit\"],[\"str\",\"_mutual\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.toTreeCircuit._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"toTreeCircuit\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\ttrue\nBoolCircuit.NOrCircuit.constFalse\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"constFalse\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.depth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"depth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.depth._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"depth\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.eval\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"eval\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.eval._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"eval\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.eval.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"eval\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.NOrCircuit.litCount\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"litCount\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.litCount._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"litCount\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.litCount.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"litCount\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.NOrCircuit.ofVar\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"ofVar\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.size\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"size\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.size._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"size\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.toTreeCircuit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"toTreeCircuit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.toTreeCircuit._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"toTreeCircuit\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.RewriteInv.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"RewriteInv\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGTransform\"]]\tfalse\tfalse\ttrue\nBoolCircuit.TreeCircuit._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.TreeCircuit._sizeOf_2\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"_sizeOf_2\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.TreeCircuit._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\ttrue\nBoolCircuit.TreeCircuit.depth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"depth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.depth._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"depth\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"depth_le_maxDepth\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.eval\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"eval\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.eval._unary\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"eval\"],[\"str\",\"_unary\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.eval._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"eval\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.eval.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"eval\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.ind.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"ind\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.length_le_sumSize.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"length_le_sumSize\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.litCount\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"litCount\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.litCount._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"litCount\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.maxDepth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"maxDepth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.maxFanin\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"maxFanin\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.maxFanin._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"maxFanin\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.maxFaninL\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"maxFaninL\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"maxFaninL_le_sumSize\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"maxFanin_le_maxFaninL\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.size\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"size\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.size._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"size\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.sumSize\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"sumSize\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toDAG\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toDAG\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toNAnd\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNAnd\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toNAnd._mutual\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNAnd\"],[\"str\",\"_mutual\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toNAnd._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNAnd\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toNAnd.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNAnd\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.toNOr\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNOr\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toNOr._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNOr\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toNOr.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNOr\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.compileTree\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTree\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.compileTree._sunfold\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTree\"],[\"str\",\"_sunfold\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.compileTree._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTree\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.compileTree.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTree\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.compileTrees\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTrees\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.compileTrees._sunfold\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTrees\"],[\"str\",\"_sunfold\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.compileTrees._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTrees\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.compileTrees.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTrees\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.compileTrees_spec.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTrees_spec\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.constCircuit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"constCircuit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.constGate\t[[\"str\",\"BoolCircuit\"],[\"str\",\"constGate\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instDecidableEqDAGGate\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqDAGGate\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instDecidableEqDAGGate.decEq\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqDAGGate\"],[\"str\",\"decEq\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instDecidableEqDAGGate.decEq.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqDAGGate\"],[\"str\",\"decEq\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\ttrue\ttrue\nBoolCircuit.instDecidableEqGateKind\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqGateKind\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instDecidableEqLit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqLit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instDecidableEqLit.decEq\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqLit\"],[\"str\",\"decEq\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instDecidableEqLit.decEq.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqLit\"],[\"str\",\"decEq\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.instFintypeGateKind\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instFintypeGateKind\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instHashableLit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instHashableLit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instHashableLit.hash\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instHashableLit\"],[\"str\",\"hash\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instHashableLit.hash.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instHashableLit\"],[\"str\",\"hash\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.instReprDAGGate\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprDAGGate\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instReprDAGGate.repr\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprDAGGate\"],[\"str\",\"repr\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instReprGateKind\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprGateKind\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instReprGateKind.repr\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprGateKind\"],[\"str\",\"repr\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instReprGateKind.repr.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprGateKind\"],[\"str\",\"repr\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\ttrue\ttrue\nBoolCircuit.instReprLit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprLit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instReprLit.repr\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprLit\"],[\"str\",\"repr\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instReprTreeCircuit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprTreeCircuit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instReprTreeCircuit.repr._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprTreeCircuit\"],[\"str\",\"repr\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instReprTreeCircuit.repr.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprTreeCircuit\"],[\"str\",\"repr\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.nandGadget\t[[\"str\",\"BoolCircuit\"],[\"str\",\"nandGadget\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\tfalse\tfalse\tfalse\nBoolCircuit.nandGadget.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"nandGadget\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\tfalse\ttrue\ttrue\nBoolCircuit.nodeKind\t[[\"str\",\"BoolCircuit\"],[\"str\",\"nodeKind\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.rewriteGates\t[[\"str\",\"BoolCircuit\"],[\"str\",\"rewriteGates\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGTransform\"]]\tfalse\tfalse\tfalse\nBoolCircuit.rewriteStep\t[[\"str\",\"BoolCircuit\"],[\"str\",\"rewriteStep\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGTransform\"]]\tfalse\tfalse\tfalse\nBoolCircuit.runWith\t[[\"str\",\"BoolCircuit\"],[\"str\",\"runWith\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.unfoldGate\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldGate\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.unfoldGate.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldGate\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.unfoldGate_eval.match_1_10\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldGate_eval\"],[\"str\",\"match_1_10\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.unfoldGate_eval.match_1_12\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldGate_eval\"],[\"str\",\"match_1_12\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.unfoldGate_eval.match_1_4\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldGate_eval\"],[\"str\",\"match_1_4\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.unfoldGate_eval.match_1_6\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldGate_eval\"],[\"str\",\"match_1_6\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.unfoldVertex\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldVertex\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.unfoldVertex._sunfold\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldVertex\"],[\"str\",\"_sunfold\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.unfoldVertex._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldVertex\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.unfoldVertex.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldVertex\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.vertexDepth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"vertexDepth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.vertexValue\t[[\"str\",\"BoolCircuit\"],[\"str\",\"vertexValue\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NAndCircuit.eval.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"eval\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NAndCircuit.litCount.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"litCount\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NOrCircuit.eval.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"eval\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NOrCircuit.litCount.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"litCount\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.eval.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"eval\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.sumSize_add_length_le.match_1_1\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"sumSize_add_length_le\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.toNAnd.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNAnd\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.toNOr.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNOr\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.instReprTreeCircuit.repr.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"instReprTreeCircuit\"],[\"str\",\"repr\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.List.map_unattach.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"List\"],[\"str\",\"map_unattach\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.DAGCircuit.0.BoolCircuit.instReprGateKind.repr.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"instReprGateKind\"],[\"str\",\"repr\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.TreeDAG.0.BoolCircuit.compileTree.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"compileTree\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.TreeDAG.0.BoolCircuit.compileTrees.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"compileTrees\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.TreeDAG.0.BoolCircuit.unfoldVertex.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldVertex\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\ttrue"
  let mut components : Std.HashMap String (String × String × String × String × String) := {}
  for line in (if componentPayload.isEmpty then [] else componentPayload.splitOn "\n") do
    match line.splitOn "\t" with
    | [n, nk, hk, i, m, a] =>
      if (components[n]?).isSome then throwError "G06-HARNESS {label}: duplicate component request"
      components := components.insert n (nk, hk, i, m, a)
    | _ => throwError "G06-HARNESS {label}: malformed component request"
  unless components.size == requests.size do throwError "G06-HARNESS {label}: component count differs"
  let env ← Lean.getEnv
  let mut resolved : Array Lean.Name := #[]
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  let mut verified : Nat := 0
  let mut active : Nat := 0
  let mut already : Nat := 0
  for (n, _) in env.constants.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue
    let ns := (catalog[n.toString]?).getD #[]
    catalog := catalog.insert n.toString (ns.push n)
  for (spelling, expectedHome) in requests do
    let ns := (catalog[spelling]?).getD #[]
    unless ns.size == 1 do throwError "G06-HARNESS {label}: absent/ambiguous imported name {spelling}; candidates={ns.size}"
    let n := ns[0]!
    let some mi := env.getModuleIdxFor? n | throwError "G06-HARNESS {label}: no home for {spelling}"
    let home := env.header.moduleNames[mi.toNat]!
    unless home.toString == expectedHome do throwError "G06-HARNESS {label}: home differs for {spelling}: {home}"
    let some ci := env.find? n | throwError "G06-HARNESS {label}: no constant for {spelling}"
    unless ci.isDefinition do throwError "G06-HARNESS {label}: requested nondefinition {spelling}"
    let some (nk, hk, ei, em, ea) := components[spelling]?
      | throwError "G06-HARNESS {label}: missing component request"
    unless nameKey n == nk && nameKey home == hk do
      throwError "G06-HARNESS {label}: actual Name components differ"
    let instanceFlag := Lean.Meta.isInstanceCore env n
    let matcherFlag := (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome
    let abbrevFlag := match ci with
      | .defnInfo d => match d.hints with | .abbrev => true | _ => false
      | _ => false
    unless toString instanceFlag == ei && toString matcherFlag == em && toString abbrevFlag == ea do
      throwError "G06-HARNESS {label}: definition/instance metadata differs"
    Lean.logInfo m!"G06-COMPONENT label={label} phase=install spelling={spelling} key={nk} home_key={hk} instance={instanceFlag}"
    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if before == .irreducible then
      already := already + 1
    else
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
      active := active + 1
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless installed == .irreducible do throwError "G06-HARNESS {label}: seal not installed for {spelling}"
    resolved := resolved.push n
    verified := verified + 1
    Lean.logInfo m!"G06-NAME label={label} spelling={spelling} actual={n.toString} home={home} before={repr before} installed={repr installed}"
  unless active + already == requests.size do throwError "G06-HARNESS {label}: installation count mismatch"
  unless verified == requests.size do throwError "G06-HARNESS {label}: verification count mismatch"
  let maskExt := Lean.Meta.globalInstanceExtension
  let maskEnv ← Lean.getEnv
  let scopes := maskExt.ext.getState maskEnv
  unless scopes.stateStack.length == 1 do
    throwError "G06-HARNESS {label}: unfolding mask requires base scope"
  let mut scopedNames : Std.HashSet Lean.Name := {}
  for (_, payloads) in scopes.scopedEntries.map.toList do
    for n in payloads do
      scopedNames := scopedNames.insert n
  let mut removed : Nat := 0
  for n in resolved do
    if scopedNames.contains n then
      throwError "G06-HARNESS {label}: scoped unfolding payload intersects request {n}"
    if Lean.Meta.isGlobalInstance maskEnv n then
      removed := removed + 1
  -- InstanceEntry's BEq checks only val, so compare every field explicitly.
  let entryFields (e : Lean.Meta.InstanceEntry) :=
    (e.keys, Lean.ExprStructEq.mk e.val, e.priority, e.globalName?, e.synthOrder, e.attrKind)
  let lookupSnapshot (e : Lean.Environment) :=
    let s := Lean.Meta.instanceExtension.getState e
    (s.discrTree.toArray.map (fun (ks, entry) => (ks, entryFields entry)),
      s.instanceNames.toArray.map (fun (n, entry) => (n, entryFields entry)), s.erased.toList)
  let beforeLookup := lookupSnapshot env
  Lean.modifyEnv fun current =>
    maskExt.modifyState current fun membership =>
      resolved.foldl (fun s n => s.erase n) membership
  let maskedEnv ← Lean.getEnv
  unless beforeLookup == lookupSnapshot maskedEnv do
    throwError "G06-HARNESS {label}: typeclass lookup state changed"
  for n in resolved do
    if Lean.Meta.isGlobalInstance maskedEnv n then
      throwError "G06-HARNESS {label}: unfolding membership after mask for {n}"
  Lean.logInfo m!"G06-MASK label={label} phase=install requested={requests.size} verified={resolved.size} removed={removed} scope_depth=1 scoped_names={scopedNames.size} tc_state=preserved"
  Lean.logInfo m!"G06-SEAL label={label} requested={requests.size} active={active} already_irreducible={already} verified={verified}"


/-!
# Layering NAND-form `DAGCircuit`s

A circuit is *layered* (`BoolCircuit.DAGCircuit.IsLayered`) when every gate sits exactly one level
above each vertex it reads: `C.depthAt a + 1 = C.depthAt (n + i)` for every argument `a` of gate
`i`.  Inputs are at level `0` and fan-in-0 gates at level `1`, so a layered circuit evaluates
level by level.

The conversion `BoolCircuit.DAGCircuit.layerNAND` takes a NAND-form circuit `C` on `n ≥ 1` inputs
to a layered NAND-form circuit on the `2n` **literals** `x, ¬x` (`BoolCircuit.litInput`), of the
same depth and function.

**Why literals (the odd-gap finding).** Call a vertex's depth its level.  In a layered NAND
circuit whose only level-0 vertices are the positive inputs, induction on the level shows that
every vertex at an even level computes a monotone function and every vertex at an odd level an
antimonotone one (constants are both; the NAND of antimonotone functions is monotone, and
conversely).  XOR is neither, so over positive inputs no layering exists in general: an odd gap
cannot always be padded.  With both literals at level `0` every vertex is available at both
parities.  Literal inputs are Bar89's "inputs and negated inputs" [Bar89, Thm 1, p003-b002].

**Construction** (computable, by columns in topological order; no NAND-form hypothesis).  Write
`D := C.depth` and `δ := C.depthAt v`.  Each old vertex `v` with `δ ≤ D` gets a *column* of new
vertices `v@k`, one for every level `δ ≤ k ≤ D`, with `v@k` at depth exactly `k`:
* **base** `v@δ`: an input `xᵢ` is input vertex `i`; a gate is a NAND gate over its arguments'
  copies `a@(δ - 1)`;
* **parity twin** `v@(δ + 1)`: an input's twin is `NAND(¬xᵢ)`, reading input vertex `n + i`; a
  gate's twin is the same NAND gate over `a@δ`; a fan-in-0 gate's twin is `NAND(NAND(x₀, ¬x₀))`,
  which needs `n ≥ 1`;
* **double-NAND chain** `v@k = NAND(NAND(v@(k - 2)))` for `k ≥ δ + 2`, the inner gate at level
  `k - 1`.

Every gate is emitted as a NAND gate `⟨.not, args⟩`.  Old vertices deeper than `D` are dead and
get no column.  The output is `out@D`.  The gate list (`layerGates`) and output vertex
(`layerOutput`) are definitions; the structure fields of `DAGCircuit` (acyclicity, output in
range) are the targets N12–N13, as N2 is for `toNANDForm`; they are proved here, structurally
(no NAND-form hypothesis, no admitted lemma), so no admission reaches `layerNAND` through them.

**Column invariant** (the plan of every target's fill): after the fold has processed the old
vertices `0, …, v - 1`, for every processed `u` with `C.depthAt u ≤ D` and every level
`C.depthAt u ≤ k ≤ D`, the recorded vertex `u@k` exists below the current vertex count, has depth
exactly `k`, reads only vertices of depth `k - 1`, and, when `C.IsNANDForm`, has on
`litInput x` the value of `u` on `x`; the column of `u` has at most `2 (D - C.depthAt u) + 1`
gates.  It is proved by induction along the fold.

**Not reused.** `DAGCircuit.toLayered` and `TreeCircuit.toLayered` (`LayeredDAG.lean`) map into
the other model `LayeredCircuit` with one vertex per layer (depth = number of gates) and need
`IsWellFormed` and no `∨`; the conversion here keeps the `DAGCircuit` model and its depth, and is
named `layerNAND`, not `toLayered`.  It is not an instance of `DAGCircuit.rewrite`: the input
count changes and the depth must be exact, not bounded.  The column fold is a construction, not
a host: its contract does not vary by consumer.

No ingested passage defines layered circuits or a layering conversion: the conversion is glue,
motivated by the level-by-level evaluation of [BV11, Thm 3.1, p015-b001; Def 3.6, p014-b001]
("depth-`L` binary arithmetic circuits", an evaluation key whose length depends on `L`).

## Main definitions

* `BoolCircuit.DAGCircuit.IsLayered` — every gate is one level above each vertex it reads.
* `BoolCircuit.litInput` — the `2n` literals of an input.
* `BoolCircuit.layerChain`, `BoolCircuit.DAGCircuit.layerAt`, `BoolCircuit.DAGCircuit.layerColumn`,
  `BoolCircuit.DAGCircuit.layerFold` — the column builder.
* `BoolCircuit.DAGCircuit.layerGates`, `BoolCircuit.DAGCircuit.layerOutput` — the gates and the
  output vertex of the layering.
* `BoolCircuit.DAGCircuit.layerNAND` — the layering conversion.

## Main results

All are statement-phase targets (glue):
* `BoolCircuit.DAGCircuit.layerGates_acyclic`, `layerOutput_lt` (N12–N13) — the structure fields.
* `BoolCircuit.DAGCircuit.layerNAND_eval` (N7) — semantics on the literal input.
* `BoolCircuit.DAGCircuit.layerNAND_isLayered` (N8), `layerNAND_isNANDForm` (N9).
* `BoolCircuit.DAGCircuit.layerNAND_depth` (N10) — depth preserved exactly.
* `BoolCircuit.DAGCircuit.layerNAND_size_le` (N11) — size `≤ 2n + (2 · depth + 1) · size`.

## References

* [Bar89] D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize
  exactly those languages in NC¹*, J. Comput. System Sci. 38(1):150–164, 1989.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient fully homomorphic encryption from (standard)
  LWE*, FOCS 2011 (full version).
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

variable {n : ℕ}

/-! ## Layered circuits and literal inputs -/

/-- `C` is *layered*: every gate sits exactly one level above each vertex it reads,
`C.depthAt a + 1 = C.depthAt (n + i)` for every argument `a` of every gate `i` (inputs at level
`0`).  Glue, motivated by the level-by-level evaluation of [BV11, Thm 3.1, p015-b001;
Def 3.6, p014-b001]. -/
def DAGCircuit.IsLayered (C : DAGCircuit n) : Prop :=
  ∀ (i : ℕ) (hi : i < C.gates.length), ∀ a ∈ (C.gates[i]).args,
    C.depthAt a + 1 = C.depthAt (n + i)

/-- Layeredness unfolded: `C.IsLayered ↔ ∀ i (hi : i < C.gates.length), ∀ a ∈ (C.gates[i]).args,
C.depthAt a + 1 = C.depthAt (n + i)`. -/
theorem DAGCircuit.isLayered_iff (C : DAGCircuit n) :
    C.IsLayered ↔ ∀ (i : ℕ) (hi : i < C.gates.length), ∀ a ∈ (C.gates[i]).args,
      C.depthAt a + 1 = C.depthAt (n + i) :=
  Iff.rfl

instance DAGCircuit.decidableIsLayered (C : DAGCircuit n) : Decidable C.IsLayered :=
  @Nat.decidableBallLT C.gates.length
    (fun i hi => ∀ a ∈ (C.gates[i]).args, C.depthAt a + 1 = C.depthAt (n + i))
    (fun i hi => List.decidableBAll _ _)

/-- The *literal input* of `x`: the `2n` literals, positive ones first,
`litInput x = Fin.append x (fun i => !x i)` (Bar89's "inputs and negated inputs"
[Bar89, Thm 1, p003-b002]). -/
def litInput (x : Fin n → Bool) : Fin (n + n) → Bool := Fin.append x fun i => !x i

/-- The literal input unfolded: `litInput x = Fin.append x (fun i => !x i)`. -/
theorem litInput_eq (x : Fin n → Bool) : litInput x = Fin.append x fun i => !x i := rfl

/-- The positive half of the literal input: `litInput x (Fin.castAdd n i) = x i`. -/
theorem litInput_castAdd (x : Fin n → Bool) (i : Fin n) : litInput x (Fin.castAdd n i) = x i := by
  rw [litInput_eq, Fin.append_left]

/-- The negative half of the literal input: `litInput x (Fin.natAdd n i) = !x i`. -/
theorem litInput_natAdd (x : Fin n → Bool) (i : Fin n) : litInput x (Fin.natAdd n i) = !x i := by
  rw [litInput_eq, Fin.append_right]

/-! ## The column builder -/

/-- The **double-NAND chain**: after the gates `gs` of a circuit with `N` inputs, with `a` and
`b` the copies of a vertex at the two levels below the next one, append `s` links; link `t`
appends the inner gate `NAND(a)` (vertex `N + |gs|`) and the outer gate `NAND(NAND(a))` (vertex
`N + |gs| + 1`), which becomes the copy two levels above `a`.  Returns the new gate list and the
outer vertices, in level order:
`layerChain N gs a b 0 = (gs, [])` and `layerChain N gs a b (s + 1) =
let r := layerChain N (gs ++ [⟨.not, [a]⟩, ⟨.not, [N + |gs|]⟩]) b (N + |gs| + 1) s;
(r.1, (N + |gs| + 1) :: r.2)`.  Glue (plan section r3 §H3.13). -/
def layerChain (N : ℕ) : List DAGGate → ℕ → ℕ → ℕ → List DAGGate × List ℕ
  | gs, _, _, 0 => (gs, [])
  | gs, a, b, s + 1 =>
    let r := layerChain N (gs ++ [⟨.not, [a]⟩, ⟨.not, [N + gs.length]⟩]) b (N + gs.length + 1) s
    (r.1, (N + gs.length + 1) :: r.2)

/-- The empty chain: `layerChain N gs a b 0 = (gs, [])`. -/
theorem layerChain_zero (N : ℕ) (gs : List DAGGate) (a b : ℕ) :
    layerChain N gs a b 0 = (gs, []) := rfl

/-- One more link: `layerChain N gs a b (s + 1) = ((layerChain N gs' b (N + |gs| + 1) s).1,
(N + |gs| + 1) :: (layerChain N gs' b (N + |gs| + 1) s).2)` with
`gs' = gs ++ [⟨.not, [a]⟩, ⟨.not, [N + |gs|]⟩]`. -/
theorem layerChain_succ (N : ℕ) (gs : List DAGGate) (a b s : ℕ) :
    layerChain N gs a b (s + 1) =
      ((layerChain N (gs ++ [⟨.not, [a]⟩, ⟨.not, [N + gs.length]⟩]) b (N + gs.length + 1) s).1,
        (N + gs.length + 1) ::
          (layerChain N (gs ++ [⟨.not, [a]⟩, ⟨.not, [N + gs.length]⟩]) b
            (N + gs.length + 1) s).2) := rfl

/-- The copy `v@k` recorded in the columns `cols` (column `v` lists `v@δ, v@(δ + 1), …` with
`δ = C.depthAt v`): `C.layerAt cols v k = (cols.getD v []).getD (k - C.depthAt v) 0`.  Glue. -/
def DAGCircuit.layerAt (C : DAGCircuit n) (cols : List (List ℕ)) (v k : ℕ) : ℕ :=
  (cols.getD v []).getD (k - C.depthAt v) 0

/-- The recorded copy unfolded: `C.layerAt cols v k = (cols.getD v []).getD (k - C.depthAt v) 0`. -/
theorem DAGCircuit.layerAt_eq (C : DAGCircuit n) (cols : List (List ℕ)) (v k : ℕ) :
    C.layerAt cols v k = (cols.getD v []).getD (k - C.depthAt v) 0 := rfl

/-- One step of the column fold: build the column of the old vertex `v` after the state
`s = (new gates, columns of 0, …, v - 1)`, over the `n + n` literal inputs.  With `D = C.depth`,
`δ = C.depthAt v` and `m = n + n + |s.1|` (the next new vertex):
* `D < δ` (dead vertex): no gate, empty column;
* `v < n` (input), `D = 0`: column `[v]`;
* `v < n`, `D ≥ 1`: twin `NAND[n + v]` (vertex `m`), then `D - 1` chain links from `(v, m)`;
  column `v :: m :: chain`;
* gate `g = C.gates.getD (v - n) ⟨.not, []⟩`: base `NAND[a@(δ - 1) | a ∈ g.args]` (vertex `m`);
  if `D = δ` the column is `[m]`; otherwise the twin is `NAND[a@δ | a ∈ g.args]` (vertex
  `m + 1`), or, when `g.args = []`, `NAND[0, n]` then `NAND[m + 1]` (twin vertex `m + 2`); then
  `D - δ - 1` chain links from `(m, twin)`; column `m :: twin :: chain`.
Glue (plan section r3 §H3.13). -/
def DAGCircuit.layerColumn (C : DAGCircuit n) (s : List DAGGate × List (List ℕ)) (v : ℕ) :
    List DAGGate × List (List ℕ) :=
  if C.depth < C.depthAt v then (s.1, s.2 ++ [[]])
  else if v < n then
    if C.depth = 0 then (s.1, s.2 ++ [[v]])
    else
      let r := layerChain (n + n) (s.1 ++ [⟨.not, [n + v]⟩]) v (n + n + s.1.length) (C.depth - 1)
      (r.1, s.2 ++ [v :: (n + n + s.1.length) :: r.2])
  else
    let g := C.gates.getD (v - n) ⟨.not, []⟩
    let m := n + n + s.1.length
    let gs₁ := s.1 ++ [⟨.not, g.args.map fun a => C.layerAt s.2 a (C.depthAt v - 1)⟩]
    if C.depth = C.depthAt v then (gs₁, s.2 ++ [[m]])
    else
      let tw : List DAGGate × ℕ :=
        if g.args = [] then (gs₁ ++ [⟨.not, [0, n]⟩, ⟨.not, [m + 1]⟩], m + 2)
        else (gs₁ ++ [⟨.not, g.args.map fun a => C.layerAt s.2 a (C.depthAt v)⟩], m + 1)
      let r := layerChain (n + n) tw.1 m tw.2 (C.depth - C.depthAt v - 1)
      (r.1, s.2 ++ [m :: tw.2 :: r.2])

/-- The fold step unfolded (`C.layerColumn s v` is the case split of its docstring).

**Proof sketch.** Definitional: `rfl`. -/
theorem DAGCircuit.layerColumn_eq (C : DAGCircuit n) (s : List DAGGate × List (List ℕ)) (v : ℕ) :
    C.layerColumn s v =
      if C.depth < C.depthAt v then (s.1, s.2 ++ [[]])
      else if v < n then
        if C.depth = 0 then (s.1, s.2 ++ [[v]])
        else
          ((layerChain (n + n) (s.1 ++ [⟨.not, [n + v]⟩]) v (n + n + s.1.length)
              (C.depth - 1)).1,
            s.2 ++ [v :: (n + n + s.1.length) ::
              (layerChain (n + n) (s.1 ++ [⟨.not, [n + v]⟩]) v (n + n + s.1.length)
                (C.depth - 1)).2])
      else
        if C.depth = C.depthAt v then
          (s.1 ++ [⟨.not, (C.gates.getD (v - n) ⟨.not, []⟩).args.map fun a =>
              C.layerAt s.2 a (C.depthAt v - 1)⟩], s.2 ++ [[n + n + s.1.length]])
        else
          let gs₁ := s.1 ++ [⟨.not, (C.gates.getD (v - n) ⟨.not, []⟩).args.map fun a =>
              C.layerAt s.2 a (C.depthAt v - 1)⟩]
          let tw : List DAGGate × ℕ :=
            if (C.gates.getD (v - n) ⟨.not, []⟩).args = [] then
              (gs₁ ++ [⟨.not, [0, n]⟩, ⟨.not, [n + n + s.1.length + 1]⟩],
                n + n + s.1.length + 2)
            else
              (gs₁ ++ [⟨.not, (C.gates.getD (v - n) ⟨.not, []⟩).args.map fun a =>
                C.layerAt s.2 a (C.depthAt v)⟩], n + n + s.1.length + 1)
          ((layerChain (n + n) tw.1 (n + n + s.1.length) tw.2
              (C.depth - C.depthAt v - 1)).1,
            s.2 ++ [(n + n + s.1.length) :: tw.2 ::
              (layerChain (n + n) tw.1 (n + n + s.1.length) tw.2
                (C.depth - C.depthAt v - 1)).2]) := rfl

/-- The column fold over the old vertices `0, …, n + |C.gates| - 1` in topological order:
`C.layerFold = (List.range (n + C.gates.length)).foldl C.layerColumn ([], [])`.  Glue. -/
def DAGCircuit.layerFold (C : DAGCircuit n) : List DAGGate × List (List ℕ) :=
  (List.range (n + C.gates.length)).foldl C.layerColumn ([], [])

/-- The column fold unfolded:
`C.layerFold = (List.range (n + C.gates.length)).foldl C.layerColumn ([], [])`. -/
theorem DAGCircuit.layerFold_eq (C : DAGCircuit n) :
    C.layerFold = (List.range (n + C.gates.length)).foldl C.layerColumn ([], []) := rfl

/-- The gate list of the layering (plan section r3 §H3.13): `C.layerGates = C.layerFold.1`, every
old vertex `v` realized at each level `C.depthAt v ≤ k ≤ C.depth` (base, parity twin, double-NAND
chain), every gate emitted as a NAND gate, columns in topological order.  Computable; glue
(no ingested source, r3 §H1 gap 4). -/
def DAGCircuit.layerGates [NeZero n] (C : DAGCircuit n) : List DAGGate := C.layerFold.1

/-- The layering's gates unfolded: `C.layerGates = C.layerFold.1`. -/
theorem DAGCircuit.layerGates_eq [NeZero n] (C : DAGCircuit n) :
    C.layerGates = C.layerFold.1 := rfl

/-- The output vertex of the layering, `out@(C.depth)`:
`C.layerOutput = C.layerAt C.layerFold.2 C.output C.depth`.  Computable; glue. -/
def DAGCircuit.layerOutput [NeZero n] (C : DAGCircuit n) : ℕ :=
  C.layerAt C.layerFold.2 C.output C.depth

/-- The layering's output unfolded: `C.layerOutput = C.layerAt C.layerFold.2 C.output C.depth`. -/
theorem DAGCircuit.layerOutput_eq [NeZero n] (C : DAGCircuit n) :
    C.layerOutput = C.layerAt C.layerFold.2 C.output C.depth := rfl

/-- The chain only extends the gate list: `gs <+: (layerChain N gs a b s).1`.  Glue. -/
private theorem layerChain_isPrefix {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ}, gs <+: (layerChain N gs a b s).1
  | 0, gs, a, b => by rw [layerChain_zero]
  | s + 1, gs, a, b => by
    rw [layerChain_succ]; exact (List.prefix_append _ _).trans layerChain_isPrefix

/-- The chain appends two gates per link:
`(layerChain N gs a b s).1.length = gs.length + 2 * s`.  Glue. -/
private theorem length_layerChain_fst {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ}, (layerChain N gs a b s).1.length = gs.length + 2 * s
  | 0, gs, a, b => by rw [layerChain_zero]; rfl
  | s + 1, gs, a, b => by
    rw [layerChain_succ, length_layerChain_fst, List.length_append]; simp; omega

/-- Every gate the chain appends reads one vertex: `g ∈ (layerChain N gs a b s).1 →
g ∈ gs ∨ ∃ w, g = ⟨.not, [w]⟩`.  Glue. -/
private theorem mem_layerChain_fst {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ} {g : DAGGate}, g ∈ (layerChain N gs a b s).1 →
      g ∈ gs ∨ ∃ w, g = ⟨.not, [w]⟩
  | 0, gs, a, b, g, hg => by rw [layerChain_zero] at hg; exact Or.inl hg
  | s + 1, gs, a, b, g, hg => by
    rw [layerChain_succ] at hg
    rcases mem_layerChain_fst hg with hg | hg
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with hg | rfl | rfl
      exacts [Or.inl hg, Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]
    · exact Or.inr hg

/-- The chain keeps a gate list acyclic, and its column `a :: b :: (outer vertices)` lies below
the vertex count, when `a` and `b` exist: `GatesAcyclic N gs → a < N + |gs| → b < N + |gs| →
GatesAcyclic N (layerChain N gs a b s).1 ∧
∀ w ∈ a :: b :: (layerChain N gs a b s).2, w < N + (layerChain N gs a b s).1.length`.  Glue. -/
private theorem layerChain_acyclic {N : ℕ} :
    ∀ {s : ℕ} {gs : List DAGGate} {a b : ℕ}, GatesAcyclic N gs → a < N + gs.length →
      b < N + gs.length → GatesAcyclic N (layerChain N gs a b s).1 ∧
        ∀ w ∈ a :: b :: (layerChain N gs a b s).2, w < N + (layerChain N gs a b s).1.length
  | 0, gs, a, b, h, ha, hb => by rw [layerChain_zero]; exact ⟨h, by simp [ha, hb]⟩
  | s + 1, gs, a, b, h, ha, hb => by
    have h2 := (h.snoc (g := ⟨.not, [a]⟩) (by simpa using ha)).snoc
      (g := ⟨.not, [N + gs.length]⟩) (by simp)
    rw [List.append_assoc] at h2
    have hl := (layerChain_isPrefix (N := N) (s := s + 1) (gs := gs) (a := a) (b := b)).length_le
    rw [layerChain_succ] at hl ⊢
    obtain ⟨h3, h4⟩ := layerChain_acyclic (s := s) (a := b) (b := N + gs.length + 1) h2
      (by simp; omega) (by simp; omega)
    refine ⟨h3, fun w hw => ?_⟩
    rcases List.mem_cons.mp hw with rfl | hw
    exacts [by omega, h4 w hw]

/-- A recorded copy is below any positive bound `B` of all column entries:
`0 < B → (∀ col ∈ cols, ∀ w ∈ col, w < B) → C.layerAt cols v k < B` (a missing copy reads as
`0`).  Glue. -/
private theorem DAGCircuit.layerAt_lt (C : DAGCircuit n) {cols : List (List ℕ)} {B : ℕ}
    (hB : 0 < B) (h : ∀ col ∈ cols, ∀ w ∈ col, w < B) (v k : ℕ) : C.layerAt cols v k < B := by
  rw [layerAt_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases hc : cols[v]? with _ | col
  · simpa using hB
  · rcases hw : col[k - C.depthAt v]? with _ | w
    · simpa [hw] using hB
    · simpa [hw] using h col (List.mem_of_getElem? hc) w (List.mem_of_getElem? hw)

/-- One fold step, structurally: if the gates `s.1` are acyclic over the `n + n` literal inputs
and every column entry of `s.2` lies below `n + n + |s.1|`, then `C.layerColumn s v` appends one
column with entries below its new vertex count, extends `s.1` (`s.1 <+: _`) acyclically by at
most `2 * C.depth + 1` gates, and keeps every gate a NAND gate when `C.IsNANDForm`.  Glue.

**Proof sketch.** Case split along `layerColumn_eq`.  Step 1: a column `a :: b :: chain` after
`p` new gates `pre` (`layerChain_acyclic`, `length_layerChain_fst`, `mem_layerChain_fst`).
A dead vertex and an input with `D = 0` add no gate; an input adds the twin `NAND[n + v]`; a
gate adds the base, reading recorded copies (`layerAt_lt`), and, below the top, the twin, reading
copies or `NAND[0, n]` then `NAND[m + 1]`.  The new gates are NAND gates by `isNAND_iff` (the
copies keep the old fan-in; the old gate is a NAND gate or the default `⟨.not, []⟩`). -/
private theorem DAGCircuit.layerColumn_struct [NeZero n] (C : DAGCircuit n)
    (s : List DAGGate × List (List ℕ)) (v : ℕ) (hacy : GatesAcyclic (n + n) s.1)
    (hcol : ∀ col ∈ s.2, ∀ w ∈ col, w < n + n + s.1.length)
    (hnand : C.IsNANDForm → ∀ g ∈ s.1, g.IsNAND) :
    (∃ col, (C.layerColumn s v).2 = s.2 ++ [col] ∧
      ∀ w ∈ col, w < n + n + (C.layerColumn s v).1.length) ∧
    s.1 <+: (C.layerColumn s v).1 ∧ GatesAcyclic (n + n) (C.layerColumn s v).1 ∧
    (C.IsNANDForm → ∀ g ∈ (C.layerColumn s v).1, g.IsNAND) ∧
    (C.layerColumn s v).1.length ≤ s.1.length + (2 * C.depth + 1) := by
  have hn : 0 < n := Nat.pos_of_neZero n
  have h1 : ∀ w : ℕ, (⟨.not, [w]⟩ : DAGGate).IsNAND := fun w =>
    (DAGGate.isNAND_iff _).mpr ⟨rfl, by simp⟩
  -- Step 1: a column `a :: b :: chain` after the `p` gates `pre`
  have hch : ∀ (pre : List DAGGate) (p a b t : ℕ), pre.length = p →
      GatesAcyclic (n + n) (s.1 ++ pre) → (C.IsNANDForm → ∀ g ∈ pre, g.IsNAND) →
      a < n + n + s.1.length + p → b < n + n + s.1.length + p → p + 2 * t ≤ 2 * C.depth + 1 →
      (∃ col, s.2 ++ [a :: b :: (layerChain (n + n) (s.1 ++ pre) a b t).2] = s.2 ++ [col] ∧
        ∀ w ∈ col, w < n + n + (layerChain (n + n) (s.1 ++ pre) a b t).1.length) ∧
      s.1 <+: (layerChain (n + n) (s.1 ++ pre) a b t).1 ∧
      GatesAcyclic (n + n) (layerChain (n + n) (s.1 ++ pre) a b t).1 ∧
      (C.IsNANDForm → ∀ g ∈ (layerChain (n + n) (s.1 ++ pre) a b t).1, g.IsNAND) ∧
      (layerChain (n + n) (s.1 ++ pre) a b t).1.length ≤ s.1.length + (2 * C.depth + 1) := by
    intro pre p a b t hp hacy' hpre ha hb ht
    obtain ⟨h3, h4⟩ := layerChain_acyclic (s := t) (a := a) (b := b) hacy'
      (by simp; omega) (by simp; omega)
    refine ⟨⟨_, rfl, h4⟩, (List.prefix_append _ _).trans layerChain_isPrefix, h3,
      fun hC g hg => ?_, by rw [length_layerChain_fst, List.length_append]; omega⟩
    rcases mem_layerChain_fst hg with hg | ⟨w, rfl⟩
    · rcases List.mem_append.mp hg with hg | hg
      exacts [hnand hC g hg, hpre hC g hg]
    · exact h1 w
  rw [layerColumn_eq]
  by_cases hd : C.depth < C.depthAt v
  · rw [if_pos hd]; exact ⟨⟨[], rfl, by simp⟩, List.prefix_refl _, hacy, hnand, by simp⟩
  rw [if_neg hd]
  by_cases hv : v < n
  · rw [if_pos hv]
    by_cases h3 : C.depth = 0
    · rw [if_pos h3]
      exact ⟨⟨[v], rfl, by simp; omega⟩, List.prefix_refl _, hacy, hnand, by simp⟩
    rw [if_neg h3]
    exact hch _ 1 _ _ _ rfl (hacy.snoc (by simp; omega))
      (fun _ g hg => by rw [List.mem_singleton.mp hg]; exact h1 _) (by omega) (by omega)
      (by omega)
  rw [if_neg hv]
  have hgN : C.IsNANDForm → (C.gates.getD (v - n) ⟨.not, []⟩).IsNAND := by
    intro hC
    rw [List.getD_eq_getElem?_getD]
    rcases hg : C.gates[v - n]? with _ | g
    · exact (DAGGate.isNAND_iff _).mpr ⟨rfl, by simp⟩
    · exact (DAGCircuit.isNANDForm_iff C).mp hC g (List.mem_of_getElem? hg)
  generalize C.gates.getD (v - n) ⟨.not, []⟩ = g at hgN ⊢
  -- the base and the twin read recorded copies, below the vertex count, and keep the fan-in
  have hb : ∀ k, (∀ w ∈ (⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩ : DAGGate).args,
      w < n + n + s.1.length) ∧
        (C.IsNANDForm → (⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩ : DAGGate).IsNAND) :=
    fun k => ⟨by
      simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact C.layerAt_lt (by omega) hcol a k,
      fun hC => (DAGGate.isNAND_iff _).mpr
        ⟨rfl, by simpa using ((DAGGate.isNAND_iff g).mp (hgN hC)).2⟩⟩
  have hacy1 := hacy.snoc (hb (C.depthAt v - 1)).1
  by_cases h4 : C.depth = C.depthAt v
  · rw [if_pos h4]
    refine ⟨⟨_, rfl, by simp⟩, List.prefix_append _ _, hacy1, fun hC g' hg' => ?_, by simp⟩
    rcases List.mem_append.mp hg' with hg' | hg'
    exacts [hnand hC g' hg', (List.mem_singleton.mp hg') ▸ (hb _).2 hC]
  rw [if_neg h4]
  dsimp only
  by_cases h5 : g.args = []
  · rw [if_pos h5]
    dsimp only
    rw [List.append_assoc]
    have h2 := (hacy1.snoc (g := ⟨.not, [0, n]⟩) (by simp; omega)).snoc
      (g := ⟨.not, [n + n + s.1.length + 1]⟩) (by simp; omega)
    exact hch _ 3 _ _ _ rfl (by simpa using h2) (fun hC g' hg' => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl
        exacts [(hb _).2 hC, (DAGGate.isNAND_iff _).mpr ⟨rfl, by simp⟩, h1 _])
      (by omega) (by omega) (by omega)
  · rw [if_neg h5]
    dsimp only
    rw [List.append_assoc]
    have h2 := hacy1.snoc (g := ⟨.not, g.args.map fun a => C.layerAt s.2 a (C.depthAt v)⟩)
      (fun w hw => by have := (hb _).1 w hw; simp; omega)
    exact hch _ 2 _ _ _ rfl (by simpa using h2) (fun hC g' hg' => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl
        exacts [(hb _).2 hC, (hb _).2 hC])
      (by omega) (by omega) (by omega)

/-- The column fold, structurally, after the old vertices `0, …, v - 1`: with
`s = (List.range v).foldl C.layerColumn ([], [])`, `s.2.length = v`, `s.1` is acyclic over the
`n + n` inputs, every column entry lies below `n + n + |s.1|`, every gate is a NAND gate when
`C.IsNANDForm`, and `s.1.length ≤ (2 * C.depth + 1) * v`.  Glue.

**Proof sketch.** Induction on `v` with `List.range_succ` and `List.foldl_append`: one step is
`layerColumn_struct`, whose hypotheses are the induction hypothesis, and whose conclusions give
the five parts for `v + 1` (the length bound adds at most `2 * C.depth + 1` gates). -/
private theorem DAGCircuit.layerFold_struct [NeZero n] (C : DAGCircuit n) (v : ℕ) :
    ((List.range v).foldl C.layerColumn ([], [])).2.length = v ∧
    GatesAcyclic (n + n) ((List.range v).foldl C.layerColumn ([], [])).1 ∧
    (∀ col ∈ ((List.range v).foldl C.layerColumn ([], [])).2, ∀ w ∈ col,
      w < n + n + ((List.range v).foldl C.layerColumn ([], [])).1.length) ∧
    (C.IsNANDForm → ∀ g ∈ ((List.range v).foldl C.layerColumn ([], [])).1, g.IsNAND) ∧
    ((List.range v).foldl C.layerColumn ([], [])).1.length ≤ (2 * C.depth + 1) * v := by
  induction v with
  | zero => exact ⟨rfl, GatesAcyclic.nil, by simp, by simp, by simp⟩
  | succ v ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range v).foldl C.layerColumn ([], []) = s at ih ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨⟨col, hc, hcw⟩, hp, ha, hn, hl⟩ := C.layerColumn_struct s v h2 h3 h4
    refine ⟨by rw [hc, List.length_append, h1]; rfl, ha, fun c hc' w hw => ?_, hn,
      by rw [Nat.mul_succ]; omega⟩
    rw [hc, List.mem_append, List.mem_singleton] at hc'
    rcases hc' with hc' | rfl
    · have := h3 c hc' w hw; have := hp.length_le; omega
    · exact hcw w hw

/-! ## The structure fields (targets) -/

/-- **N12. Acyclicity of the layering.** Every gate of `C.layerGates` reads only earlier vertices
of the circuit on `n + n` inputs: `∀ (i : ℕ) (h : i < C.layerGates.length),
∀ a ∈ (C.layerGates[i]).args, a < n + n + i` (the `args_lt` field of `DAGCircuit (n + n)`, i.e.
`GatesAcyclic (n + n) C.layerGates`).  Glue.

Stated in the field's form rather than as `GatesAcyclic (n + n) C.layerGates` (plan section r3
§H5.6b): `GatesAcyclic` (`DAGCircuit.lean`) has no published reader, and filling the field from a
`GatesAcyclic` proof would unfold it (Rule 10).  The meaning is identical (the body of
`GatesAcyclic`).

**Proof sketch.** Induction along the fold (`layerFold_eq`, `List.range_succ`,
`List.foldl_append`; private `layerFold_struct`, one step `layerColumn_struct`) with the column
invariant of the module docstring, part "every recorded copy lies below the current vertex
count": each step (`layerColumn_eq`) appends gates that read `n + v` or `0, n` (inputs, below
`n + n` by `NeZero n`), recorded copies (below the count, `layerAt_lt`; a missing copy reads as
the input `0`), or the gates just appended (`layerChain_succ`: the inner gate `N + |gs|`
precedes the outer one), so `GatesAcyclic.snoc` keeps the gate list acyclic
(`layerChain_acyclic`).  The field form is `gatesAcyclic_iff`. -/
theorem DAGCircuit.layerGates_acyclic [NeZero n] (C : DAGCircuit n) :
    ∀ (i : ℕ) (h : i < C.layerGates.length), ∀ a ∈ (C.layerGates[i]).args, a < n + n + i := by
  have h := (C.layerFold_struct (n + C.gates.length)).2.1
  rw [← layerFold_eq, ← layerGates_eq] at h
  exact gatesAcyclic_iff.mp h

/-- **N13. The output is a vertex.** `C.layerOutput < (n + n) + C.layerGates.length` (the
`output_lt` field of `DAGCircuit (n + n)`).  Glue.

**Proof sketch.** The output is the recorded copy `out@D` (`layerOutput_eq`).  By the column
invariant (private `layerFold_struct` at `n + |C.gates|`, `layerFold_eq`, `layerGates_eq`)
every column entry lies below the vertex count `n + n + |C.layerGates|`, and so does every
recorded copy (`layerAt_lt`: a missing copy reads as the input `0`, below `n + n` by
`NeZero n`). -/
theorem DAGCircuit.layerOutput_lt [NeZero n] (C : DAGCircuit n) :
    C.layerOutput < (n + n) + C.layerGates.length := by
  have h := (C.layerFold_struct (n + C.gates.length)).2.2.1
  rw [← layerFold_eq, ← layerGates_eq] at h
  rw [layerOutput_eq]
  exact C.layerAt_lt (by have := Nat.pos_of_neZero n; omega) h _ _

/-! ## The conversion -/

/-- **The layering conversion** (plan section r3 §H3.13): the circuit on the `n + n` literal
inputs with gates `C.layerGates` and output `C.layerOutput`,
`C.layerNAND = ⟨C.layerGates, C.layerOutput, N12, N13⟩` (field readers `layerNAND_gates`,
`layerNAND_output`, generated by `simps`, not `@[simp]`).  While N12 and N13 are admitted,
`sorryAx` reaches it through them only.  Glue (no ingested source, r3 §H1 gap 4); motivated by
[BV11, Thm 3.1, p015-b001; Def 3.6, p014-b001]. -/
@[simps (config := { isSimp := false }) gates output]
def DAGCircuit.layerNAND [NeZero n] (C : DAGCircuit n) : DAGCircuit (n + n) where
  gates := C.layerGates
  output := C.layerOutput
  args_lt := C.layerGates_acyclic
  output_lt := C.layerOutput_lt

section LayerNAND

variable [NeZero n] (C : DAGCircuit n)

/-- Under `C.IsNANDForm`, every gate of the layering is a NAND gate:
`C.IsNANDForm → ∀ g ∈ C.layerGates, g.IsNAND`.  Glue. -/
private theorem DAGCircuit.layerGates_isNAND (hC : C.IsNANDForm) :
    ∀ g ∈ C.layerGates, g.IsNAND := by
  have h := (C.layerFold_struct (n + C.gates.length)).2.2.2.1 hC
  rwa [← layerFold_eq, ← layerGates_eq] at h

/-- A list of naturals all of whose entries equal `k`, with an entry `y₀`, has `foldr max 0`
equal to `k`: `(∀ y ∈ l, y = k) → y₀ ∈ l → l.foldr max 0 = k`, from Mathlib's
`List.max_le_of_forall_le` and `List.le_max_of_le` (`⊥ = 0` on `ℕ`).  Glue. -/
private theorem foldr_max_eq_of_forall {l : List ℕ} {k y₀ : ℕ} (h : ∀ y ∈ l, y = k)
    (h₀ : y₀ ∈ l) : l.foldr max 0 = k := by
  rw [← Nat.bot_eq_zero]
  exact le_antisymm (List.max_le_of_forall_le l k fun y hy => (h y hy).le)
    (List.le_max_of_le h₀ (h y₀ h₀).ge)

/-- The depth of a gate `g` of the layering, read off a prefix `gs ++ [g]` of its gate list:
`gs ++ [g] <+: C.layerNAND.gates → C.layerNAND.depthAt (n + n + gs.length) =
1 + (g.args.map C.layerNAND.depthAt).foldr max 0`.  Glue. -/
private theorem DAGCircuit.layerNAND_depthAt_snoc {gs : List DAGGate} {g : DAGGate}
    (h : gs ++ [g] <+: C.layerNAND.gates) :
    C.layerNAND.depthAt (n + n + gs.length) =
      1 + (g.args.map C.layerNAND.depthAt).foldr max 0 := by
  have hi : gs.length < (gs ++ [g]).length := by simp
  have hd : (fun a => C.layerNAND.depths.getD a 0) = C.layerNAND.depthAt :=
    funext fun a => (C.layerNAND.depthAt_eq a).symm
  rw [C.layerNAND.depthAt_gate (lt_of_lt_of_le hi h.length_le), DAGGate.depth_eq,
    ← h.getElem hi, List.getElem_concat_length rfl, hd]

/-- The value of a gate `g` of the layering, read off a prefix `gs ++ [g]` of its gate list, when
`C.IsNANDForm`: `(C.layerNAND.values y).getD (n + n + gs.length) false =
!(g.args.all fun a => (C.layerNAND.values y).getD a false)`.  Glue. -/
private theorem DAGCircuit.layerNAND_values_snoc (hC : C.IsNANDForm) {gs : List DAGGate}
    {g : DAGGate} (h : gs ++ [g] <+: C.layerNAND.gates) (y : Fin (n + n) → Bool) :
    (C.layerNAND.values y).getD (n + n + gs.length) false =
      !(g.args.all fun a => (C.layerNAND.values y).getD a false) := by
  have hi : gs.length < (gs ++ [g]).length := by simp
  have hmem : g ∈ C.layerGates := by rw [← layerNAND_gates]; exact h.subset (by simp)
  rw [C.layerNAND.values_getD_gate y (lt_of_lt_of_le hi h.length_le), ← h.getElem hi,
    List.getElem_concat_length rfl, DAGGate.eval_of_isNAND (C.layerGates_isNAND hC g hmem)]

/-- A one-argument gate `NAND[w]` of the layering, read off a prefix `gs ++ [NAND[w]]`:
`C.layerNAND.depthAt (n + n + gs.length) = C.layerNAND.depthAt w + 1` and, when `C.IsNANDForm`,
its value is `!(C.layerNAND.values y).getD w false`.  Glue. -/
private theorem DAGCircuit.layerNAND_single {gs : List DAGGate} {w : ℕ}
    (h : gs ++ [⟨.not, [w]⟩] <+: C.layerNAND.gates) :
    C.layerNAND.depthAt (n + n + gs.length) = C.layerNAND.depthAt w + 1 ∧
      (C.IsNANDForm → ∀ y, (C.layerNAND.values y).getD (n + n + gs.length) false =
        !(C.layerNAND.values y).getD w false) := by
  refine ⟨?_, fun hC y => ?_⟩
  · rw [C.layerNAND_depthAt_snoc h]; simp; omega
  · rw [C.layerNAND_values_snoc hC h]; simp

/-- The literal inputs of the layering, read as old values: for `u < n`, input vertex `u` holds
`(C.values x).getD u false` and input vertex `n + u` its negation, on `litInput x`.  Glue. -/
private theorem DAGCircuit.layerNAND_values_lit {u : ℕ} (hu : u < n) (x : Fin n → Bool) :
    (C.layerNAND.values (litInput x)).getD u false = (C.values x).getD u false ∧
    (C.layerNAND.values (litInput x)).getD (n + u) false = !(C.values x).getD u false := by
  have h0 := C.values_getD_input x ⟨u, hu⟩
  have h1 := C.layerNAND.values_getD_input (litInput x) (Fin.castAdd n ⟨u, hu⟩)
  have h2 := C.layerNAND.values_getD_input (litInput x) (Fin.natAdd n ⟨u, hu⟩)
  rw [litInput_castAdd] at h1
  rw [litInput_natAdd] at h2
  exact ⟨h1.trans h0.symm, h2.trans (congrArg (!·) h0.symm)⟩

/-- The double-NAND chain realizes a column: for a vertex predicate `P` (vertex, level) that
every link `NAND(NAND(a))` (two consecutive gates of `G` after `gs`) lifts two levels, if the
chain's gates are a prefix of `G`, `P a L` and `P b (L + 1)`, then
`P ((a :: b :: (layerChain N gs a b s).2).getD j 0) (L + j)` for every `j ≤ s + 1`.  Glue. -/
private theorem layerChain_col {G : List DAGGate} {N : ℕ} {P : ℕ → ℕ → Prop}
    (hstep : ∀ (gs : List DAGGate) (a L : ℕ),
      gs ++ [⟨.not, [a]⟩, ⟨.not, [N + gs.length]⟩] <+: G → P a L →
        P (N + gs.length + 1) (L + 2)) :
    ∀ {s : ℕ} {gs : List DAGGate} {a b L : ℕ}, (layerChain N gs a b s).1 <+: G → P a L →
      P b (L + 1) → ∀ j ≤ s + 1, P ((a :: b :: (layerChain N gs a b s).2).getD j 0) (L + j)
  | 0, gs, a, b, L, _, ha, hb, j, hj => by
    rw [layerChain_zero]
    rcases j with _ | _ | j
    exacts [ha, hb, by omega]
  | s + 1, gs, a, b, L, hpre, ha, hb, j, hj => by
    rw [layerChain_succ] at hpre ⊢
    have key := layerChain_col hstep hpre hb (hstep gs a L (layerChain_isPrefix.trans hpre) ha)
    rcases j with _ | j
    · exact ha
    · rw [List.getD_cons_succ, show L + (j + 1) = L + 1 + j by omega]
      exact key j (by omega)

/-- One link of the chain over the layering keeps the column invariant of an old vertex `u`:
if `gs ++ [NAND[a], NAND[n + n + |gs|]]` is a prefix of the layering's gates, then
`C.layerNAND.depthAt a = L → C.layerNAND.depthAt (n + n + gs.length + 1) = L + 2`, and the outer
vertex keeps the value of `u` on every literal input when `a` has it (`C.IsNANDForm`).  Glue. -/
private theorem DAGCircuit.layerNAND_link (u : ℕ) {gs : List DAGGate} {a L : ℕ}
    (hp : gs ++ [⟨.not, [a]⟩, ⟨.not, [n + n + gs.length]⟩] <+: C.layerNAND.gates)
    (ha : C.layerNAND.depthAt a = L ∧ (C.IsNANDForm → ∀ x,
      (C.layerNAND.values (litInput x)).getD a false = (C.values x).getD u false)) :
    C.layerNAND.depthAt (n + n + gs.length + 1) = L + 2 ∧ (C.IsNANDForm → ∀ x,
      (C.layerNAND.values (litInput x)).getD (n + n + gs.length + 1) false =
        (C.values x).getD u false) := by
  have hp2 : gs ++ [⟨.not, [a]⟩] ++ [⟨.not, [n + n + gs.length]⟩] <+: C.layerNAND.gates := by
    simpa using hp
  obtain ⟨d1, v1⟩ := C.layerNAND_single ((List.prefix_append _ _).trans hp2)
  obtain ⟨d2, v2⟩ := C.layerNAND_single hp2
  have hl : n + n + (gs ++ [(⟨.not, [a]⟩ : DAGGate)]).length = n + n + gs.length + 1 := by
    simp; omega
  rw [hl] at d2 v2
  exact ⟨by omega, fun hC x => by rw [v2 hC, v1 hC, Bool.not_not]; exact ha.2 hC x⟩

/-- One fold step, semantically, over the layering `C.layerNAND` (whose gates extend those of
the step, `hpre`): if every recorded copy `u@k` of an earlier live vertex `u < v` has depth `k`
and, under `C.IsNANDForm`, the value of `u` on every literal input, then so has every copy
`v@k` of the new column, for `C.depthAt v ≤ k ≤ C.depth`; and every new gate reads vertices of
one common depth.  Glue.

**Proof sketch.** Case split along `layerColumn_eq`, the copies of `v` read off with
`layerAt_eq` and `List.getD_append_right`.  Step 1: a column `a :: b :: chain` after new gates
`pre`, by `layerChain_col` with `layerNAND_link`.  Step 2: an input `v` (`depthAt_input`) is
`v@0`, and its twin `NAND[n + v]` has depth `1` and value `!!xᵥ` (`layerNAND_single`,
`layerNAND_values_lit`).  Step 3: a gate `v = n + j` of depth `δ` reads earlier, shallower
vertices (`depthAt_gate`, `DAGGate.depth_eq`, `C.args_lt`, `DAGGate.getD_lt_depth`) and is a
NAND of their values (`values_getD_gate`, `DAGGate.eval_of_isNAND`).  Step 4: a NAND gate over
copies at one level `k` has depth `k + 1` (`foldr_max_eq_of_forall`) and the gate's value
(`all_congr_mem`); this gives the base `v@δ` (level `δ - 1`; a fan-in-0 base has depth
`1 = δ`) and the twin (level `δ`).  Step 5: a fan-in-0 twin `NAND(NAND(x₀, ¬x₀))` has depth `2`
and value `false`. -/
private theorem DAGCircuit.layerColumn_sem (s : List DAGGate × List (List ℕ)) (v : ℕ)
    (hv : v < n + C.gates.length) (hlen : s.2.length = v)
    (hpre : (C.layerColumn s v).1 <+: C.layerNAND.gates)
    (hsem : ∀ u < v, C.depthAt u ≤ C.depth → ∀ k, C.depthAt u ≤ k → k ≤ C.depth →
      C.layerNAND.depthAt (C.layerAt s.2 u k) = k ∧ (C.IsNANDForm → ∀ x,
        (C.layerNAND.values (litInput x)).getD (C.layerAt s.2 u k) false =
          (C.values x).getD u false)) :
    (C.depthAt v ≤ C.depth → ∀ k, C.depthAt v ≤ k → k ≤ C.depth →
      C.layerNAND.depthAt (C.layerAt (C.layerColumn s v).2 v k) = k ∧ (C.IsNANDForm → ∀ x,
        (C.layerNAND.values (litInput x)).getD (C.layerAt (C.layerColumn s v).2 v k) false =
          (C.values x).getD v false)) ∧
    ∀ g ∈ (C.layerColumn s v).1, g ∈ s.1 ∨ ∃ k, ∀ a ∈ g.args, C.layerNAND.depthAt a = k := by
  have hn : 0 < n := Nat.pos_of_neZero n
  let P : ℕ → ℕ → Prop := fun w k => C.layerNAND.depthAt w = k ∧ (C.IsNANDForm → ∀ x,
    (C.layerNAND.values (litInput x)).getD w false = (C.values x).getD v false)
  have hcol : ∀ (col : List ℕ) (k : ℕ),
      C.layerAt (s.2 ++ [col]) v k = col.getD (k - C.depthAt v) 0 := fun col k => by
    rw [layerAt_eq, List.getD_append_right _ _ _ _ hlen.le, hlen, Nat.sub_self,
      List.getD_cons_zero]
  have hU : ∀ w : ℕ, ∃ k, ∀ a ∈ (⟨.not, [w]⟩ : DAGGate).args, C.layerNAND.depthAt a = k :=
    fun w => ⟨_, fun a ha => by rw [List.mem_singleton.mp ha]⟩
  -- Step 1: a column `a :: b :: chain` after the new gates `pre`
  have hfin : ∀ (pre : List DAGGate) (a b t : ℕ), (layerChain (n + n) (s.1 ++ pre) a b t).1 <+:
      C.layerNAND.gates → P a (C.depthAt v) → P b (C.depthAt v + 1) →
      (∀ g ∈ pre, ∃ k, ∀ a ∈ g.args, C.layerNAND.depthAt a = k) →
      C.depth = C.depthAt v + t + 1 →
      (C.depthAt v ≤ C.depth → ∀ k, C.depthAt v ≤ k → k ≤ C.depth →
        P (C.layerAt (s.2 ++ [a :: b :: (layerChain (n + n) (s.1 ++ pre) a b t).2]) v k) k) ∧
      ∀ g ∈ (layerChain (n + n) (s.1 ++ pre) a b t).1, g ∈ s.1 ∨
        ∃ k, ∀ a ∈ g.args, C.layerNAND.depthAt a = k := by
    intro pre a b t hp ha hb hpre ht
    refine ⟨fun _ k hk1 hk2 => ?_, fun g hg => ?_⟩
    · rw [hcol]
      have := layerChain_col (P := P) (fun _ _ _ hp ha => C.layerNAND_link v hp ha) hp ha hb
        (k - C.depthAt v) (by omega)
      rwa [Nat.add_sub_of_le hk1] at this
    · rcases mem_layerChain_fst hg with hg | ⟨w, rfl⟩
      · rcases List.mem_append.mp hg with hg | hg
        exacts [Or.inl hg, Or.inr (hpre g hg)]
      · exact Or.inr (hU w)
  rw [layerColumn_eq] at hpre ⊢
  by_cases h1 : C.depth < C.depthAt v
  · rw [if_pos h1]
    exact ⟨fun h => absurd h (by omega), fun g hg => Or.inl hg⟩
  rw [if_neg h1] at hpre ⊢
  by_cases h2 : v < n
  · -- Step 2: an input vertex
    rw [if_pos h2] at hpre ⊢
    have hv0 : P v (C.depthAt v) :=
      ⟨(by rw [C.depthAt_input h2]; exact C.layerNAND.depthAt_input (by omega)),
        fun _ x => (C.layerNAND_values_lit h2 x).1⟩
    by_cases h3 : C.depth = 0
    · rw [if_pos h3]
      refine ⟨fun _ k hk1 hk2 => ?_, fun g hg => Or.inl hg⟩
      rw [hcol, show k - C.depthAt v = 0 by omega, List.getD_cons_zero,
        show k = C.depthAt v by omega]
      exact hv0
    rw [if_neg h3] at hpre ⊢
    obtain ⟨d1, v1⟩ := C.layerNAND_single (layerChain_isPrefix.trans hpre)
    exact hfin _ _ _ _ hpre hv0 ⟨by rw [d1, C.layerNAND.depthAt_input (by omega),
      C.depthAt_input h2], fun hC x => by
        rw [v1 hC, (C.layerNAND_values_lit h2 x).2, Bool.not_not]⟩
      (fun g hg => by rw [List.mem_singleton.mp hg]; exact hU _)
      (by rw [C.depthAt_input h2]; omega)
  -- Step 3: a gate vertex `v = n + j`: its depth, arguments and value
  rw [if_neg h2] at hpre ⊢
  obtain ⟨j, rfl⟩ : ∃ j, v = n + j := ⟨v - n, by omega⟩
  have hj : j < C.gates.length := by omega
  rw [show n + j - n = j by omega, List.getD_eq_getElem _ _ hj] at hpre ⊢
  have hδ : C.depthAt (n + j) =
      1 + ((C.gates[j]).args.map fun a => C.depths.getD a 0).foldr max 0 := by
    rw [C.depthAt_gate hj, DAGGate.depth_eq]
  have harg : ∀ a ∈ (C.gates[j]).args, a < n + j ∧ C.depthAt a < C.depthAt (n + j) :=
    fun a ha => ⟨C.args_lt j hj a ha, by
      rw [C.depthAt_eq a, C.depthAt_gate hj]; exact DAGGate.getD_lt_depth _ _ ha⟩
  have hval : C.IsNANDForm → ∀ x, (C.values x).getD (n + j) false =
      !((C.gates[j]).args.all fun a => (C.values x).getD a false) := fun hC x => by
    rw [C.values_getD_gate x hj,
      DAGGate.eval_of_isNAND ((C.isNANDForm_iff).mp hC _ (List.getElem_mem hj))]
  generalize C.gates[j] = g at hδ harg hval hpre ⊢
  -- Step 4: a NAND gate over the copies at one level `k` of the arguments
  have hlev := fun k (hk : ∀ a ∈ g.args, C.depthAt a ≤ k) (hkD : k ≤ C.depth) a
    (ha : a ∈ g.args) => hsem a (harg a ha).1 (le_trans (hk a ha) hkD) k (hk a ha) hkD
  have hgate : ∀ (gs : List DAGGate) (k : ℕ),
      gs ++ [⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩] <+: C.layerNAND.gates →
      g.args ≠ [] → (∀ a ∈ g.args, C.depthAt a ≤ k) → k ≤ C.depth →
      C.layerNAND.depthAt (n + n + gs.length) = k + 1 ∧ (C.IsNANDForm → ∀ x,
        (C.layerNAND.values (litInput x)).getD (n + n + gs.length) false =
          (C.values x).getD (n + j) false) := by
    intro gs k hp hne hk hkD
    refine ⟨?_, fun hC x => ?_⟩
    · obtain ⟨a₀, ha₀⟩ := List.exists_mem_of_ne_nil _ hne
      rw [C.layerNAND_depthAt_snoc hp, List.map_map,
        foldr_max_eq_of_forall (k := k) (fun y hy => ?_) (List.mem_map_of_mem ha₀)]
      · omega
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
        exact (hlev k hk hkD a ha).1
    · rw [C.layerNAND_values_snoc hC hp, List.all_map, hval hC x]
      exact congrArg (!·) (all_congr_mem fun a ha => (hlev k hk hkD a ha).2 hC x)
  have hbu : ∀ k, (∀ a ∈ g.args, C.depthAt a ≤ k) → k ≤ C.depth →
      ∃ k', ∀ b ∈ (⟨.not, g.args.map fun a => C.layerAt s.2 a k⟩ : DAGGate).args,
        C.layerNAND.depthAt b = k' := fun k hk hkD => ⟨k, fun b hb => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (hlev k hk hkD a ha).1⟩
  have hδ1 : 1 ≤ C.depthAt (n + j) := by omega
  have hk1 : ∀ a ∈ g.args, C.depthAt a ≤ C.depthAt (n + j) - 1 := fun a ha => by
    have := (harg a ha).2; omega
  set b0 : DAGGate := ⟨.not, g.args.map fun a => C.layerAt s.2 a (C.depthAt (n + j) - 1)⟩
    with hb0
  have hbase : s.1 ++ [b0] <+: C.layerNAND.gates → C.depthAt (n + j) ≤ C.depth →
      P (n + n + s.1.length) (C.depthAt (n + j)) := by
    intro hp hD
    by_cases h5 : g.args = []
    · refine ⟨?_, fun hC x => ?_⟩
      · rw [C.layerNAND_depthAt_snoc hp, hδ, hb0, h5]; simp
      · rw [C.layerNAND_values_snoc hC hp, hval hC x, hb0, h5]; simp
    · have := hgate s.1 _ hp h5 hk1 (by omega)
      rwa [Nat.sub_add_cancel hδ1] at this
  by_cases h4 : C.depth = C.depthAt (n + j)
  · rw [if_pos h4] at hpre ⊢
    refine ⟨fun _ k hk1 hk2 => ?_, fun g' hg' => ?_⟩
    · rw [hcol, show k - C.depthAt (n + j) = 0 by omega, List.getD_cons_zero,
        show k = C.depthAt (n + j) by omega]
      exact hbase hpre (by omega)
    · rcases List.mem_append.mp hg' with hg' | hg'
      exacts [Or.inl hg', Or.inr ((List.mem_singleton.mp hg') ▸ hbu _ hk1 (by omega))]
  -- Step 5: the parity twin `v@(δ + 1)`, then the chain
  rw [if_neg h4] at hpre ⊢
  dsimp only at hpre ⊢
  by_cases h5 : g.args = []
  · rw [if_pos h5] at hpre ⊢
    dsimp only at hpre ⊢
    have hp' : s.1 ++ [b0] ++ [⟨.not, [0, n]⟩] ++ [⟨.not, [n + n + s.1.length + 1]⟩] <+:
        C.layerNAND.gates := by rw [List.append_assoc _ [_]]; exact layerChain_isPrefix.trans hpre
    have hp1 := (List.prefix_append _ _).trans hp'
    have e1 : n + n + (s.1 ++ [b0]).length = n + n + s.1.length + 1 := by simp; omega
    have e2 : n + n + (s.1 ++ [b0] ++ [(⟨.not, [0, n]⟩ : DAGGate)]).length =
        n + n + s.1.length + 2 := by simp; omega
    have d1 := C.layerNAND_depthAt_snoc hp1
    obtain ⟨d2, v2⟩ := C.layerNAND_single hp'
    rw [e1] at d1
    rw [e2] at d2 v2
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero,
      C.layerNAND.depthAt_input (show 0 < n + n by omega),
      C.layerNAND.depthAt_input (show n < n + n by omega)] at d1
    have ht : P (n + n + s.1.length + 2) (C.depthAt (n + j) + 1) := by
      refine ⟨by rw [hδ, h5]; simp; omega, fun hC x => ?_⟩
      have v1 := C.layerNAND_values_snoc hC hp1 (litInput x)
      have hl := C.layerNAND_values_lit hn x
      rw [Nat.add_zero] at hl
      rw [e1] at v1
      simp only [List.all_cons, List.all_nil, Bool.and_true, hl.1, hl.2] at v1
      rw [v2 hC, v1, hval hC x, h5]
      simp
    rw [List.append_assoc] at hpre ⊢
    exact hfin _ _ _ _ hpre (hbase ((List.prefix_append _ _).trans hp1) (by omega)) ht
      (fun g' hg' => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl
        exacts [hbu _ hk1 (by omega), ⟨0, fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl <;> exact C.layerNAND.depthAt_input (by omega)⟩, hU _])
      (by omega)
  · rw [if_neg h5] at hpre ⊢
    dsimp only at hpre ⊢
    have hp' := layerChain_isPrefix.trans hpre
    have ht := hgate _ (C.depthAt (n + j)) hp' h5 (fun a ha => (harg a ha).2.le) (by omega)
    rw [show (s.1 ++ [b0]).length = s.1.length + 1 by simp, ← add_assoc] at ht
    rw [List.append_assoc] at hpre ⊢
    exact hfin _ _ _ _ hpre (hbase ((List.prefix_append _ _).trans hp') (by omega)) ht
      (fun g' hg' => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl
        exacts [hbu _ hk1 (by omega), hbu _ (fun a ha => (harg a ha).2.le) (by omega)])
      (by omega)

/-- The column fold, semantically, over the layering `C.layerNAND`: for
`s = (List.range v).foldl C.layerColumn ([], [])` with `v ≤ n + |C.gates|` and `s.1` a prefix
of the layering's gates, every copy `u@k` (`u < v`, `C.depthAt u ≤ k ≤ C.depth`) has depth `k`
and, under `C.IsNANDForm`, the value of `u` on every literal input; and every gate of `s.1`
reads vertices of one common depth.  Glue.

**Proof sketch.** Induction on `v` with `List.range_succ`: `layerColumn_struct` for the shape of a
step, the induction hypothesis on the prefix, `List.getD_append` for the earlier copies, and
`layerColumn_sem` for the new column. -/
private theorem DAGCircuit.layerFold_sem (v : ℕ) (hv : v ≤ n + C.gates.length)
    (hpre : ((List.range v).foldl C.layerColumn ([], [])).1 <+: C.layerNAND.gates) :
    (∀ u < v, C.depthAt u ≤ C.depth → ∀ k, C.depthAt u ≤ k → k ≤ C.depth →
      C.layerNAND.depthAt (C.layerAt ((List.range v).foldl C.layerColumn ([], [])).2 u k) = k ∧
      (C.IsNANDForm → ∀ x, (C.layerNAND.values (litInput x)).getD
        (C.layerAt ((List.range v).foldl C.layerColumn ([], [])).2 u k) false =
          (C.values x).getD u false)) ∧
    ∀ g ∈ ((List.range v).foldl C.layerColumn ([], [])).1, ∃ k, ∀ a ∈ g.args,
      C.layerNAND.depthAt a = k := by
  induction v with
  | zero => exact ⟨fun u hu => absurd hu (Nat.not_lt_zero u), fun g hg => by simp at hg⟩
  | succ v ih =>
    have hst := C.layerFold_struct v
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hpre ⊢
    generalize (List.range v).foldl C.layerColumn ([], []) = s at ih hst hpre ⊢
    obtain ⟨h1, h2, h3, h4, -⟩ := hst
    obtain ⟨⟨col, hc, -⟩, hp, -, -, -⟩ := C.layerColumn_struct s v h2 h3 h4
    obtain ⟨ih1, ih2⟩ := ih (by omega) (hp.trans hpre)
    obtain ⟨hn1, hn2⟩ := C.layerColumn_sem s v (by omega) h1 hpre ih1
    refine ⟨fun u hu hud k hk1 hk2 => ?_, fun g hg => (hn2 g hg).elim (ih2 g) id⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
    · rw [hc, layerAt_eq, List.getD_append _ _ _ _ (by omega), ← layerAt_eq]
      exact ih1 u hu hud k hk1 hk2
    · exact hn1 hud k hk1 hk2

/-- **N7. Semantics on the literal input.** For a NAND-form circuit the layering computes the same
function on the literals: `C.IsNANDForm → C.layerNAND.eval (litInput x) = C.eval x`.  Glue.

**Proof sketch.** The column invariant, value part, at the output: by induction along the fold,
every recorded copy `v@k` has on `litInput x` the value of `v` on `x`.  Inputs: `v@0` is input
vertex `v` (`DAGCircuit.values_getD_input`, `litInput_castAdd`); the twin `NAND(¬xᵥ)` reads
vertex `n + v` (`litInput_natAdd`) and gives `!!xᵥ = xᵥ` (`DAGGate.eval_of_isNAND`, N1).
Gates: the old gate is a NAND gate (`DAGCircuit.isNANDForm_iff`, `DAGGate.eval_of_isNAND`) and
the base and twin read copies with the same values (`DAGCircuit.values_getD_gate`); a fan-in-0
twin gives `!(!(x₀ && !x₀)) = false`.  A chain link gives `!!b = b`.  The induction is the
private `layerFold_sem` (one step `layerColumn_sem`, links `layerChain_col`, `layerNAND_link`);
read off at the live output `out@D` (`C.output_lt`, `DAGCircuit.depth_eq`) with
`DAGCircuit.eval_eq`, `layerNAND_output` and `layerOutput_eq`. -/
theorem DAGCircuit.layerNAND_eval (hC : C.IsNANDForm) (x : Fin n → Bool) :
    C.layerNAND.eval (litInput x) = C.eval x := by
  have hfin := C.layerFold_sem (n + C.gates.length) le_rfl
    (by rw [layerNAND_gates, layerGates_eq, layerFold_eq])
  rw [← layerFold_eq] at hfin
  rw [DAGCircuit.eval_eq C.layerNAND, DAGCircuit.eval_eq C, layerNAND_output, layerOutput_eq]
  exact (hfin.1 C.output C.output_lt C.depth_eq.ge C.depth C.depth_eq.ge le_rfl).2 hC x

/-- **N8. Layered.** `C.layerNAND.IsLayered`, with no hypothesis: every new gate reads only copies
one level down.  Glue.

**Proof sketch.** `isLayered_iff`, then the column invariant, depth part: every recorded copy
`v@k` has depth exactly `k` (`DAGCircuit.depthAt_gate`, `DAGGate.depth_eq`; the depth of a gate
does not depend on its kind, so no NAND-form hypothesis is needed), and every gate appended at
level `k` reads only vertices of depth `k - 1`: the base reads `a@(δ - 1)`, the twin `a@δ` (or
inputs `0, n` through the inner gate), a chain link `v@(k - 2)` through the inner gate at level
`k - 1`. -/
theorem DAGCircuit.layerNAND_isLayered : C.layerNAND.IsLayered := by
  have hfin := C.layerFold_sem (n + C.gates.length) le_rfl
    (by rw [layerNAND_gates, layerGates_eq, layerFold_eq])
  rw [← layerFold_eq] at hfin
  rw [← layerGates_eq, ← layerNAND_gates] at hfin
  rw [isLayered_iff]
  intro i hi a ha
  obtain ⟨k, hk⟩ := hfin.2 _ (List.getElem_mem hi)
  have hmax : ((C.layerNAND.gates[i]).args.map fun b => C.layerNAND.depths.getD b 0).foldr
      max 0 = k := foldr_max_eq_of_forall (fun y hy => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
        rw [← C.layerNAND.depthAt_eq]; exact hk b hb) (List.mem_map_of_mem ha)
  rw [C.layerNAND.depthAt_gate hi, DAGGate.depth_eq, hmax, hk a ha]
  omega

/-- **N9. NAND form.** `C.IsNANDForm → C.layerNAND.IsNANDForm`: every gate is emitted as a `¬`
gate, and the copies keep the old fan-in, so `hC` is needed for fan-in `≤ 2`.  Glue.

**Proof sketch.** `isNANDForm_iff`, `DAGGate.isNAND_iff` and `layerNAND_gates`: induction along the
fold (`layerFold_eq`, `layerColumn_eq`, `layerChain_succ`); every appended gate is
`⟨.not, args⟩` with `args` of length `1` (chain, input twin), `2` (`NAND[0, n]`) or the old
gate's fan-in (base and twin, `List.length_map`), which is at most `2` by `hC`. -/
theorem DAGCircuit.layerNAND_isNANDForm (hC : C.IsNANDForm) : C.layerNAND.IsNANDForm := by
  rw [isNANDForm_iff, layerNAND_gates]
  exact C.layerGates_isNAND hC

/-- **N10. Depth is preserved exactly.** `C.layerNAND.depth = C.depth`.  Glue.

**Proof sketch.** `DAGCircuit.depth_eq` and `layerNAND_output`: the output is `out@D` with
`D = C.depth` (`layerOutput_eq`), and by the column invariant, depth part, it has depth exactly
`D`. -/
theorem DAGCircuit.layerNAND_depth : C.layerNAND.depth = C.depth := by
  have hfin := C.layerFold_sem (n + C.gates.length) le_rfl
    (by rw [layerNAND_gates, layerGates_eq, layerFold_eq])
  rw [← layerFold_eq] at hfin
  rw [DAGCircuit.depth_eq C.layerNAND, layerNAND_output, layerOutput_eq]
  exact (hfin.1 C.output C.output_lt C.depth_eq.ge C.depth C.depth_eq.ge le_rfl).1

/-- **N11. Size.** `C.layerNAND.size ≤ 2 * n + (2 * C.depth + 1) * C.size`.  Glue.

Constant settled at the statement phase: with `D = C.depth` and `δ = C.depthAt v`, the column of
an input has `0` gates (`D = 0`) or `1 + 2 (D - 1) = 2D - 1` (twin and chain); the column of a live
gate has `1` (base) when `δ = D`, otherwise `1 + 1 + 2 (D - δ - 1) = 2 (D - δ)` gates, or
`2 (D - δ) + 1` for a fan-in-0 gate (two-gate twin); a dead vertex has none.  Every column has at
most `2D + 1` gates, so `|C.layerGates| ≤ (2D + 1) (n + |C.gates|)`, and the size is
`(n + n) + |C.layerGates| ≤ 2n + (2D + 1) · C.size`.

**Proof sketch.** `DAGCircuit.size_eq` (both circuits) and `layerNAND_gates`; induction along the
fold with the column-length part of the invariant (each step appends at most `2D + 1` gates:
`layerColumn_eq`, `layerChain` appends exactly two gates per link), summed over the
`n + |C.gates|` old vertices. -/
theorem DAGCircuit.layerNAND_size_le : C.layerNAND.size ≤ 2 * n + (2 * C.depth + 1) * C.size := by
  have h := (C.layerFold_struct (n + C.gates.length)).2.2.2.2
  rw [← layerFold_eq, ← layerGates_eq] at h
  rw [DAGCircuit.size_eq C.layerNAND, DAGCircuit.size_eq C, layerNAND_gates]
  omega

end LayerNAND

end BoolCircuit
/- G06-HARNESS EOF-VERIFY SealcoeB_Complexity_CircuitComplexity_NANDLayering -/
set_option maxHeartbeats 0
run_cmd do
  let label : String := "SealcoeB_Complexity_CircuitComplexity_NANDLayering"
  let payload : String := "BoolCircuit.CompileListSpec.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.CompileSpec.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.DAGCircuit.IsFaninTwo\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.IsNANDForm\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.DAGCircuit.IsWellFormed\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.decidableIsNANDForm\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.DAGCircuit.depth\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.depthAt\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.depths\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.eval\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.rewrite\tTCSlib.Complexity.CircuitComplexity.DAGTransform\nBoolCircuit.DAGCircuit.size\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuit.toNANDForm\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.DAGCircuit.toTree\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.DAGCircuit.values\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.Accepts\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.HasFaninTwo\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.HasPolylogDepth\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.IsPolySize\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.IsWellFormed\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.language\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGCircuitFamily.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate.FaninTwo\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate.IsNAND\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.DAGGate.WellFormed\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate.decidableIsNAND\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.DAGGate.depth\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate.eval\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.DAGGate.remap\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.GadgetCorrect\tTCSlib.Complexity.CircuitComplexity.DAGTransform\nBoolCircuit.GadgetSpec.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.DAGTransform\nBoolCircuit.GateKind._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.GateKind._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.GateKind.enumList\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.GateKind.ofNat\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.GatesAcyclic\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.Lit._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.Lit._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.Lit.eval\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.Lit.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit._sizeOf_2\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit._sizeOf_3\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit._sizeOf_4\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.constTrue\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.depth\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.depth._mutual\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.depth._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.eval\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.eval._mutual\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.eval._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.eval.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.litCount\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.litCount._mutual\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.litCount._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.litCount.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.ofVar\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.size\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.size._mutual\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.size._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.toTreeCircuit\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.toTreeCircuit._mutual\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NAndCircuit.toTreeCircuit._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.constFalse\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.depth\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.depth._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.eval\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.eval._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.eval.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.litCount\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.litCount._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.litCount.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.ofVar\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.size\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.size._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.toTreeCircuit\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.NOrCircuit.toTreeCircuit._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.RewriteInv.mk._flat_ctor\tTCSlib.Complexity.CircuitComplexity.DAGTransform\nBoolCircuit.TreeCircuit._sizeOf_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit._sizeOf_2\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit._sizeOf_inst\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.depth\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.depth._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.eval\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.eval._unary\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.eval._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.eval.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.ind.match_1_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.length_le_sumSize.match_1_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.litCount\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.litCount._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.maxDepth\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.maxFanin\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.maxFanin._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.maxFaninL\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.size\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.size._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.sumSize\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toDAG\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.TreeCircuit.toNAnd\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toNAnd._mutual\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toNAnd._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toNAnd.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toNOr\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toNOr._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.TreeCircuit.toNOr.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.compileTree\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTree._sunfold\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTree._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTree.match_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTrees\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTrees._sunfold\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTrees._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTrees.match_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.compileTrees_spec.match_1_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.constCircuit\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.constGate\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instDecidableEqDAGGate\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instDecidableEqDAGGate.decEq\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instDecidableEqDAGGate.decEq.match_1\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instDecidableEqGateKind\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instDecidableEqLit\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instDecidableEqLit.decEq\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instDecidableEqLit.decEq.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instFintypeGateKind\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instHashableLit\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instHashableLit.hash\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instHashableLit.hash.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instReprDAGGate\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instReprDAGGate.repr\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instReprGateKind\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instReprGateKind.repr\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instReprGateKind.repr.match_1\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.instReprLit\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instReprLit.repr\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instReprTreeCircuit\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instReprTreeCircuit.repr._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.instReprTreeCircuit.repr.match_1\tTCSlib.Complexity.CircuitComplexity.Basic\nBoolCircuit.nandGadget\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.nandGadget.match_1\tTCSlib.Complexity.CircuitComplexity.NANDForm\nBoolCircuit.nodeKind\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.rewriteGates\tTCSlib.Complexity.CircuitComplexity.DAGTransform\nBoolCircuit.rewriteStep\tTCSlib.Complexity.CircuitComplexity.DAGTransform\nBoolCircuit.runWith\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\nBoolCircuit.unfoldGate\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldGate.match_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldGate_eval.match_1_10\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldGate_eval.match_1_12\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldGate_eval.match_1_4\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldGate_eval.match_1_6\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldVertex\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldVertex._sunfold\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldVertex._unsafe_rec\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.unfoldVertex.match_1\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.vertexDepth\tTCSlib.Complexity.CircuitComplexity.TreeDAG\nBoolCircuit.vertexValue\tTCSlib.Complexity.CircuitComplexity.TreeDAG\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NAndCircuit.eval.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NAndCircuit.litCount.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NOrCircuit.eval.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NOrCircuit.litCount.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.eval.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.sumSize_add_length_le.match_1_1\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.toNAnd.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.toNOr.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.instReprTreeCircuit.repr.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.List.map_unattach.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.Basic\n_private.TCSlib.Complexity.CircuitComplexity.DAGCircuit.0.BoolCircuit.instReprGateKind.repr.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.DAGCircuit\n_private.TCSlib.Complexity.CircuitComplexity.TreeDAG.0.BoolCircuit.compileTree.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.TreeDAG\n_private.TCSlib.Complexity.CircuitComplexity.TreeDAG.0.BoolCircuit.compileTrees.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.TreeDAG\n_private.TCSlib.Complexity.CircuitComplexity.TreeDAG.0.BoolCircuit.unfoldVertex.match_1.splitter\tTCSlib.Complexity.CircuitComplexity.TreeDAG"
  let expectedRequests : Nat := 187
  let mut requests : Array (String × String) := #[]
  let payloadLines := if payload.isEmpty then [] else payload.splitOn "\n"
  for line in payloadLines do
    match line.splitOn "\t" with
    | [spelling, home] =>
      unless !spelling.isEmpty && !home.isEmpty do throwError "G06-HARNESS {label}: empty request field"
      requests := requests.push (spelling, home)
    | _ => throwError "G06-HARNESS {label}: malformed serialized request row"
  unless requests.size == expectedRequests do throwError "G06-HARNESS {label}: serialized request count differs: {requests.size} vs {expectedRequests}"
  let rec nameParts : Lean.Name → List (String × String)
    | .anonymous => []
    | .str p s => nameParts p ++ [("str", s)]
    | .num p n => nameParts p ++ [("num", toString n)]
  let nameKey (n : Lean.Name) : String := (Lean.toJson (nameParts n)).compress
  let componentPayload : String := "BoolCircuit.CompileListSpec.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"CompileListSpec\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\ttrue\nBoolCircuit.CompileSpec.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"CompileSpec\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGCircuit.IsFaninTwo\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"IsFaninTwo\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.IsNANDForm\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"IsNANDForm\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.IsWellFormed\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"IsWellFormed\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGCircuit._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\ttrue\nBoolCircuit.DAGCircuit.decidableIsNANDForm\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"decidableIsNANDForm\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\ttrue\tfalse\tfalse\nBoolCircuit.DAGCircuit.depth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"depth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.depthAt\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"depthAt\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.depths\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"depths\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.eval\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"eval\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGCircuit.rewrite\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"rewrite\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGTransform\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.size\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"size\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.toNANDForm\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"toNANDForm\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.toTree\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"toTree\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"unfoldVertex_depth_le\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"unfoldVertex_eval\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"unfoldVertex_maxFanin_le\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"unfoldVertex_size_le\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.DAGCircuit.values\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuit\"],[\"str\",\"values\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily.Accepts\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"Accepts\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily.HasFaninTwo\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"HasFaninTwo\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily.HasPolylogDepth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"HasPolylogDepth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily.IsPolySize\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"IsPolySize\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily.IsWellFormed\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"IsWellFormed\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGCircuitFamily._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\ttrue\nBoolCircuit.DAGCircuitFamily.language\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"language\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGCircuitFamily.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGCircuitFamily\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGGate.FaninTwo\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"FaninTwo\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGGate.IsNAND\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"IsNAND\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGGate.WellFormed\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"WellFormed\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGGate._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGGate._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\ttrue\nBoolCircuit.DAGGate.decidableIsNAND\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"decidableIsNAND\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\ttrue\tfalse\tfalse\nBoolCircuit.DAGGate.depth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"depth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGGate.eval\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"eval\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.DAGGate.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.DAGGate.remap\t[[\"str\",\"BoolCircuit\"],[\"str\",\"DAGGate\"],[\"str\",\"remap\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.GadgetCorrect\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GadgetCorrect\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGTransform\"]]\tfalse\tfalse\tfalse\nBoolCircuit.GadgetSpec.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GadgetSpec\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGTransform\"]]\tfalse\tfalse\ttrue\nBoolCircuit.GateKind._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GateKind\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.GateKind._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GateKind\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\ttrue\nBoolCircuit.GateKind.enumList\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GateKind\"],[\"str\",\"enumList\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.GateKind.ofNat\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GateKind\"],[\"str\",\"ofNat\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\nBoolCircuit.GatesAcyclic\t[[\"str\",\"BoolCircuit\"],[\"str\",\"GatesAcyclic\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.Lit._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"Lit\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.Lit._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"Lit\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\ttrue\nBoolCircuit.Lit.eval\t[[\"str\",\"BoolCircuit\"],[\"str\",\"Lit\"],[\"str\",\"eval\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.Lit.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"Lit\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.NAndCircuit._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.NAndCircuit._sizeOf_2\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"_sizeOf_2\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.NAndCircuit._sizeOf_3\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"_sizeOf_3\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.NAndCircuit._sizeOf_4\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"_sizeOf_4\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.NAndCircuit._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\ttrue\nBoolCircuit.NAndCircuit.constTrue\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"constTrue\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.depth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"depth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.depth._mutual\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"depth\"],[\"str\",\"_mutual\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.depth._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"depth\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.eval\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"eval\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.eval._mutual\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"eval\"],[\"str\",\"_mutual\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.eval._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"eval\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.eval.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"eval\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.NAndCircuit.litCount\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"litCount\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.litCount._mutual\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"litCount\"],[\"str\",\"_mutual\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.litCount._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"litCount\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.litCount.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"litCount\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.NAndCircuit.ofVar\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"ofVar\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.size\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"size\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.size._mutual\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"size\"],[\"str\",\"_mutual\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.size._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"size\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.toTreeCircuit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"toTreeCircuit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.toTreeCircuit._mutual\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"toTreeCircuit\"],[\"str\",\"_mutual\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NAndCircuit.toTreeCircuit._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"toTreeCircuit\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\ttrue\nBoolCircuit.NOrCircuit.constFalse\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"constFalse\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.depth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"depth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.depth._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"depth\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.eval\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"eval\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.eval._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"eval\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.eval.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"eval\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.NOrCircuit.litCount\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"litCount\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.litCount._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"litCount\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.litCount.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"litCount\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.NOrCircuit.ofVar\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"ofVar\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.size\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"size\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.size._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"size\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.toTreeCircuit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"toTreeCircuit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.NOrCircuit.toTreeCircuit._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"toTreeCircuit\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.RewriteInv.mk._flat_ctor\t[[\"str\",\"BoolCircuit\"],[\"str\",\"RewriteInv\"],[\"str\",\"mk\"],[\"str\",\"_flat_ctor\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGTransform\"]]\tfalse\tfalse\ttrue\nBoolCircuit.TreeCircuit._sizeOf_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"_sizeOf_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.TreeCircuit._sizeOf_2\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"_sizeOf_2\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\nBoolCircuit.TreeCircuit._sizeOf_inst\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"_sizeOf_inst\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\ttrue\nBoolCircuit.TreeCircuit.depth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"depth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.depth._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"depth\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"depth_le_maxDepth\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.eval\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"eval\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.eval._unary\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"eval\"],[\"str\",\"_unary\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.eval._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"eval\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.eval.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"eval\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.ind.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"ind\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.length_le_sumSize.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"length_le_sumSize\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.litCount\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"litCount\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.litCount._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"litCount\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.maxDepth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"maxDepth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.maxFanin\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"maxFanin\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.maxFanin._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"maxFanin\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.maxFaninL\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"maxFaninL\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"maxFaninL_le_sumSize\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"maxFanin_le_maxFaninL\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.size\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"size\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.size._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"size\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.sumSize\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"sumSize\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toDAG\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toDAG\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toNAnd\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNAnd\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toNAnd._mutual\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNAnd\"],[\"str\",\"_mutual\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toNAnd._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNAnd\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toNAnd.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNAnd\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.TreeCircuit.toNOr\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNOr\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toNOr._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNOr\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.TreeCircuit.toNOr.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNOr\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.compileTree\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTree\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.compileTree._sunfold\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTree\"],[\"str\",\"_sunfold\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.compileTree._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTree\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.compileTree.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTree\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.compileTrees\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTrees\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.compileTrees._sunfold\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTrees\"],[\"str\",\"_sunfold\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.compileTrees._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTrees\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.compileTrees.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTrees\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.compileTrees_spec.match_1_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"compileTrees_spec\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.constCircuit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"constCircuit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.constGate\t[[\"str\",\"BoolCircuit\"],[\"str\",\"constGate\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instDecidableEqDAGGate\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqDAGGate\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instDecidableEqDAGGate.decEq\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqDAGGate\"],[\"str\",\"decEq\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instDecidableEqDAGGate.decEq.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqDAGGate\"],[\"str\",\"decEq\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\ttrue\ttrue\nBoolCircuit.instDecidableEqGateKind\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqGateKind\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instDecidableEqLit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqLit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instDecidableEqLit.decEq\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqLit\"],[\"str\",\"decEq\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instDecidableEqLit.decEq.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instDecidableEqLit\"],[\"str\",\"decEq\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.instFintypeGateKind\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instFintypeGateKind\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instHashableLit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instHashableLit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instHashableLit.hash\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instHashableLit\"],[\"str\",\"hash\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instHashableLit.hash.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instHashableLit\"],[\"str\",\"hash\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.instReprDAGGate\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprDAGGate\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instReprDAGGate.repr\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprDAGGate\"],[\"str\",\"repr\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instReprGateKind\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprGateKind\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instReprGateKind.repr\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprGateKind\"],[\"str\",\"repr\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instReprGateKind.repr.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprGateKind\"],[\"str\",\"repr\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\ttrue\ttrue\nBoolCircuit.instReprLit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprLit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instReprLit.repr\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprLit\"],[\"str\",\"repr\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instReprTreeCircuit\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprTreeCircuit\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\ttrue\tfalse\tfalse\nBoolCircuit.instReprTreeCircuit.repr._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprTreeCircuit\"],[\"str\",\"repr\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\tfalse\nBoolCircuit.instReprTreeCircuit.repr.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"instReprTreeCircuit\"],[\"str\",\"repr\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\nBoolCircuit.nandGadget\t[[\"str\",\"BoolCircuit\"],[\"str\",\"nandGadget\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\tfalse\tfalse\tfalse\nBoolCircuit.nandGadget.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"nandGadget\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"NANDForm\"]]\tfalse\ttrue\ttrue\nBoolCircuit.nodeKind\t[[\"str\",\"BoolCircuit\"],[\"str\",\"nodeKind\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.rewriteGates\t[[\"str\",\"BoolCircuit\"],[\"str\",\"rewriteGates\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGTransform\"]]\tfalse\tfalse\tfalse\nBoolCircuit.rewriteStep\t[[\"str\",\"BoolCircuit\"],[\"str\",\"rewriteStep\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGTransform\"]]\tfalse\tfalse\tfalse\nBoolCircuit.runWith\t[[\"str\",\"BoolCircuit\"],[\"str\",\"runWith\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\tfalse\nBoolCircuit.unfoldGate\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldGate\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.unfoldGate.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldGate\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.unfoldGate_eval.match_1_10\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldGate_eval\"],[\"str\",\"match_1_10\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.unfoldGate_eval.match_1_12\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldGate_eval\"],[\"str\",\"match_1_12\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.unfoldGate_eval.match_1_4\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldGate_eval\"],[\"str\",\"match_1_4\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.unfoldGate_eval.match_1_6\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldGate_eval\"],[\"str\",\"match_1_6\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.unfoldVertex\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldVertex\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.unfoldVertex._sunfold\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldVertex\"],[\"str\",\"_sunfold\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.unfoldVertex._unsafe_rec\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldVertex\"],[\"str\",\"_unsafe_rec\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.unfoldVertex.match_1\t[[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldVertex\"],[\"str\",\"match_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\ttrue\ttrue\nBoolCircuit.vertexDepth\t[[\"str\",\"BoolCircuit\"],[\"str\",\"vertexDepth\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\nBoolCircuit.vertexValue\t[[\"str\",\"BoolCircuit\"],[\"str\",\"vertexValue\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\tfalse\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NAndCircuit.eval.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"eval\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NAndCircuit.litCount.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"NAndCircuit\"],[\"str\",\"litCount\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NOrCircuit.eval.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"eval\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.NOrCircuit.litCount.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"NOrCircuit\"],[\"str\",\"litCount\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.eval.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"eval\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.sumSize_add_length_le.match_1_1\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"sumSize_add_length_le\"],[\"str\",\"match_1_1\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\ttrue\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.toNAnd.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNAnd\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.TreeCircuit.toNOr.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"TreeCircuit\"],[\"str\",\"toNOr\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.BoolCircuit.instReprTreeCircuit.repr.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"instReprTreeCircuit\"],[\"str\",\"repr\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.Basic.0.List.map_unattach.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"],[\"num\",\"0\"],[\"str\",\"List\"],[\"str\",\"map_unattach\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"Basic\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.DAGCircuit.0.BoolCircuit.instReprGateKind.repr.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"instReprGateKind\"],[\"str\",\"repr\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"DAGCircuit\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.TreeDAG.0.BoolCircuit.compileTree.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"compileTree\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.TreeDAG.0.BoolCircuit.compileTrees.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"compileTrees\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\ttrue\n_private.TCSlib.Complexity.CircuitComplexity.TreeDAG.0.BoolCircuit.unfoldVertex.match_1.splitter\t[[\"str\",\"_private\"],[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"],[\"num\",\"0\"],[\"str\",\"BoolCircuit\"],[\"str\",\"unfoldVertex\"],[\"str\",\"match_1\"],[\"str\",\"splitter\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"CircuitComplexity\"],[\"str\",\"TreeDAG\"]]\tfalse\tfalse\ttrue"
  let mut components : Std.HashMap String (String × String × String × String × String) := {}
  for line in (if componentPayload.isEmpty then [] else componentPayload.splitOn "\n") do
    match line.splitOn "\t" with
    | [n, nk, hk, i, m, a] =>
      if (components[n]?).isSome then throwError "G06-HARNESS {label}: duplicate component request"
      components := components.insert n (nk, hk, i, m, a)
    | _ => throwError "G06-HARNESS {label}: malformed component request"
  unless components.size == requests.size do throwError "G06-HARNESS {label}: component count differs"
  let env ← Lean.getEnv
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  let mut verified : Nat := 0
  for (n, _) in env.constants.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue
    let ns := (catalog[n.toString]?).getD #[]
    catalog := catalog.insert n.toString (ns.push n)
  for (spelling, expectedHome) in requests do
    let ns := (catalog[spelling]?).getD #[]
    unless ns.size == 1 do throwError "G06-HARNESS {label}: absent/ambiguous imported name {spelling}; candidates={ns.size}"
    let n := ns[0]!
    let some mi := env.getModuleIdxFor? n | throwError "G06-HARNESS {label}: no home for {spelling}"
    let home := env.header.moduleNames[mi.toNat]!
    unless home.toString == expectedHome do throwError "G06-HARNESS {label}: home differs for {spelling}: {home}"
    let some ci := env.find? n | throwError "G06-HARNESS {label}: no constant for {spelling}"
    unless ci.isDefinition do throwError "G06-HARNESS {label}: requested nondefinition {spelling}"
    let some (nk, hk, ei, em, ea) := components[spelling]?
      | throwError "G06-HARNESS {label}: missing component request"
    unless nameKey n == nk && nameKey home == hk do
      throwError "G06-HARNESS {label}: actual Name components differ"
    let instanceFlag := Lean.Meta.isInstanceCore env n
    let matcherFlag := (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome
    let abbrevFlag := match ci with
      | .defnInfo d => match d.hints with | .abbrev => true | _ => false
      | _ => false
    unless toString instanceFlag == ei && toString matcherFlag == em && toString abbrevFlag == ea do
      throwError "G06-HARNESS {label}: definition/instance metadata differs"
    Lean.logInfo m!"G06-COMPONENT label={label} phase=eof spelling={spelling} key={nk} home_key={hk} instance={instanceFlag}"
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless installed == .irreducible do throwError "G06-HARNESS {label}: seal not installed at EOF for {spelling}"
    if Lean.Meta.isGlobalInstance env n then
      throwError "G06-HARNESS {label}: unfolding membership at EOF for {spelling}"
    verified := verified + 1
  unless verified == requests.size do throwError "G06-HARNESS {label}: verification count mismatch"
  Lean.logInfo m!"G06-MASK label={label} phase=eof requested={requests.size} verified={verified}"
  Lean.logInfo m!"G06-SEAL-END label={label} requested={requests.size} verified={verified}"

