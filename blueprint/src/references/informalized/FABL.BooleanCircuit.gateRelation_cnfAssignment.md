<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.gateRelation_cnfAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluated Assignments Satisfy Gate Relations

**Claim.** For any input, the assignment encoding its input bits and evaluated gate values satisfies the prescribed relation at every gate.

**Proof.** Fix a gate and split on its type. The assignment's value at a gate coordinate is the sign encoding of that gate's evaluated value, and at an input coordinate it is the sign encoding of the corresponding input bit (`FABL.BooleanCircuit.cnfAssignment_gateCoordinate`, `FABL.BooleanCircuit.cnfAssignment_inputCoordinate`). Decoding either encoded Boolean value recovers the original Boolean value (`FABL.boolOfSign_signOfBool`). For an input gate or a constant gate, the evaluation is respectively the selected input bit or the constant (`FABL.BooleanCircuit.evalGate_eq_input`, `FABL.BooleanCircuit.evalGate_eq_const`). For a negation, conjunction, or disjunction gate, its evaluation is the corresponding Boolean operation on the earlier gates' evaluations (`FABL.BooleanCircuit.evalGate_eq_neg`, `FABL.BooleanCircuit.evalGate_eq_and`, `FABL.BooleanCircuit.evalGate_eq_or`). In each case these facts identify the decoded gate value with exactly the right-hand side of its gate relation.

**Key facts.** `FABL.BooleanCircuit.cnfAssignment_gateCoordinate`, `FABL.BooleanCircuit.cnfAssignment_inputCoordinate`, `FABL.boolOfSign_signOfBool`, `FABL.BooleanCircuit.evalGate_eq_input`, `FABL.BooleanCircuit.evalGate_eq_const`, `FABL.BooleanCircuit.evalGate_eq_neg`, `FABL.BooleanCircuit.evalGate_eq_and`, `FABL.BooleanCircuit.evalGate_eq_or`.
