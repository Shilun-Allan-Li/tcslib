<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.gateValue_eq_evalGate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate Relations Determine Gate Values

**Claim.** If an assignment satisfies every gate relation, then the Boolean value decoded from each gate coordinate equals the value obtained by evaluating that gate from the decoded input-coordinate values.

**Proof.** Proceed by induction on the gate index, using that every source of a non-input gate is strictly earlier. Fix a gate and split on its type. For an input gate or constant gate, the gate relation directly gives the decoded value, and the evaluation equations identify the evaluated gate with the input value or constant (`FABL.BooleanCircuit.evalGate_eq_input`, `FABL.BooleanCircuit.evalGate_eq_const`). For a negation gate, the induction hypothesis identifies the decoded value at its earlier source with that source's evaluation; substituting this into the gate relation shows that the gate value is the negation of the source evaluation, as required by the evaluation equation (`FABL.BooleanCircuit.evalGate_eq_neg`). For an AND gate, apply the induction hypothesis to both earlier inputs and substitute both equalities into the gate relation; the evaluation equation identifies the result with their conjunction (`FABL.BooleanCircuit.evalGate_eq_and`). The OR case is identical with disjunction in place of conjunction (`FABL.BooleanCircuit.evalGate_eq_or`).

**Key facts.** `FABL.BooleanCircuit.evalGate_eq_input`, `FABL.BooleanCircuit.evalGate_eq_const`, `FABL.BooleanCircuit.evalGate_eq_neg`, `FABL.BooleanCircuit.evalGate_eq_and`, `FABL.BooleanCircuit.evalGate_eq_or`.
