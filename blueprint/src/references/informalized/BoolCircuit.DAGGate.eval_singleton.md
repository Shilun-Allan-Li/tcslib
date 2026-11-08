<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGGate.eval_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a One-Input Gate

**Claim.** For a gate kind other than negation, the gate with sole input $a$ evaluates to the value at index $a$, with out-of-range indices taken as false.

**Proof.** Split into conjunction and disjunction, the two kinds allowed by the hypothesis. For a one-element argument list, both the conjunction and the disjunction of its values equal that sole value. The gate evaluation therefore equals the value at index $a$.
