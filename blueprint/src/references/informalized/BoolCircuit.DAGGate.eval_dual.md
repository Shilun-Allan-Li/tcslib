<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.DAGGate.eval_dual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation under duality

**Claim.** If all gate arguments are within the Boolean value list, and a NOT gate has exactly one argument, then the dual gate evaluated on the pointwise-negated values gives the negation of the original evaluation.

**Proof.** The range hypothesis ensures that at each argument the value in the pointwise-negated list is the negation of the original lookup; the default value is irrelevant because every referenced index is in range. For an AND gate, the dual is an OR gate, and the disjunction of the negated lookups is the negation of their conjunction (`any_eq_not_all`). For an OR gate, the dual is AND, and the conjunction of the negated lookups is the negation of their disjunction (`all_eq_not_any`). For a NOT gate, the singleton-input hypothesis writes its argument list as one index. Its dual has the corresponding dual kind, and the in-range lookup identity gives the required negation directly.

**Key facts.** `BoolCircuit.any_eq_not_all`, `BoolCircuit.all_eq_not_any`.
