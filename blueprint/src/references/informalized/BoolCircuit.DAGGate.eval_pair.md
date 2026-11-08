<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGGate.eval_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Two-Input Gate

**Claim.** For a gate kind other than negation, the gate with inputs $a,b$ evaluates to the associated binary operation applied to the values at those indices, with out-of-range values taken as false.

**Proof.** Split into the two possible kinds, conjunction and disjunction. For conjunction, evaluating the two-element argument list takes the conjunction of the two indexed values; for disjunction, it takes their disjunction. In each case this is exactly the operation associated with the gate kind. The excluded negation case is the only other kind.
