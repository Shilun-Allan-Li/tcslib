<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.eval_tseitinGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a List of Tseitin Constraints

**Claim.** The conjunction of the Tseitin encodings of a list of gates, with successive vertex indices starting at $z$, evaluates to true exactly when each gate's encoding at its corresponding index evaluates to true.

**Proof.** Induct on the list of gates, generalizing the starting index. For the empty list, the conjunction is true and there are no gate conditions to check. For a list with first gate $g$ and tail $gs$, the encoded formula is the concatenation of $g$'s encoding at $z$ and the tail's encoding starting at $z+1$. The evaluation of a concatenation is the conjunction of the evaluations, so the induction hypothesis reduces the claim to the first gate's condition and the conditions for the tail. The first gate corresponds to index $0$; each tail index $i$ corresponds to index $i+1$ in the original list. The starting vertex for that gate is the same either way, since $z+1+i=z+(i+1)$. Hence both directions of the claimed equivalence follow by matching the first condition and all the shifted tail conditions.
