<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.eval_node_pairUp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation After Pairing Children

**Claim.** Replacing consecutive pairs of children by gates of the same type, with any final unpaired child left alone, preserves the evaluation of the outer gate.

**Proof.** Induct on the list. The empty list is unchanged. For a singleton list, pairing leaves the child alone, so its value is unchanged. For a list beginning with two children, the induction hypothesis preserves the evaluation of the paired remainder. The new leading gate combines the first two child values using the same operation as the outer gate. Associativity of conjunction in the AND case and of disjunction in the OR case then identifies the resulting fold with the original evaluation.
