<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.eval₁_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation with a Unique Output

**Claim.** For a layered circuit with a unique output, its scalar evaluation on $xs$ equals the value of the node in the last layer corresponding to the unique output.

**Proof.** Scalar evaluation is defined by evaluating the circuit's output function at the unique element of the output type. The output function, in turn, is defined as evaluation of the corresponding node in the last layer. Unfolding these definitions gives the stated equality.
