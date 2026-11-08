<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.evalNode_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Layer Evaluation

**Claim.** A node $u$ at layer $0$ evaluates to the value assigned by $xs$ to its corresponding input.

**Proof.** The recursive definition of node evaluation has the input assignment as its base case at layer $0$. The node is identified with its corresponding input by $F$'s layer-zero identification, so its value is $xs$ applied to that input.
