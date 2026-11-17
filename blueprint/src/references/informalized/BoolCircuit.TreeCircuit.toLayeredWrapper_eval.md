<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredCircuit.lean :: BoolCircuit.TreeCircuit.toLayeredWrapper_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Layered Embedding

**Claim.** For any Boolean circuit tree $C$ and input assignment $x$, the value computed by the unique output of its layered feedforward embedding equals the value of $C$ evaluated directly on $x$.

**Proof.** The layered circuit has a unique output, so its evaluation is the value at that output node. Apply the fact that every node in a positive layer of the embedding evaluates to the value of the original tree on $x$ (`BoolCircuit.TreeCircuit.toLayeredWrapper_evalNode_const`). The output lies in the final layer, whose index is the embedding depth; the depth formula makes this a positive layer and places it within the theorem's stated range. Thus the output value is $C$'s direct evaluation on $x$.

**Key facts.** `BoolCircuit.TreeCircuit.toLayeredWrapper_evalNode_const`.
