<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredCircuit.lean :: BoolCircuit.TreeCircuit.toLayeredWrapper_evalNode_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Evaluation of Embedded Circuit Nodes

**Claim.** For every integer $m$ with $1\le m\le \mathrm{depth}(C)+1$ and every node $v$ in layer $m$ of the feedforward embedding of $C$, the value of $v$ on input $x$ equals the value of $C$ on $x$.

**Proof.** Separate the base layer from the higher layers. At the first positive layer, the definition of the embedding makes its nodes compute the value of the whole tree, so the assertion holds there. For each subsequent layer, the embedding carries forward the same computed value; applying the induction hypothesis to the preceding layer therefore gives the assertion for the next one. The bounds on $m$ ensure that the layer and its predecessor are within the embedding.

**Caveat.** The proof source uses simplification and induction over the layer index, but the supplied formal context omits the definition of the layered embedding and does not expose the induction's detailed layer behavior. The account of how values are propagated therefore cannot be fully verified from the provided material.
