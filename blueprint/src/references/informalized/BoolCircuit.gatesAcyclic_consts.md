<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily.lean :: BoolCircuit.gatesAcyclic_consts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of two constant gates

**Claim.** For every $k$, the false constant gate followed by the true constant gate is acyclic from index bound $k$.

**Proof.** The list has two positions, $0$ and $1$. Both constant gates have no inputs, so there is no input index at either position that could violate the required bound. Hence the list is acyclic from $k$.
