<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.place_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Vertex Placement

**Claim.** For any natural number $k$, the vertex placement map for a sequential circuit at stage $k$ is injective.

**Proof.** Suppose two vertices $a$ and $b$ have the same placement. Split according to whether each lies below the input count $n$. If both are inputs, placement leaves them unchanged, so $a=b$. If both are at least $n$, placement adds the same offset $kM.size$ to each, and equality of the results gives $a=b$ by cancellation. The mixed cases would require an unchanged input vertex to equal a placed vertex at least $n+kM.size$, which cannot hold. Hence the placements being equal always forces $a=b$.
