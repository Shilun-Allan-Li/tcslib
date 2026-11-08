<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.maxDepth_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum depth after adjoining a circuit

**Claim.** The maximum depth in the list formed by placing $c$ before $cs$ is the maximum of the depth of $c$ and the maximum depth in $cs$.

**Proof.** By definition, the maximum depth of a list is the right fold that takes the maximum of each circuit's depth, starting from $0$. Folding over a list with first element $c$ therefore gives the maximum of $c$'s depth and the fold over the remaining list, which is its maximum depth.
