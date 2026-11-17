<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/TreeNCAC.lean :: BoolCircuit.combine_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of a Combined Circuit

**Claim.** For any gate type and finite list $cs$ of Boolean circuit trees, the depth of the combined circuit is at most the maximum depth in $cs$, plus $\lceil\log_2 |cs|\rceil+1$, where the maximum depth of an empty list is $0$.

**Proof.** The combined circuit is defined by running the recursive combination with fuel equal to the list length. Apply the recursive depth bound `combineFuel_depth` with this fuel; its hypothesis that the list length is at most the fuel holds with equality. This gives the claimed estimate directly.

**Key facts.** `BoolCircuit.combineFuel_depth`.
