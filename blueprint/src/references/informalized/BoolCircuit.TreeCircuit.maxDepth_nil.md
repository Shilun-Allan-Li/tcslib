<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.maxDepth_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum depth of the empty list

**Claim.** The maximum depth among an empty list of Boolean circuit trees is $0$.

**Proof.** The maximum depth of a list is defined by folding the maximum operation over its entries, starting from $0$. The empty list contributes no entries, so its fold is the starting value $0$.
