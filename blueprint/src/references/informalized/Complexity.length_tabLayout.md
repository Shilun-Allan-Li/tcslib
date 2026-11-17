<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauSpec.lean :: Complexity.length_tabLayout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Layout Length

**Claim.** For every natural number $N$, the list of input-bit sources in the layout for an input of length $N$ has length $N$.

**Proof.** The layout maps one input-bit source over each index in the range of length $N$. Mapping preserves the number of list entries, so the layout has length $N$.
