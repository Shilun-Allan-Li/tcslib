<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.mem_treeSize_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Tree-Size Languages

**Claim.** A language has tree size at most $T$ exactly when there is a family of Boolean circuit trees, one on $n$ variables for each $n$, whose size is at most $T(n)$ and whose evaluation on the entries of every Boolean word agrees with membership of that word in the language.

**Proof.** The definition of the class of languages of tree size at most $T$ is precisely the property that the language satisfies this family-of-trees condition. Thus the equivalence is immediate from the definition.
