<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect.lean :: BoolCircuit.CircuitEval.ofFn_getD_eq_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexed Prefix Reconstruction

**Claim.** For every Boolean word $x$ and $n\le |x|$, the word of length $n$ whose entries are the corresponding entries of $x$ is the prefix of $x$ of length $n$.

**Proof.** We show the two lists have the same length and agree at every index below that length. The bound $n\le |x|$ ensures that all such indices are valid indices of $x$, so the default value in the indexed construction is never used. At each index, both lists therefore return the same entry of $x$, which proves equality of the lists.
