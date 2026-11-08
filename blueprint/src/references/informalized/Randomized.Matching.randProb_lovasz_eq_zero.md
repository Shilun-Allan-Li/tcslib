<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.randProb_lovasz_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Acceptance Probability Without a Perfect Matching

**Claim.** If the bipartite graph specified by $A$ has no perfect matching, then the probability that the determinant of the adjacency-masked matrix of sampled entries over $R$ is nonzero is zero.

**Proof.** For every sample, the matrix obtained by masking the sampled entries with $A$ has determinant zero when the graph has no perfect matching ( `det_lovaszMatrix_eq_zero`). Hence the event that this determinant is nonzero is equivalent, on every input string, to the false event. The probability is unchanged when an event is replaced by an equivalent one ( `randProb_congr`), and the false event has probability zero ( `randProb_false`).

**Key facts.** `Randomized.Matching.det_lovaszMatrix_eq_zero`, `Randomized.randProb_congr`, `Randomized.randProb_false`.
