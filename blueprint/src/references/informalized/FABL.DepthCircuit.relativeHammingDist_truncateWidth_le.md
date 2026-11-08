<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.relativeHammingDist_truncateWidth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truncation Error Bound

**Claim.** For any depth circuit $C$ and width $w$, the relative Hamming distance between $C$ and its width-$w$ truncation is at most $C.size\,2^{-w}$.

**Proof.** 1. Regard relative Hamming distance as the uniform probability that the two circuits disagree; this is the identity supplied by `FABL.uniformProbability_ne_eq_relativeHammingDist`. Let the deleted indices be those first-layer gates whose widths exceed $w$. If the circuit and its truncation disagree on an input, some deleted gate must have a nonneutral output on that input (`FABL.DepthCircuit.exists_deletedLayer1_of_eval_ne_truncateWidth`). Thus the disagreement indicator is bounded by the sum of the indicators that each deleted gate is nonneutral.

2. Average this pointwise inequality over inputs and exchange the finite sum with expectation. A first-layer gate of width $k$ is nonneutral with probability $2^{-k}$ (`FABL.DepthCircuit.uniformProbability_evalLayer1_ne_neutral`). For every deleted gate, $k>w$, so $2^{-k}\leq 2^{-w}$. Therefore the disagreement probability is at most the number of deleted gates times $2^{-w}$.

3. The number of deleted gates is at most the number of first-layer gates, which is at most the total circuit size. Substituting this bound gives the asserted estimate.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`, `FABL.DepthCircuit.exists_deletedLayer1_of_eval_ne_truncateWidth`, `FABL.DepthCircuit.uniformProbability_evalLayer1_ne_neutral`.
