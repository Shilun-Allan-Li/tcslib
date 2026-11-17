<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.missProb_antitone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Miss Probability

**Claim.** For fixed target and starting vertices, the miss probability is nonincreasing with the walk length.

**Proof.** The one-step inequality says that increasing the length from $k$ to $k+1$ cannot increase the miss probability (`missProb_succ_le`). Iterating this adjacent-step inequality along the natural-number order proves the asserted antitonicity.

**Key facts.** `Randomized.RegularMultigraph.missProb_succ_le`.
