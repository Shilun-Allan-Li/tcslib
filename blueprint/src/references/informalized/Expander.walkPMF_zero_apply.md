<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Walks.lean :: Expander.walkPMF_zero_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of an Initial Walk

**Claim.** Every walk consisting of a single state has probability $(n: \mathbb{R}_{\ge 0\infty})^{-1}$ under the process that chooses its initial state uniformly.

**Proof.** A function from the singleton index set to the state space is determined by its value at the sole index, so the event specifying that function has exactly one preimage under the map that turns a state into a constant one-state walk. The probability of the walk is therefore the uniform probability of that state, which is the reciprocal of the number of states, $n$.
