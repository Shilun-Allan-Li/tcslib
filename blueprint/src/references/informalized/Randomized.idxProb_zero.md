<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.idxProb_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability at Length Zero

**Claim.** At length zero, the probability assigned to $A$ is $1$ if $A$ holds of the empty sequence and $0$ otherwise.

**Proof.** There is exactly one function from the empty set of positions into the alphabet, corresponding under the list representation to the empty sequence. Thus the filtered set has one element precisely when $A([])$ holds, and otherwise has none. The denominator is $D^0=1$, so the probability is respectively $1$ or $0.
