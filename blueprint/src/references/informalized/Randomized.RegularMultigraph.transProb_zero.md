<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.transProb_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Step Transition Probability

**Claim.** The probability that a zero-step walk from $u$ ends at $v$ is $1$ when $u=v$ and $0$ otherwise.

**Proof.** A zero-step walk has no indices, so its endpoint is its starting vertex $u$. The zero-step index-probability formula (`idxProb_zero`) says the probability of an event on the empty index list is $1$ if that event holds and $0$ otherwise. Applying it to the endpoint event gives the stated result.

**Key facts.** `Randomized.idxProb_zero`.
