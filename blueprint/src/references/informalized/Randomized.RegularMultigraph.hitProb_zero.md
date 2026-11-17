<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.hitProb_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Step Hitting Probability

**Claim.** For a regular multigraph and vertices $s,t$, the probability that a length-zero walk starting at $s$ hits $t$ is $1$ if $s=t$ and $0$ otherwise.

**Proof.** There is only one length-zero index sequence, the empty sequence. Its hit event is true exactly when its starting vertex $s$ equals $t$. The zero-length index-probability formula (`idxProb_zero`) therefore gives probability $1$ when $s=t$ and $0$ otherwise.

**Key facts.** `Randomized.idxProb_zero`.
