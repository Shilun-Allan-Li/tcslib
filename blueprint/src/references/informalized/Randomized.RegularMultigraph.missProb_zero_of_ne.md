<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.missProb_zero_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Miss Probability Away from the Target

**Claim.** If $s\ne t$, then a walk of length zero started at $s$ has miss probability $1$ for target $t$.

**Proof.** At length zero the hit probability is $1$ exactly when the starting vertex equals the target, and is $0$ otherwise (`hitProb_zero`). Since $s\ne t$, the hit probability here is $0$, so its complement, the miss probability, is $1$.

**Key facts.** `Randomized.RegularMultigraph.hitProb_zero`.
