<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean :: Randomized.succ_mul_binTail_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binomial-tail bound

**Claim.** For $D\ge1$ and all natural numbers $L,j$, $(L+1)B_D(L,j)\le jD$.

**Proof.** For each $m\le L$, the binomial tail with first parameter $L$ is at most the one with first parameter $m$. Indeed, the tail is nonincreasing in its first parameter, by the one-step inequality `Randomized.binTail_succ_le`; iterating gives the comparison. Summing this inequality over $m=0,\ldots,L$ bounds $(L+1)B_D(L,j)$ by $\sum_{m=0}^{L}B_D(m,j)$. The sum bound `Randomized.sum_binTail_le` says this is at most $jD$, proving the result.

**Key facts.** `Randomized.binTail_succ_le`, `Randomized.sum_binTail_le`.
