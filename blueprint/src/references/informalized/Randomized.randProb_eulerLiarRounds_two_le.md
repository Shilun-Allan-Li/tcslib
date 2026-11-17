<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.randProb_eulerLiarRounds_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Round Euler Liar Probability Bound

**Claim.** For odd composite $N>1$, if $8N\le 2^\ell$, then two Euler liar rounds using $2\ell$ random bits accept with probability at most $\frac13$.

**Proof.** The repeated-round bound gives an upper bound of $\left(\frac12+\delta\right)^2$, where $\delta=(N-1)/2^{\ell+1}$. The hypothesis $8N\le 2^\ell$ implies $16(N-1)\le 2^{\ell+1}$, hence $0\le\delta\le 1/16$. Therefore the bound is at most $(1/2+1/16)^2=81/256<1/3$, which proves the claim.

**Key facts.** `Randomized.randProb_eulerLiarRounds_le`.
