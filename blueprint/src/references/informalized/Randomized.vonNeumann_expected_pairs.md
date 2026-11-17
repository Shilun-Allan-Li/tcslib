<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.vonNeumann_expected_pairs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected pairs before rejection

**Claim.** For $0<\rho<1$, summing over $K=0,\ldots,M-1$ the probability that the pair rule returns none is at most $1/(2\rho(1-\rho))$.

**Proof.** The probability of returning none after $K$ pairs is $(\rho^2+(1-\rho)^2)^K$ (`Randomized.vonNeumann_none`): each pair is equal with probability $\rho^2+(1-\rho)^2$, and all $K$ pairs must be equal. Put $x=\rho^2+(1-\rho)^2$. The assumptions imply $0<x<1$, since $1-x=2\rho(1-\rho)>0$. The finite geometric-sum bound gives $\sum_{K=0}^{M-1}x^K\le 1/(1-x)$. Finally, $1-x=2\rho(1-\rho)$, giving the claimed bound.

**Key facts.** `Randomized.vonNeumann_none`.
