<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.testLen_le_polyLen_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Testing length polynomial bound

**Claim.** If $n,m\le N$, then $n(m+4)+16(m+12)^2\le 2400(N+1)^2$.

**Proof.** From $n\le N$ and $m\le N$, we have $n(m+4)\le N(N+4)$ and $(m+12)^2\le(N+12)^2$. Thus the left side is at most $N(N+4)+16(N+12)^2$. Expanding, this is $17N^2+388N+2304$, which is at most $2400(N+1)^2$ for every natural number $N$.
