<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.missProb_thousand_mul_pow_three_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Miss Probability After Cubically Many Steps

**Claim.** If $D\le 100|V|$ and $s$ can reach $t$, then after $1000|V|^3$ steps the probability of failing to visit $t$ is at most $1/10$.

**Proof.** Choose a walk from $s$ to $t$ of length less than $|V|$ (`exists_short_walk`), and let $L=1000|V|^3$. The expected hitting-time estimate for a walk of length at most $|V|$, under the degree bound, gives $\operatorname{hitTime}(t,L+1,s)\le 100|V|^3$ (`hitTime_le_hundred_mul`). The miss-probability lower bound relating this expected hitting time to the chance of missing after $L$ steps gives $(L+1)\operatorname{missProb}(t,L,s)\le \operatorname{hitTime}(t,L+1,s)$ (`succ_mul_missProb_le`). If the miss probability exceeded $1/10$, multiplying by the positive number $L+1$ would make the left side exceed $(1000|V|^3+1)/10$, which is greater than $100|V|^3$. This contradicts the two bounds, proving the claim.

**Key facts.** `Randomized.RegularMultigraph.exists_short_walk`, `Randomized.RegularMultigraph.succ_mul_missProb_le`, `Randomized.RegularMultigraph.hitTime_le_hundred_mul`.
