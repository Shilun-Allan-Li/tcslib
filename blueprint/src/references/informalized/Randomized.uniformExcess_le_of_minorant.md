<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.uniformExcess_le_of_minorant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform excess under a minorized transition

**Claim.** For a finite nonempty set $V$, a column-stochastic transition $P$ whose entries are at least $\delta$, and a probability mass function $p$, the uniform excess after applying $P$ is at most $(1-|V|\delta)$ times the uniform excess of $p$.

**Proof.** Fix a column $v$ and write $n=|V|$. Since $p$ sums to $1$, the deviations $p(u)-1/n$ sum to zero (`Randomized.sum_sub_inv_card`). Expand each summand in the output excess as
\[
p(u)P(u,v)=\bigl(p(u)-1/n\bigr)\bigl(P(u,v)-\delta\bigr)+(1/n)P(u,v)+\delta\bigl(p(u)-1/n\bigr).
\]
After summing over $u$ and subtracting $1/n$, the column sum condition and the zero-sum deviations cancel the last two contributions. Each deviation is at most the input uniform excess (`Randomized.le_uniformExcess`), while $P(u,v)-\delta\ge0$. Thus the remaining sum is at most the uniform excess times $\sum_u(P(u,v)-\delta)=1-n\delta$, using the column sum again. This bounds the output excess at every $v$; taking its maximum proves the assertion.

**Key facts.** `Randomized.sum_sub_inv_card`, `Randomized.le_uniformExcess`.
