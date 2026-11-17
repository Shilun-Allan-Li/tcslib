<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.haltCoin_mul_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Coin Prefix Decomposition

**Claim.** For every natural number $J$, the halting coin multiplied by $4^J$ is the length-$J$ halting prefix plus a remainder between $0$ and $1/3$.

**Proof.** Write $H=\sum_{j\geq0} b_j(1/4)^{j+1}$, where each halting bit $b_j$ is either zero or one. First, the length-$J$ prefix is the integer encoded by the first $J$ base-$4$ digits: $\operatorname{haltPrefix}(J)=4^J\sum_{j<J}b_j(1/4)^{j+1}$. This identity follows by induction from the recurrence that appends the next digit. Split the convergent series for $H$ after its first $J$ terms. Multiplying by $4^J$ turns the initial segment into that prefix; the remaining tail is $\tau=\sum_{j\geq0}b_{j+J}(1/4)^{j+1}$. Every summand is nonnegative, so $\tau\geq0$. Since $b_{j+J}\leq1$, the tail is at most the geometric series $\sum_{j\geq0}(1/4)^{j+1}=1/3$.

**Key facts.** `Randomized.haltBit_le_one`, `Randomized.summable_haltCoin`.
