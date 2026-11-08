<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.summable_haltCoin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summability of the halting-bit series

**Claim.** For every natural number $J$, the series with terms $h_{j+J}4^{-(j+1)}$ is summable, where $h_k$ is $1$ on the halting set and $0$ otherwise.

**Proof.** Each halting bit is nonnegative and at most $1$ (the bound is supplied by `haltBit_le_one`). Hence each term is nonnegative and at most $(1/4)^{j+1}=(1/4)(1/4)^j$. The geometric series with ratio $1/4$, multiplied by $1/4$, is summable since $0<1/4<1$. Comparison proves the desired summability.

**Key facts.** `Randomized.haltBit_le_one`.
