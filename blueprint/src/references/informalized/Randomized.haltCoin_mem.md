<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.haltCoin_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Coin Bounds

**Claim.** The halting coin lies in the interval $[0,1/3]$.

**Proof.** Apply the finite-prefix decomposition at $J=0$: it gives a real remainder $\tau$ with $H\cdot 4^0=\operatorname{haltPrefix}(0)+\tau$ and $0\leq\tau\leq1/3$. Since $4^0=1$ and the length-zero prefix is $0$, this identifies $H=\tau$. The two remainder bounds therefore give the claimed interval.

**Key facts.** `Randomized.haltCoin_mul_pow`.
