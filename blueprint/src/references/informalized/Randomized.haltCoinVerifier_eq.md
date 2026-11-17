<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.haltCoinVerifier_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coin Verifier Identifies the Halting Language

**Claim.** For bit strings $x,r$ with $r$ of positive length, if the fraction of ones in $r$ differs from the halting coin by at most $1/(4d(x))$, then the verifier's output on $(x,r)$ equals the Boolean indicator of whether $x$ belongs to the halting language.

**Proof.** Let $e=(r.\mathrm{count}(\mathrm{true}))d(x)/|r|$. Multiplying the assumed approximation error by the positive quantity $d(x)$ shows that $|e-d(x)\,\mathrm{haltCoin}|\le1/4$. Since $d(x)=4^{\mathrm{hlJ}(x)}$, the coin's scaled value is exactly the quantity bounded in the structural characterization of the halting language (`Randomized.haltCoin_mul_pow_hlJ`). Because $|r|>0$, the verifier's first inequality is equivalent to $4\,\mathrm{hlN}(x)+2/3<e$, and its second is equivalent to $e<4\,\mathrm{hlN}(x)+2$. If $x$ belongs to the language, the characterization places the scaled coin between $4\,\mathrm{hlN}(x)+1$ and $4\,\mathrm{hlN}(x)+4/3$. The error bound then puts $e$ strictly between the verifier's two thresholds, so both tests pass and the output is true. If $x$ is outside the language, the scaled coin is either at most $4\,\mathrm{hlN}(x)+1/3$ or at least $4\,\mathrm{hlN}(x)+4$. The same error bound forces $e$ below the lower threshold or above the upper one, so at least one test fails and the output is false. The indicator has these same values, by its membership characterizations (`Randomized.indicator_eq_true_iff`, `Randomized.indicator_eq_false_iff`).

**Key facts.** `Randomized.haltCoin_mul_pow_hlJ`, `Randomized.indicator_eq_true_iff`, `Randomized.indicator_eq_false_iff`.
