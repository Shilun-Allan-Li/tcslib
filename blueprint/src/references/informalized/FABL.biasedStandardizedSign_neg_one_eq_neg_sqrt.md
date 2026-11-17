<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedStandardizedSign_neg_one_eq_neg_sqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standardized Negative Sign Formula

**Claim.** For $p\in(0,1)$, the standardized value of the negative sign is $-\sqrt{(1-p)/p}$.

**Proof.** The standardized value at $-1$ is known to equal $-2(1-p)/\sigma$, where $\sigma$ is the positive bias standard deviation. It remains to identify the positive quantities $2(1-p)/\sigma$ and $\sqrt{(1-p)/p}$. Both are nonnegative. Their squares agree: using $\sigma^2=4p(1-p)$, the first square is $4(1-p)^2/[4p(1-p)]=(1-p)/p$, which is the square of the second. Positivity of $p$ and $1-p$ justifies cancellation. Hence the quantities are equal, and the negative signs give the asserted formula.

**Key facts.** `FABL.biasedStandardizedSign_neg_one_eq`, `FABL.biasSigma_pos`, `FABL.biasSigma_sq`.
