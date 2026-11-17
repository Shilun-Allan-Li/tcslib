<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Hoeffding.lean :: weighted_exp_le_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted exponential affine bound

**Claim.** For a probability vector $p$ and numbers $\ell_i\in[0,1]$, the weighted sum of $e^{-\eta\ell_i}$ is at most $1-(1-e^{-\eta})\sum_i p_i\ell_i$, for every real $\eta$.

**Proof.** For each $i$, convexity of the exponential gives the chord bound $e^{-\eta\ell_i}\le 1-\ell_i+\ell_i e^{-\eta}$ when $0\le\ell_i\le1$ (the fact proved in `exp_convexity_bound'`). Multiply by $p_i\ge0$ and sum over $i$. The resulting right-hand side is $\sum_i p_i-(\sum_i p_i\ell_i)+e^{-\eta}(\sum_i p_i\ell_i)$. Using $\sum_i p_i=1$ and collecting terms yields the stated bound.

**Key facts.** `exp_convexity_bound'`.
