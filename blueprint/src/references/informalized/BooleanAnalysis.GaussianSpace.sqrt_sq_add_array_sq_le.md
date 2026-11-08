<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianBobkov.lean :: BooleanAnalysis.GaussianSpace.sqrt_sq_add_array_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Approximation Bound for Repeated Coordinates

**Claim.** If $m>0$, $e\ge0$, and every $d_{ij}$ is within $e$ of $g_i/\sqrt m$, then $\sqrt{P^2+\sum_{i=1}^n\sum_{j=1}^m d_{ij}^2}\le\sqrt{P^2+\sum_{i=1}^n g_i^2}+\sqrt{nm}\,e$.

**Proof.** Index the pairs $(i,j)$ by the finite product set. Apply the Euclidean length bound under perturbation (`BooleanAnalysis.GaussianSpace.sqrt_sq_add_sum_sq_le_add_error`) to the arrays $d_{ij}$ and $g_i/\sqrt m$. The squared norm of the second array is $\sum_i g_i^2$: for each fixed $i$, its $m$ repeated terms contribute $m(g_i/\sqrt m)^2=g_i^2$, using $m>0$. Each coordinate error has absolute value at most $e$, so the sum of squared errors over the $nm$ pairs is at most $nm e^2$. Its square root is at most $\sqrt{nm}\,e$, since $e\ge0$. Substituting these two estimates into the perturbation bound gives the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.sqrt_sq_add_sum_sq_le_add_error`.
