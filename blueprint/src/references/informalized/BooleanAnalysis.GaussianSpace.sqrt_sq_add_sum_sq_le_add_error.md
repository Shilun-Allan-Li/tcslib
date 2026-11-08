<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianBobkov.lean :: BooleanAnalysis.GaussianSpace.sqrt_sq_add_sum_sq_le_add_error -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Euclidean Length Bound Under Perturbation

**Claim.** For a finite index set $I$, a real number $P$, and real numbers $d_i,g_i$ for each $i\in I$, $\sqrt{P^2+\sum_{i\in I}d_i^2}\le\sqrt{P^2+\sum_{i\in I}g_i^2}+\sqrt{\sum_{i\in I}(d_i-g_i)^2}$.

**Proof.** Form two vectors indexed by the disjoint union of one extra coordinate and $I$: let the first have coordinates $P$ and $d_i$, and the second have coordinates $P$ and $g_i$. The first vector is the sum of the second and their difference. The triangle inequality for the Euclidean norm bounds the first vector's norm by the second vector's norm plus the norm of the difference. These three norms are exactly the three square-root expressions in the statement.
