<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Majority.lean :: BooleanAnalysis.ThresholdFunctions.sum_fourier_sq_eq_sum_weightLevel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier sums grouped by degree

**Claim.** The sum over cube subsets of $g(|S|)\widehat f(S)^2$ equals the sum, over degrees $k=0,\ldots,n$, of $g(k)$ times the Fourier weight at level $k$.

**Proof.** Group the finite sum over all subsets $S$ according to their cardinality. Every such cardinality is at most $n$, so it lies in the range $0,\ldots,n$. For each fixed degree $k$, the contribution from the fiber $|S|=k$ is $g(k)$ times the sum of $\widehat f(S)^2$ over precisely those subsets; by the definition of the level weight, this is $g(k)W_k[f]$. Summing these fiber contributions gives the identity.
