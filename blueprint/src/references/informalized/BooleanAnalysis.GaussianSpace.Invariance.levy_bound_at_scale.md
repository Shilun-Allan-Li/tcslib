<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceDistribution.lean :: BooleanAnalysis.GaussianSpace.Invariance.levy_bound_at_scale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lévy bound from smooth tests

**Claim.** Under the assumed bound on differences of integrals of smooth test functions in terms of their derivative bounds, the Lévy distance is at most $(m+2)\eta+(2^m/\eta^{m+1})B$ for every $\eta>0$.

**Proof.** Fix a threshold $u$. Choose the smooth cutoff supplied by `exists_contDiff_cutoff`: it takes values in $[0,1]$, equals $1$ to the left of $u$, vanishes to the right of $u+(m+2)\eta$, and its $(m+1)$st derivative is bounded by $C=2^m/\eta^{m+1}$. The integral sandwich fact (`integral_cutoff_sandwich`) places each measure's CDF at $u$ below the cutoff integral and places that integral below its CDF at $u+(m+2)\eta$. Applying this for both measures and using the assumed test-function error, whose absolute-value bound gives both directions of comparison, shows that each CDF at $u$ is at most the other's CDF at $u+(m+2)\eta$ plus $CB$. The comparison lemma (`levyDistance_le_of_cdf_comparison`) now applies with shift $(m+2)\eta$ and error $CB$, yielding the stated bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.exists_contDiff_cutoff`, `BooleanAnalysis.GaussianSpace.Invariance.integral_cutoff_sandwich`, `BooleanAnalysis.GaussianSpace.Invariance.levyDistance_le_of_cdf_comparison`.
