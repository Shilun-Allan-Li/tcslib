<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Quantiles Toward the Midpoint

**Claim.** Suppose $0<a<1$, $0<b<1$, $a\leq b$, and $a+b\leq1$. Then $Q(b)^2\leq Q(a)^2$.

**Proof.** Since the quantile is increasing on $(0,1)$ (`standardGaussianQuantile_strictMonoOn`), $Q(a)\leq Q(b)$. Also $b\leq1-a$, and both $b$ and $1-a$ lie in $(0,1)$, so monotonicity gives $Q(b)\leq Q(1-a)$. By complementary quantile symmetry (`standardGaussianQuantile_one_sub`), this upper bound is $-Q(a)$. Consequently $Q(a)\leq Q(b)\leq -Q(a)$. These bounds place $Q(b)$ between the two endpoints $Q(a)$ and $-Q(a)$, so its absolute value is at most $|Q(a)|$. Squaring gives the asserted inequality.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_strictMonoOn`, `BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_one_sub`.
