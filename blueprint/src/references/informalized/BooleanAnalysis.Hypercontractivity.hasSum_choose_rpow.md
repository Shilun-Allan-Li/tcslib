<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.hasSum_choose_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Generalized Binomial Series

**Claim.** If $|x|<1$, the generalized binomial series with coefficients $\binom{s}{k}$ converges to $(1+x)^s$.

**Proof.** The analytic binomial power-series theorem says that the power series for $(1+z)^s$ about $z=0$ converges to that function throughout the open unit ball. Since $|x|<1$, the real number $x$ lies in this ball. Evaluating the series there gives terms $\binom{s}{k}x^k$; identifying the power-series coefficients with the generalized binomial coefficients yields the stated sum.
