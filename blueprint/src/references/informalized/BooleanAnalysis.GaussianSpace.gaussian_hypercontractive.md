<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussian_hypercontractive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian hypercontractivity

**Claim.** For $1\le p\le q$, $0\le\rho\le1$, and $\rho^2(q-1)\le p-1$ in the stated extended-real formulation, Gaussian noise maps $L^p$ into $L^q$ and does not increase the $L^p$ norm.

**Proof.** The hypotheses place $\rho$ in $[-1,1]$. If $p=q$, preservation of $L^p$ membership and contraction of the $L^p$ norm give both conclusions directly. If $p<q$ and $\rho=0$, the noise operator is the constant function equal to the mean of $f$. The norm of a constant on a probability space is its absolute value, which is at most the $L^p$ norm by the integral-versus-norm bound; this also gives the required $L^q$ membership. In the remaining case $p<q$ and $\rho\ne0$, the exponent condition implies $p>1$ and $q<\infty$, and translates to the corresponding real-exponent inequality. Test the noise output against any function in $L^\infty$. The two marginals of the correlated Gaussian pair are standard Gaussian, and the dual test bound controls each pairing by $\|f\|_p$ times the dual $L^{q/(q-1)}$ norm of the test function. The bounded-pairing criterion then yields both $L^q$ membership and the asserted norm bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianNoise_memLp`, `BooleanAnalysis.GaussianSpace.gaussianNoise_contract`, `BooleanAnalysis.GaussianSpace.gaussianNoise_zero`, `BooleanAnalysis.GaussianSpace.norm_integral_le_toReal_eLpNorm`, `BooleanAnalysis.GaussianSpace.hypercontractive_exponents_of_nonzero`, `BooleanAnalysis.GaussianSpace.hypercontractive_toReal_condition`, `BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_fst`, `BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_snd`, `BooleanAnalysis.GaussianSpace.gaussianNoise_dual_test_bound`, `BooleanAnalysis.GaussianSpace.memLp_and_eLpNorm_le_of_bounded_pairing`.
