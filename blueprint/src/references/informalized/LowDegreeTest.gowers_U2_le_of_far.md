<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.gowers_U2_le_of_far -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A $U^2$ bound from low-degree farness

**Claim.** If $f$ is $\varepsilon$-far from degree at most $d$, then the fourth power of the $U^2$ norm of its $\pm1$ lift is at most $(1-2\varepsilon)^2$.

**Proof.** By the Fourier formula for the $U^2$ norm (`gowers_U2_fourier`), the norm power is the sum of the fourth powers of the Fourier coefficients. The absolute coefficient bound from farness (`abs_fourier_coeff_le_of_far_from_degree`) implies that each squared coefficient is at most $(1-2\varepsilon)^2$. Thus each fourth power is at most that bound times the squared coefficient, and summing gives an upper bound of $(1-2\varepsilon)^2$ times the sum of squared coefficients. Parseval's identity for the $\pm1$ lift (`parseval_pm1`) says that this latter sum is $1$, proving the result.

**Key facts.** `LowDegreeTest.gowers_U2_fourier`, `LowDegreeTest.abs_fourier_coeff_le_of_far_from_degree`, `LowDegreeTest.parseval_pm1`.
