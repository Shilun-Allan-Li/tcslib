<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov.lean :: BooleanAnalysis.GaussianSpace.bobkovFunctional_noise_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Contraction of the Bobkov Functional

**Claim.** If $f$ takes values in $[0,1]$ and $0\le\rho\le1$, then applying the Boolean noise operator does not increase the Bobkov functional: $B(T_\rho f)\le B(f)$.

**Proof.** Apply the extended-functional noise contraction theorem with the closed Gaussian profile as its profile function. Its hypotheses are supplied by continuity of the profile on $[0,1]$ (`continuousOn_closedGaussianProfile`), its nonnegativity (`closedGaussianProfile_nonneg`), and the two-point inequality controlling the profile across a Boolean coordinate (`bobkov_two_point`). Take no auxiliary functions in the extended functional. With this choice, the extended functional reduces to the Bobkov functional: the auxiliary-gradient sum is empty, and the integrand is exactly the square root of the squared profile plus the sum of squared coordinate derivatives. The extended contraction theorem (`extendedFunctional_noise_le`) therefore gives the claimed inequality.

**Key facts.** `BooleanAnalysis.GaussianSpace.BobkovInterpolation.extendedFunctional_noise_le`, `BooleanAnalysis.GaussianSpace.continuousOn_closedGaussianProfile`, `BooleanAnalysis.GaussianSpace.closedGaussianProfile_nonneg`, `BooleanAnalysis.GaussianSpace.bobkov_two_point`.
