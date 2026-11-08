<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.noiseSensitivity_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Noise Sensitivity

**Claim.** For every Boolean function and every noise rate $0\le\delta\le1$, its noise sensitivity is nonnegative.

**Proof.** By definition, noise sensitivity is a finite sum of terms of the form $p(x,y)\,q(x,y)$, where $p(x,y)$ is the probability mass of a pair and $q(x,y)$ is the indicator that the function changes. Both factors are nonnegative, so every summand is nonnegative and hence so is their sum.
