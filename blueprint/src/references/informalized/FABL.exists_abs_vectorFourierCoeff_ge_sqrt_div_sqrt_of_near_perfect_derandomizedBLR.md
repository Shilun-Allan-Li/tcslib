<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLR.lean :: FABL.exists_abs_vectorFourierCoeff_ge_sqrt_div_sqrt_of_near_perfect_derandomizedBLR -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient from Near-Perfect Acceptance

**Claim.** Under the stated bias and near-perfect acceptance assumptions, some frequency has vector Fourier coefficient of the real sign encoding with absolute value at least $\sqrt{1-2\delta-\varepsilon}/\sqrt{1-\varepsilon}$.

**Proof.** Put $F$ equal to the real sign encoding of $f$. Rewriting the acceptance probability as $\tfrac12+\tfrac12(1-2\delta)$ lets the affine-correlation theorem provide an affine function whose correlation with $F$ is at least $\sqrt{(1-2\delta)^2-\varepsilon}/\sqrt{1-\varepsilon}$. The sign encoding of an affine function factors as its constant sign times its Walsh character (`realSignEncodedFunction_affineFunction`, `affineSignFunction_apply`). Thus this correlation is a signed Fourier coefficient of $F$; since the constant sign is $\pm1$ (`signValue_eq_neg_one_or_one`), the absolute value of that coefficient is at least the same bound. The near-perfect assumption and $\varepsilon<1$ yield $\tfrac12\le ((1-2\delta)^2-\varepsilon)/(1-\varepsilon)$. Taking square roots gives a squared coefficient of at least $1/2$. The acceptance upper bound in terms of that squared coefficient (`two_mul_derandomizedBLRAcceptanceProbability_sub_one_le_of_half_le_sq`) then implies $ (1-2\delta-\varepsilon)/(1-\varepsilon)$ is no greater than the squared coefficient. Taking square roots once more proves the claim. The Fourier coefficient is identified with the uniform expectation against the Walsh character by `vectorFourierCoeff_eq_expect`.

**Key facts.** `FABL.exists_affine_correlation_ge_sqrt_div_sqrt_of_derandomizedBLRAcceptanceProbability_eq`, `FABL.realSignEncodedFunction_affineFunction`, `FABL.affineSignFunction_apply`, `FABL.signValue_eq_neg_one_or_one`, `FABL.vectorFourierCoeff_eq_expect`, `FABL.two_mul_derandomizedBLRAcceptanceProbability_sub_one_le_of_half_le_sq`.
