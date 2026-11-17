<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLR.lean :: FABL.sq_le_expectation_convolution_sq_of_derandomizedBLRAcceptanceProbability_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Bias Bounded by Convolution Second Moment

**Claim.** If the derandomized BLR acceptance probability is $1/2+\theta/2$, then $\theta^2$ is at most the density-weighted expectation of the squared convolution of the sign-encoded function with itself.

**Proof.** Let $F$ be the real sign-encoded function and let $C=F*F$ be its convolution with itself. The centering identity for the acceptance probability states that twice the acceptance probability minus one is the density-weighted expectation of $F(y)C(y)$ (`two_mul_derandomizedBLRAcceptanceProbability_sub_one`). Using the given acceptance probability, this identifies $\theta$ with that expectation. The density expectation satisfies the second-moment inequality $(\mathbb E_\phi g)^2\leq\mathbb E_\phi(g^2)$ (`ProbabilityDensity.sq_expectation_le_expectation_sq`), so apply it to $g(y)=F(y)C(y)$. Since $F$ is sign-valued (`isSignValued_realSignEncodedFunction`), $F(y)^2=1$, and therefore $(F(y)C(y))^2=C(y)^2$ pointwise. Substitution yields the desired bound.

**Key facts.** `FABL.two_mul_derandomizedBLRAcceptanceProbability_sub_one`, `FABL.isSignValued_realSignEncodedFunction`, `FABL.ProbabilityDensity.sq_expectation_le_expectation_sq`.
