<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityCharacterizations.lean :: FABL.ProbabilityDensity.covariance_binaryFunctionOnSignCube_eq_expectation_sub_mean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Covariance Under a Density

**Claim.** For a probability density $\varphi$ and a Boolean function $h$, the covariance of the function induced by $\varphi$ on the sign cube with the real-valued version of $h$ equals the expectation of $h$ under $\varphi$, transported to the sign cube, minus the uniform mean of $h$.

**Proof.** First transport the mixed expectation on the sign cube back through the binary-to-sign bijection. This identifies the expectation of the induced function times $h$ with the density expectation of $h$ evaluated after the bijection. The same change of variables shows that the induced function has mean equal to the mean of $\varphi$ on the binary cube, which is $1$ by the defining expectation property of a probability density (\texttt{ProbabilityDensity.expect_eq_one}). Now use the covariance identity $\operatorname{Cov}(f,g)=\mathbb E[fg]-\mathbb E[f]\mathbb E[g]$, supplied by \texttt{covariance_eq_sum_fourierCoeff_mul}. Substituting the two identifications and the mean $1$ gives the asserted density expectation minus the uniform mean of $h$.

**Key facts.** `FABL.ProbabilityDensity.expect_eq_one`, `FABL.covariance_eq_sum_fourierCoeff_mul`.
