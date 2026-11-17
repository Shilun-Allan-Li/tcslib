<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/FourierNorms.lean :: FABL.ProbabilityDensity.abs_expectation_signFunction_sub_mean_le_fourierOneNorm_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation Error from Fourier Norm

**Claim.** For a real-valued function on the sign cube and an \(\varepsilon\)-biased density, the absolute difference between the density expectation and the uniform mean is at most the function's Fourier one-norm times \(\varepsilon\), assuming \(\varepsilon\ge0\).

**Proof.** Transfer the density to the sign cube using the coordinatewise identification between the binary cube and the sign cube. Under this identification, the mixed expectation of the transferred density times \(f\) equals the density expectation of \(f\), and the transferred density has mean one by normalization. The covariance of the transferred density with \(f\) is consequently exactly the difference between that density expectation and the uniform mean. Bias is equivalent to Fourier regularity of the transferred density (\texttt{FABL.ProbabilityDensity.isBiased\_iff\_isFourierRegular}); Fourier regularity implies low-degree Fourier regularity at every degree (\texttt{FABL.IsFourierRegular.isLowDegreeFourierRegular}). Apply the covariance bound for a low-degree Fourier-regular function, which bounds its covariance with a function of degree at most \(n\) by the latter's Fourier one-norm times \(\varepsilon\) (\texttt{FABL.IsLowDegreeFourierRegular.abs\_covariance\_le\_fourierOneNorm\_mul}). The degree of any function on the \(n\)-dimensional sign cube is at most \(n\) (\texttt{FABL.fourierDegree\_le\_dimension}), giving the stated inequality.

**Key facts.** `FABL.ProbabilityDensity.expect_eq_one`, `FABL.ProbabilityDensity.isBiased_iff_isFourierRegular`, `FABL.covariance_eq_sum_fourierCoeff_mul`, `FABL.IsFourierRegular.isLowDegreeFourierRegular`, `FABL.fourierDegree_le_dimension`, `FABL.IsLowDegreeFourierRegular.abs_covariance_le_fourierOneNorm_mul`.
