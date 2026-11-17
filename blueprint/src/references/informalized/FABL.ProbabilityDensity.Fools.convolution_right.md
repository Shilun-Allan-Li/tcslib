<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/Fooling.lean :: FABL.ProbabilityDensity.Fools.convolution_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convolution Preserves Fooling

**Claim.** If a probability density \(\psi\) fools every function in a translation-closed class with error at most \(\varepsilon\), then convolving \(\psi\) with any probability density \(\phi\) preserves that error bound on the class.

**Proof.** Fix \(f\in C\). The expectation of \(f\) under the convolution is the average over shifts \(z\), weighted by \(\phi(z)\), of the \(\psi\)-expectation of the translate \(y\mapsto f(y+z)\) (\texttt{FABL.ProbabilityDensity.expectation\_convolution}). Since the class is translation-closed, each translate belongs to \(C\). For each shift, fooling bounds the difference between its \(\psi\)-expectation and its uniform mean by \(\varepsilon\); translation invariance of the uniform mean identifies that mean with the uniform mean of \(f\) (\texttt{FABL.ProbabilityDensity.expect\_translate\_add}). The weights \(\phi(z)\) are nonnegative (\texttt{FABL.ProbabilityDensity.nonneg}), so the absolute value of their weighted average of these differences is at most the weighted average of their absolute values. This is at most \(\varepsilon\) times the total weight, which is one by the density normalization (\texttt{FABL.ProbabilityDensity.expect\_eq\_one}).

**Key facts.** `FABL.ProbabilityDensity.expectation_convolution`, `FABL.ProbabilityDensity.expect_translate_add`, `FABL.ProbabilityDensity.nonneg`, `FABL.ProbabilityDensity.expect_eq_one`.
