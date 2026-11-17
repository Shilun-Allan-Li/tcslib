<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BasicFourierFormulas.lean :: FABL.variance_eq_sum_sq_fourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance and nonconstant Fourier coefficients

**Claim.** For a real-valued function on the sign cube, its variance equals its second moment minus the square of its mean, and also the sum of the squares of its nonempty Fourier coefficients.

**Proof.** Expanding $(f-\mathbb E f)^2$ and using linearity of expectation gives $\operatorname{Var}(f)=\mathbb E[f^2]-(\mathbb E f)^2$. Parseval's identity (`parseval`) writes the second moment as the sum of the squares of all Fourier coefficients, while the mean is the empty-set coefficient (`mean_eq_fourierCoeff_empty`). The empty-set term in the Parseval sum is therefore exactly the squared mean. Removing that term leaves the sum over nonempty subsets, which proves the second identity.

**Key facts.** `FABL.parseval`, `FABL.mean_eq_fourierCoeff_empty`.
