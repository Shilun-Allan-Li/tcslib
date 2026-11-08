<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.tendsto_signedHammingTwoTailEpsilon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Signed Hamming Tail Coefficient

**Claim.** For every real $t$, twice the absolute value of the singleton Fourier coefficient of the indicated upper-tail event on the uniform sign cube of dimension $m+1$ tends to $0$ as $m\to\infty$.

**Proof.** The singleton Fourier coefficient equals the expectation of the upper-tail indicator multiplied by the normalized Rademacher sum, divided by $\sqrt{m+1}$ (the singleton Fourier coefficient formula, `FABL.fourierCoeff_hammingUpperTailIndicator_singleton`). The numerator tends to the finite value given by the standard Gaussian density at $t$ (`FABL.tendsto_expect_hammingUpperTailIndicator_mul_normalizedRademacherSum`). Meanwhile, $1/\sqrt{m+1}\to0$ (`FABL.tendsto_inv_sqrt_nat_succ`). Thus the coefficient, a product of these two quantities, tends to $0$. Multiplication by $2$ and taking absolute values preserve convergence, with limiting value $|2\cdot0|=0$.

**Key facts.** `FABL.fourierCoeff_hammingUpperTailIndicator_singleton`, `FABL.tendsto_expect_hammingUpperTailIndicator_mul_normalizedRademacherSum`, `FABL.tendsto_inv_sqrt_nat_succ`.
