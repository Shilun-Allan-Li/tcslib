<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricAsymptotics.lean :: FABL.log_inv_standardGaussianDensity_div_isEquivalent_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic Gaussian Logarithmic Growth

**Claim.** As $t\to+\infty$, the logarithm of the reciprocal of the standard Gaussian density at $t$, divided by $t$, is asymptotic to $t^2/2$.

**Proof.** To prove asymptotic equivalence, it suffices to show that the ratio of the two functions tends to $1$; the comparison function $t^2/2$ is nonzero for all sufficiently large $t$. For positive $t$, the preceding logarithmic identity writes this ratio as $1+2(\log t/t^2)+2(\log\sqrt{2\pi}/t^2)$. The first added term tends to zero because $\log t/t\to0$ and $1/t\to0$, and the second tends to zero because its numerator is constant while $t^2\to\infty$. Hence the ratio tends to $1$.

**Key facts.** `FABL.log_inv_standardGaussianDensity_div`.
