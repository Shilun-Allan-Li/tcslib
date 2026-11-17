<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.fourierCoeff_andFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients of Conjunction

**Claim.** For the conjunction function, the empty-set coefficient is $1-2\cdot 2^{-w}$, and for every nonempty $S$ the coefficient is $-2\cdot 2^{-w}(-1)^{|S|}$.

**Proof.** Split according to whether $S$ is empty. In the empty case, the coefficient is the mean of the function, which is the probability that its value is $1$ minus the probability that its value is $-1$. The conjunction is $-1$ at exactly one cube point, so that latter probability is $2^{-w}$; the two output probabilities sum to one, giving the stated empty coefficient. In the nonempty case, apply the established formula for nonempty sets, which gives $-2\cdot 2^{-w}(-1)^{|S|}$.

**Key facts.** `FABL.fourierCoeff_andFunction_empty`, `FABL.fourierCoeff_andFunction_of_ne_empty`.
