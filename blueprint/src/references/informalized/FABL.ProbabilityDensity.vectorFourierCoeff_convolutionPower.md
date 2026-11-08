<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBias.lean :: FABL.ProbabilityDensity.vectorFourierCoeff_convolutionPower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of convolution powers

**Claim.** For a probability density $\phi$, a nonnegative integer $d$, and a cube point $\gamma$, the Fourier coefficient of the $d$th convolution power of $\phi$ at $\gamma$ is the $d$th power of the Fourier coefficient of $\phi$ at $\gamma$.

**Proof.** Proceed by induction on $d$. For $d=0$, the convolution power is the point mass at zero. Its Fourier coefficient is $1$ at every frequency, which is also the zeroth power of the coefficient of $\phi$. For the step from $d$ to $d+1$, the $(d+1)$st convolution power is the convolution of the $d$th power with $\phi$. Fourier coefficients turn convolution into multiplication (\(\texttt{FABL.binaryFourierCoeff_convolution}\)), so the coefficient in question is the product of the coefficient at stage $d$ and the coefficient of $\phi$. The induction hypothesis makes this the $d$th power times the coefficient of $\phi$, hence the $(d+1)$st power.

**Key facts.** `FABL.binaryFourierCoeff_subsetDensity_singleton_zero`, `FABL.binaryFourierCoeff_convolution`.
