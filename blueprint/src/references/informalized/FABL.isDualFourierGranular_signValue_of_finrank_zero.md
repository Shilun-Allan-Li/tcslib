<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.isDualFourierGranular_signValue_of_finrank_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Granularity in Dimension Zero

**Claim.** When $V$ has dimension zero over $\mathbb F_2$, every dual Fourier coefficient of the real-valued version of a sign-valued function on $V$ is an integer multiple of $1$.

**Proof.** Dimension zero makes $V$ a subsingleton, so its only element is $0$. For any dual functional, `dualFourierCoeff_eq_expect` writes its coefficient as the uniform average of the function times the associated Walsh character. Since the average is over the singleton $\{0\}$ and the character there equals $1$, this coefficient is simply $\operatorname{signValue}(f(0))$. The value $f(0)$ is one of the two units $1$ and $-1$. In the first case the coefficient is the integer $1$ times the scale $\operatorname{degreeFourierGranularity}(1)=1$; in the second it is $-1$ times that scale. Hence every dual coefficient has the required form.

**Key facts.** `FABL.dualFourierCoeff_eq_expect`.
