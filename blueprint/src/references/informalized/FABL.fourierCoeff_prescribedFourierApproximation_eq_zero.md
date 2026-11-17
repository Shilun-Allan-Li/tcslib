<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.fourierCoeff_prescribedFourierApproximation_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing outside the prescribed family

**Claim.** For a nonempty family $\mathcal F$ and $T\notin\mathcal F$, the prescribed Fourier approximation has Fourier coefficient zero at $T$.

**Proof.** Expand the coefficient of the approximation as the expectation of its defining sum over inputs $a$, multiplied by the character at $T$. Distribute the character over the sum and interchange the finite sum and expectation. For each fixed $a$, pull the scalar $f(a)$ outside the expectation; the remaining expectation is the coefficient of the prescribed Fourier kernel at $T$. That kernel coefficient is $(|\mathcal F|^{-1})\chi_T(a)$ when $T\in\mathcal F$ and zero otherwise (`fourierCoeff_prescribedFourierKernel`). Since $T\notin\mathcal F$, every summand vanishes, and thus the full coefficient is zero.

**Key facts.** `FABL.fourierCoeff_prescribedFourierKernel`.
