<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.abs_vectorFourierCoeff_completeQuadratic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete Quadratic Fourier Coefficient

**Claim.** For even $n$ and $\gamma\in\mathbb F_2^n$, the absolute value of the Fourier coefficient of the real sign-valued complete quadratic function is $2^{-n/2}$.

**Proof.** Write the even integer $n$ as $m+m$. The square identity for the coefficient (`vectorFourierCoeff_completeQuadratic_sq`) says its square is $(2^{m+m})^{-1}$. Since $(2^{-m})^2=(2^{m+m})^{-1}$, the square of the absolute value of the coefficient equals $(2^{-m})^2$. Equality of squares implies that the absolute value is either $2^{-m}$ or $-2^{-m}$. The absolute value is nonnegative and $2^{-m}$ is positive, so only the first possibility holds. Finally, $n/2=m$, giving the stated value.

**Key facts.** `FABL.vectorFourierCoeff_completeQuadratic_sq`.
