<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.completeQuadraticBoolean_ne_one_of_pos_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonconstancy of the quadratic Boolean function

**Claim.** For every positive even integer $n$, the complete quadratic Boolean function on $n$ sign coordinates is not constantly $1$.

**Proof.** Choose a coordinate $i\in\mathrm{Fin}(n)$, which exists since $n>0$, and suppose the function were constantly $1$. Its real form would then be the constant function $1$. The Fourier coefficient of this constant function on the nonempty set $\{i\}$ is zero: by the definition of the coefficient, this is the expectation of the corresponding nonconstant monomial, whose expectation is zero (`expect_monomial`). On the other hand, the absolute value of every Fourier coefficient of the complete quadratic Boolean function in even dimension is $2^{-n/2}$ (`abs_fourierCoeff_completeQuadraticBoolean`). This number is strictly positive, contradicting the zero coefficient. Thus the function is not constantly $1$.

**Key facts.** `FABL.expect_monomial`, `FABL.abs_fourierCoeff_completeQuadraticBoolean`.
