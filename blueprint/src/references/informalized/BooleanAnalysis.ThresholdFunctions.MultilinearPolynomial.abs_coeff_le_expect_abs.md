<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Polynomial.lean :: BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.abs_coeff_le_expect_abs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient bound by absolute mean

**Claim.** Each Walsh coefficient of a polynomial is bounded in absolute value by the uniform expectation of the absolute value of that polynomial on the Boolean cube.

**Proof.** The coefficient of $S$ in the Walsh expansion of the evaluation function equals $p(S)$ (\texttt{MultilinearPolynomial.fourierCoeff_eval}). Thus it suffices to bound the absolute value of the corresponding Fourier coefficient. Writing that coefficient as the uniform average of $p(x)\chi_S(x)$, the absolute value of an average is at most the average of the absolute values. Since every character takes values of absolute value one—equivalently, its square is one (\texttt{chiS_sq_eq_one})—we have $|p(x)\chi_S(x)|=|p(x)|$. The uniform expectation agrees with the finite uniform average (\texttt{expect_eq_fintypeExpect}), yielding the result.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.fourierCoeff_eval`, `BooleanAnalysis.expect_eq_fintypeExpect`, `BooleanAnalysis.chiS_sq_eq_one`.
