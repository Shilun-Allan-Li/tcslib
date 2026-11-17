<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.pow_two_half_le_polynomialSparsity_completeQuadraticBoolean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sparsity Bound for a Quadratic Threshold Representation

**Claim.** For even $n$, any nonzero polynomial whose threshold sign represents the complete quadratic Boolean function has at least $2^{n/2}$ nonzero Fourier coefficients.

**Proof.** The threshold-representation bound says that the sum of the absolute Fourier coefficients of the represented Boolean function over any family containing the support of the representing polynomial is at least $1$ (`one_le_sum_abs_fourierCoeff_of_polynomialThresholdRepresentation`). Apply it to the polynomial's Fourier support itself. For even $n$, every Fourier coefficient of the complete quadratic Boolean function has absolute value $2^{-n/2}$ (`abs_fourierCoeff_completeQuadraticBoolean`). Thus the sum over the support is its cardinality multiplied by $2^{-n/2}$. Since this sum is at least $1$, the support has cardinality at least $2^{n/2}$, as claimed.

**Key facts.** `FABL.one_le_sum_abs_fourierCoeff_of_polynomialThresholdRepresentation`, `FABL.abs_fourierCoeff_completeQuadraticBoolean`.
