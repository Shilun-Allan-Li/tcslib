<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/InnerProductModTwo.lean :: FABL.pow_two_le_polynomialSparsity_innerProductModTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner product threshold sparsity

**Claim.** Every nonzero polynomial threshold representation of the mod-two inner product Boolean function on two length-$n$ blocks has at least $2^n$ nonzero Fourier coefficients.

**Proof.** The Fourier coefficients of the inner product Boolean function all have absolute value $2^{-n}$ (\texttt{abs\_fourierCoeff\_innerProductModTwoBoolean}). The general threshold-representation inequality says that, for a nonzero representing polynomial, the sum of the absolute values of the target's Fourier coefficients over the polynomial's Fourier support is at least $1$ (\texttt{one\_le\_sum\_abs\_fourierCoeff\_of\_polynomialThresholdRepresentation}). On that support, each summand equals $2^{-n}$, so the sum is the number of support elements multiplied by $2^{-n}$. Hence $1\leq \mathrm{polynomialSparsity}(p)2^{-n}$, and multiplying by $2^n>0$ gives the claimed lower bound.

**Key facts.** `FABL.one_le_sum_abs_fourierCoeff_of_polynomialThresholdRepresentation`, `FABL.abs_fourierCoeff_innerProductModTwoBoolean`.
