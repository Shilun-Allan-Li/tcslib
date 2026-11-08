<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.fourierCoeff_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of constants

**Claim.** The Fourier coefficient of the constant function with value $c$ is $c$ at the zero multi-index and zero at every other multi-index.

**Proof.** The constant function with value $c$ is $c$ times the constant-one function. By homogeneity of Fourier coefficients (\texttt{fourierCoeff_smul}), its coefficient is $c$ times that of the constant-one function. The constant-one function is the product basis function at the zero multi-index, since every coordinate basis function there is constant one (\texttt{productFunction_zero}). Orthonormality of the product basis (\texttt{productFunction_orthonormal}) says its inner product with the basis function indexed by $a$ is one when $a$ is the zero multi-index and zero otherwise. Multiplication by $c$ yields the formula.

**Key facts.** `FABL.FiniteFourierBasis.fourierCoeff_smul`, `FABL.FiniteFourierBasis.productFunction_zero`, `FABL.FiniteFourierBasis.productFunction_orthonormal`.
