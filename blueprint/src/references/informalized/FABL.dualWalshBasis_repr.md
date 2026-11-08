<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.dualWalshBasis_repr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients as basis coordinates

**Claim.** The coordinate of $f$ in the dual Walsh basis at $\psi$ equals the dual Fourier coefficient of $f$ at $\psi$.

**Proof.** Expand $f$ in the dual Walsh basis. For each $x$, its value is the sum over $\phi$ of the basis coordinate at $\phi$ times the Walsh character at $x$. By orthogonality of Walsh characters, the expectation of the product of the characters indexed by $\phi$ and $\psi$ is $1$ if $\phi=\psi$ and $0$ otherwise (\texttt{FABL.expect_dualWalshCharacter_mul}). Thus the coordinate at $\psi$ equals the sum of the basis coordinates weighted by these orthogonality factors. Rewrite each factor as the corresponding character-product expectation, pull the constant coordinate into the expectation, and interchange the finite sum and expectation. The basis expansion then reduces the integrand to $f(x)$ times the Walsh character at $\psi$. This is the dual Fourier coefficient by the coefficient-as-expectation identity (\texttt{FABL.dualFourierCoeff_eq_expect}).

**Key facts.** `FABL.expect_dualWalshCharacter_mul`, `FABL.dualFourierCoeff_eq_expect`.
