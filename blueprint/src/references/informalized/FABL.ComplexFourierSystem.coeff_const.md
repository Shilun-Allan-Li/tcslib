<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.ComplexFourierSystem.coeff_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of a constant

**Claim.** The coefficient of the constant function with value $c$ is $c$ at the distinguished index and zero at every other index.

**Proof.** Express the coefficient as the probability-weighted inner product of the basis vector at $i$ with the constant function (`FABL.ComplexFourierSystem.coeff_eq_inner`). Since the distinguished basis vector is the constant-one function, the constant function with value $c$ is $c$ times that vector. Linearity in the second argument of the inner product (`FABL.ComplexFourierSystem.pmfComplexInner_smul_right`) pulls out the factor $c$. Orthonormality makes the inner product of the basis vectors equal to one when $i$ is the distinguished index and zero otherwise, giving the stated coefficient.

**Key facts.** `FABL.ComplexFourierSystem.coeff_eq_inner`, `FABL.ComplexFourierSystem.pmfComplexInner_smul_right`.
