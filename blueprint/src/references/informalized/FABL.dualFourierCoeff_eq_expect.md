<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.dualFourierCoeff_eq_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual Fourier coefficient as an expectation

**Claim.** For a function $f:V\to\mathbb R$ and a linear functional $\psi$, the dual Fourier coefficient of $f$ at $\psi$ is the uniform expectation of $f(x)$ times the Walsh character associated with $\psi$.

**Proof.** Unfold the dual Fourier coefficient, finite-group Fourier coefficient, and uniform inner product. The inner product of real-valued functions on a finite set with uniform weights is their uniform expectation; since the real inner product is pointwise multiplication, this gives $\mathbb E_x[f(x)\,\mathrm{dualWalshCharacter}(\psi)(x)]$.
