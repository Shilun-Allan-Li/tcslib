<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Regularity.lean :: FABL.isFourierRegular_uniformLpNorm_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Regularity from the Uniform $L^1$ Norm

**Claim.** For any real-valued function on the Boolean cube, every nonempty-set Fourier coefficient is bounded in absolute value by the uniform average of the function's absolute value.

**Proof.** Fix a coordinate set $S$. The bound for an individual Fourier coefficient by the uniform $L^1$ norm applies to $f$ and $S$ directly. In particular, it applies when $S$ is nonempty, giving the required Fourier regularity.

**Key facts.** `FABL.abs_fourierCoeff_le_uniformLpNorm_one`.
