<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.noiseOperator_one_apply_amplification -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity at Full Noise Parameter

**Claim.** For every sign-cube function and every point, the noise operator with parameter $1$ returns the function’s value at that point.

**Proof.** Expand the noise operator in its Fourier basis using the noise operator Fourier expansion (`noiseOperator_fourier_expansion`). At parameter $1$, each multiplier $1^{|S|}$ is $1$, so the resulting sum is exactly the Fourier expansion of the function at the given point. The Fourier expansion identity (`fourier_expansion`) says that this sum equals the function’s value, proving the claim.

**Key facts.** `FABL.noiseOperator_fourier_expansion`, `FABL.fourier_expansion`.
