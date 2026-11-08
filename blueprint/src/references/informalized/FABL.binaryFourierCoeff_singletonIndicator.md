<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.binaryFourierCoeff_singletonIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient of the zero-vector indicator

**Claim.** For any coordinate set $S$ in dimension $n$, the Fourier coefficient of the indicator of the zero vector is $2^{-n}$.

**Proof.** Write the Fourier coefficient as the uniform average, or equivalently the sum over all cube points divided by the cube's cardinality. Since the function is zero away from the zero vector, only that point contributes; its character value is $1$, because every coordinate sum at the zero vector is zero. The cube has $2^n$ points, so the average is $1/2^n$.
