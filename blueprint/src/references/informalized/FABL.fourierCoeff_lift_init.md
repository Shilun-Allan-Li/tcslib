<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.fourierCoeff_lift_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient under coordinate extension

**Claim.** Extending a function on the $k$-dimensional cube by ignoring the last coordinate preserves its Fourier coefficient at a frequency embedded among the first $k$ coordinates.

**Proof.** Parametrize each point of the $(k+1)$-dimensional cube by a pair consisting of its first $k$ coordinates and its last coordinate. The coefficient becomes the expectation over these pairs. The monomial at the embedded frequency is independent of the last coordinate (`FABL.monomial_map_castSucc_snoc`), as is the extended function. Averaging over the last coordinate therefore leaves the expectation over the first $k$ coordinates, exactly the original Fourier coefficient.

**Key facts.** `FABL.monomial_map_castSucc_snoc`.
