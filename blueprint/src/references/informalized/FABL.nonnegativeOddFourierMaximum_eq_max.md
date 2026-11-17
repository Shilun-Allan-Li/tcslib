<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.nonnegativeOddFourierMaximum_eq_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Odd Fourier Maximum

**Claim.** When n is positive, the nonnegative odd Fourier maximum of f equals the maximum of zero and the largest Fourier coefficient indexed by an odd-cardinality subset.

**Proof.** The odd-frequency set is nonempty when n>0, so its image under the Fourier coefficient map has a maximum. The nonnegative maximum is formed by adjoining zero to this image. The finite-set maximum identity for adjoining one element says that this new maximum is the maximum of the adjoined value, zero, and the original maximum. This is precisely the claimed equality.
