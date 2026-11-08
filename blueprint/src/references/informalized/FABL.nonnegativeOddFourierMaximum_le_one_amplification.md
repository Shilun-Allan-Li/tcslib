<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.nonnegativeOddFourierMaximum_le_one_amplification -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for the Nonnegative Odd Maximum

**Claim.** For every Boolean function f, its nonnegative odd Fourier maximum is at most 1.

**Proof.** The maximum is taken over a finite set consisting of zero and the Fourier coefficients indexed by odd-cardinality subsets. Zero is at most 1. Each coefficient in the image is at most 1 by the coefficient bound (`fourierCoeff_le_one_amplification`). Hence every element of the set is at most 1, and so is its maximum.

**Key facts.** `FABL.fourierCoeff_le_one_amplification`.

**Caveat.** The supplied informal statement describes an Odd BLR acceptance inequality, but the formal declaration and proof establish the auxiliary upper bound stated in the claim.
