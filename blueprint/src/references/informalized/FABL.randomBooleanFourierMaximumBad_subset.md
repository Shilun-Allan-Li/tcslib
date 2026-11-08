<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RandomBooleanFourierMaximum.lean :: FABL.randomBooleanFourierMaximumBad_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A large Fourier maximum has a large coefficient

**Claim.** If the largest absolute Fourier coefficient of a Boolean function exceeds the threshold $T_n$, then some Fourier coefficient has absolute value at least $T_n$.

**Proof.** The Fourier infinity norm is the supremum of the absolute Fourier coefficients over the finite, nonempty collection of subsets of coordinates. If this supremum is greater than $T_n$, the finite-supremum characterization yields a subset $S$ whose coefficient has absolute value strictly greater than $T_n$. In particular, it is at least $T_n$, so the function belongs to the union of the sets indexed by such subsets.
