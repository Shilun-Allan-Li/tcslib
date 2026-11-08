<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.oddBLRAcceptanceProbability_eq_one_iff_oddParity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perfect Acceptance Characterizes Odd Parity

**Claim.** The odd BLR test accepts a sign-valued function $f$ on the sign cube with probability one exactly when $f$ is a parity function associated with a subset of odd cardinality.

**Proof.** For the forward direction, the acceptance bound in terms of the nonnegative odd Fourier maximum (\(\texttt{oddBLRAcceptanceProbability\_le\_correctedMaximum}\)) shows that acceptance probability one forces this maximum to be at least one. The maximum is also at most one (\(\texttt{nonnegativeOddFourierMaximum\_le\_one\_amplification}\)), so it equals one. By the definition of this finite maximum, the value one must occur among the odd-cardinality Fourier coefficients: it cannot be the extra value zero. Thus some odd-cardinality set $S$ has Fourier coefficient one.

The Fourier coefficient is the uniform inner product with the monomial indexed by $S$ (\(\texttt{fourierCoeff\_eq\_uniformInner}\)); that monomial is the real-valued form of the parity function (\(\texttt{parityFunction\_toReal}\)). The inner product of two sign-valued functions equals one minus twice their relative Hamming distance (\(\texttt{uniformInner\_eq\_one\_sub\_two\_mul\_relativeHammingDist}\)). Since the coefficient is one, this distance is zero, so the functions agree everywhere (\(\texttt{eq\_of\_relativeHammingDist\_eq\_zero\_amplification}\)). Hence $f$ is that odd parity.

Conversely, suppose $f$ is parity on an odd-cardinality set $S$. The tester's Fourier-sum formula (\(\texttt{oddBLRAcceptanceProbability\_eq\_fourierSum}\)) and the fact that a monomial has Fourier coefficient one at its own set and zero elsewhere (\(\texttt{fourierCoeff\_monomial}\)) make the sum contain exactly one nonzero contribution, equal to one. Substitution gives acceptance probability one.

**Key facts.** `FABL.oddBLRAcceptanceProbability_le_correctedMaximum`, `FABL.nonnegativeOddFourierMaximum_le_one_amplification`, `FABL.uniformInner_eq_one_sub_two_mul_relativeHammingDist`, `FABL.parityFunction_toReal`, `FABL.fourierCoeff_eq_uniformInner`, `FABL.eq_of_relativeHammingDist_eq_zero_amplification`, `FABL.oddBLRAcceptanceProbability_eq_fourierSum`, `FABL.fourierCoeff_monomial`.
