<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.totalInfluence_eq_zero_of_isPolynomialThreshold_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Influence at Degree Zero

**Claim.** If a Boolean function has a polynomial threshold representation of Fourier degree zero, then the total influence of its real-valued sign representation is zero.

**Proof.** Choose a representing polynomial $p$. Since its Fourier degree is at most zero, every nonempty Fourier coefficient vanishes: the degree characterization (`FABL.fourierDegree_le_iff`) gives this for each nonempty set, whose cardinality is positive. The Fourier expansion (`FABL.fourier_expansion`) therefore reduces at every input to the empty-set term, so $p$ is constant. The threshold representation then makes the Boolean function, and hence its real-valued sign representation, constant as well. A constant function has zero total influence (`FABL.totalInfluence_const`), proving the claim.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.fourier_expansion`, `FABL.totalInfluence_const`.
