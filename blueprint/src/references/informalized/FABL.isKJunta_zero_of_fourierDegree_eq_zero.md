<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.isKJunta_zero_of_fourierDegree_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Fourier degree gives a constant

**Claim.** If the real sign representation of a Boolean function has Fourier degree zero, then the function depends on at most zero coordinates.

**Proof.** Fourier degree zero implies that the set of relevant coordinates of the real representation is empty (\texttt{relevantCoordinates\_toReal\_eq\_empty\_of\_fourierDegree\_eq\_zero}). The general fact that a bound on the number of relevant coordinates yields a junta of that size (\texttt{isKJunta\_of\_card\_relevantCoordinates\_toReal\_le}) now gives a $0$-junta, since the empty set has cardinality zero.

**Key facts.** `FABL.relevantCoordinates_toReal_eq_empty_of_fourierDegree_eq_zero`, `FABL.isKJunta_of_card_relevantCoordinates_toReal_le`.
