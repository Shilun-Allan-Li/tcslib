<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.booleanInfluence_eq_uniformProbability_discreteDerivative_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence as a derivative event

**Claim.** For a Boolean function and coordinate $i$, the influence equals the probability that the discrete derivative in coordinate $i$ is nonzero.

**Proof.** It suffices to compare the two events at each input. The discrete derivative is nonzero exactly when the function's real-valued version takes different values at the two inputs obtained by setting coordinate $i$ to $1$ and to $-1$ (`discreteDerivative_ne_zero_iff`). Pivotality is equivalent to those same two restrictions of the original function being different (`isPivotal_iff_setCoordinate_ne`). Since the real-valued version is obtained by applying the injective map `signValue`, the two restrictions differ as real numbers exactly when they differ as signs (`signValue_injective`). The events therefore agree pointwise, and hence have equal uniform probabilities.

**Key facts.** `FABL.discreteDerivative_ne_zero_iff`, `FABL.isPivotal_iff_setCoordinate_ne`, `FABL.signValue_injective`.
