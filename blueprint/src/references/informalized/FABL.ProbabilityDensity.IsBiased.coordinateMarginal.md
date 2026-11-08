<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBiasMarginals.lean :: FABL.ProbabilityDensity.IsBiased.coordinateMarginal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bias of Coordinate Marginals

**Claim.** Every coordinate marginal of an \(\varepsilon\)-biased density is itself \(\varepsilon\)-biased.

**Proof.** Fix a nonzero frequency \(\gamma\) on the selected coordinates. The Fourier coefficient of the marginal at \(\gamma\) equals the original density's coefficient at the frequency obtained by lifting \(\gamma\) to the full coordinate set (\texttt{FABL.ProbabilityDensity.vectorFourierCoeff\_coordinateMarginal}). This lifted frequency is nonzero whenever \(\gamma\) is nonzero (\texttt{FABL.coordinateFrequencyLift\_ne\_zero}). The original bias bound therefore applies to that coefficient and proves the marginal's required bound.

**Key facts.** `FABL.ProbabilityDensity.vectorFourierCoeff_coordinateMarginal`, `FABL.coordinateFrequencyLift_ne_zero`.
