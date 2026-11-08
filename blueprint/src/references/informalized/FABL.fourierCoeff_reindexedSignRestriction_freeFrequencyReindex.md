<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.fourierCoeff_reindexedSignRestriction_freeFrequencyReindex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction Fourier Reindexing

**Claim.** For a Boolean function, a fixed assignment outside $J$, and a frequency $S$ supported on $J$, the Fourier coefficient on the reindexed free cube equals the Fourier coefficient of the restricted function at $S$.

**Proof.** Apply the reindexing identity for Fourier coefficients on the free cube: the coefficient at a frequency $T$ equals the indexed Fourier coefficient of the restriction at the frequency obtained by transporting $T$ back along the coordinate equivalence (`fourierCoeff_reindexedSignRestriction`). Take $T$ to be the reindexing of $S$. The map-back identity (`map_freeFrequencyReindex_symm`) says that this transported frequency is exactly $S$. By the definition of the restriction Fourier coefficient, the resulting indexed coefficient is the desired right-hand side.

**Key facts.** `FABL.fourierCoeff_reindexedSignRestriction`, `FABL.map_freeFrequencyReindex_symm`.
