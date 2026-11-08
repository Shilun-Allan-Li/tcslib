<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.juntaWitnessCore_isCorrelationImmune -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlation immunity of the witness core

**Claim.** If $g$ depends only on coordinates in $J$ and is correlation immune through degree $d$, then its restriction to the coordinates in $J$, with the other coordinates fixed to $+1$ and the surviving coordinates reindexed, is also correlation immune through degree $d$.

**Proof.** Take any nonempty set $T$ of at most $d$ coordinates in the restricted cube. The Fourier coefficient of the witness core indexed by $T$ equals the Fourier coefficient of $g$ indexed by the image of $T$ under the coordinate embedding (the Fourier-coefficient identity for the witness core, `fourierCoeff_juntaWitnessCore`). The image is nonempty: any element of $T$ maps to an element of that image. The embedding is injective, so the image has the same cardinality as $T$, hence at most $d$. Correlation immunity of $g$ therefore makes this coefficient zero, proving the required condition for every such $T$.

**Key facts.** `FABL.fourierCoeff_juntaWitnessCore`.
