<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.fourierCoeff_juntaWitnessCore -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of a junta witness

**Claim.** If $g$ depends only on coordinates in $J$, then the coefficient of its restriction to the free coordinates of $J$ at $T$ equals the coefficient of $g$ at the corresponding coordinates of $J$.

**Proof.** Translate $T$ through the increasing enumeration of $J$ to a frequency $A$ on the free coordinates. Reindexing the cube average identifies the coefficient of the restricted function with the indexed Fourier coefficient of the restriction of $g$ when all fixed coordinates are set to $1$. Since $g$ depends only on $J$, changing the fixed coordinates cannot change this restriction: the free-coordinate values in the two combined inputs agree on every coordinate in $J$, by the free-coordinate property of `combineSignCube_apply_free`. Therefore this indexed coefficient is the same for every fixed-coordinate assignment. Averaging it over those assignments gives the full coefficient of $g$ at the lifted frequency, by the restriction-averaging identity (`expect_restrictionFourierCoeff`). The lifted frequency is exactly the image of $T$ under the coordinate embedding, which proves the claim.

**Key facts.** `FABL.combineSignCube_apply_free`, `FABL.expect_restrictionFourierCoeff`.
