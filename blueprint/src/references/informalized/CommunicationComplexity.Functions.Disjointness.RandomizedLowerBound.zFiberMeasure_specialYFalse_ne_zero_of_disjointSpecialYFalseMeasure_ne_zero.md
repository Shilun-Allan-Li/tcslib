<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zFiberMeasure_specialYFalse_ne_zero_of_disjointSpecialYFalseMeasure_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity on the special-bit event

**Claim.** If the measure of the fiber under the hard distribution conditioned on disjointness and on Bob's special bit being false is nonzero, then the measure of the false special-bit event under the hard distribution conditioned on the fiber is nonzero.

**Proof.** Write $Z$ for the fiber and $Y_0$ for the event that Bob's special bit is false. The factorization identity for the disjoint-conditioned measure of the fiber says that its measure under the disjoint-and-false conditioning is $(3/2)$ times the disjoint-conditioned measure of $Y_0\cap Z$ (`disjointSpecialYFalseMeasure_measureReal_zVariable`). Thus the hypothesis forces the latter intersection measure to be nonzero. Since the disjoint-conditioned measure is absolutely continuous with respect to the original hard-distribution measure, the original measure of $Y_0\cap Z$ is also nonzero. The fiber itself has nonzero original measure (`volume_zFiber_ne_zero`). Applying the conditional-measure formula, the probability of $Y_0$ under the measure conditioned on $Z$ is the reciprocal of the fiber measure times the measure of $Z\cap Y_0$. Both factors are nonzero, so this conditional probability is nonzero.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_measureReal_zVariable`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_zFiber_ne_zero`.
