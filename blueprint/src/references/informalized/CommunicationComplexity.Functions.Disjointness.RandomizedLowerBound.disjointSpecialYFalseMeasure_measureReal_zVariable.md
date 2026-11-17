<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_measureReal_zVariable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mass of a Conditioned Fiber

**Claim.** For any achievable value $z$ of $Z$, its mass under the law conditioned on disjointness and Bob’s special bit being false is $3/2$ times its mass under the disjointness-conditioned law intersected with the event that Bob’s special bit is false.

**Proof.** By the conditional-measure formula, the mass of the fiber at $z$ under the further-conditioned law equals its mass intersected with the false-special-bit event under the disjointness-conditioned law, divided by the mass of that event. The latter mass is $2/3$ (\texttt{disjointCondMeasure_measureReal_specialY_false}). Taking its reciprocal gives the factor $3/2$, and rearranging yields the stated identity.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialY_false`.
