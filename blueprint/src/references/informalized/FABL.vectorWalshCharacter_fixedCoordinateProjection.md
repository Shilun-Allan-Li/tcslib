<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.vectorWalshCharacter_fixedCoordinateProjection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh Characters under Fixed-Coordinate Projection

**Claim.** Projecting a point onto coordinates outside $J$ and evaluating the Walsh character indexed by $\gamma$ gives the same value as evaluating at the original point the character indexed by the lift of $\gamma$ that is zero on $J$.

**Proof.** By the character evaluation formula (`FABL.vectorWalshCharacter_apply`), both values are binary signs of dot products. The dot product of the lifted frequency with the original point equals the dot product of $\gamma$ with the projection onto coordinates outside $J$ (`FABL.f₂DotProduct_fixedCoordinateFrequencyLift`). Their binary signs agree, yielding the result.

**Key facts.** `FABL.vectorWalshCharacter_apply`, `FABL.f₂DotProduct_fixedCoordinateFrequencyLift`.
