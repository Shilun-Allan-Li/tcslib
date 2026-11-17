<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBiasMarginals.lean :: FABL.vectorWalshCharacter_coordinateProjection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh Characters under Coordinate Projection

**Claim.** Projecting a point of $\mathbb{F}_2^n$ onto coordinates in $J$ and evaluating the Walsh character indexed by $\gamma$ gives the same value as evaluating at the original point the character indexed by the lift of $\gamma$ that is zero outside $J$.

**Proof.** Write both Walsh character values as the binary sign of their respective dot products (`FABL.vectorWalshCharacter_apply`). The dot product of the lifted frequency with the original point equals the dot product of $\gamma$ with the projection of the point (`FABL.f₂DotProduct_coordinateFrequencyLift`). The binary signs, and hence the characters, are therefore equal.

**Key facts.** `FABL.vectorWalshCharacter_apply`, `FABL.f₂DotProduct_coordinateFrequencyLift`.
