<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.exists_isKJunta_one_relativeHammingDist_le_of_fourierWeightAtMost_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A junta close to a Boolean function

**Claim.** If a Boolean function has Fourier weight at most level one at least $1-\delta$, for $0\le\delta\le1/1600$, then it is within relative Hamming distance $1601\delta$ of a one-coordinate junta.

**Proof.** Lift the given function to the balanced cube. The level-one weight of this lift equals the original weight at most level one (`fourierWeightAtLevel_one_balancedFKNLift`), so the lift satisfies the hypothesis of the FKN theorem. That theorem (`fkn`) supplies a signed dictator—possibly negated and on one of the lifted coordinates—within relative Hamming distance $1601\delta$ of the lift. Project this signed dictator back to the original cube. The projection is a one-coordinate junta (`balancedFKNProjection_isKJunta_one`), and the distance is preserved by the lift-projection correspondence (`relativeHammingDist_balancedFKNLift_signedDictator`). Thus the projected junta has the required distance from the original function.

**Key facts.** `FABL.fourierWeightAtLevel_one_balancedFKNLift`, `FABL.fkn`, `FABL.balancedFKNProjection_isKJunta_one`, `FABL.relativeHammingDist_balancedFKNLift_signedDictator`.
