<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.mean_improvedFKNBalancedLift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the Improved Balanced Lift

**Claim.** The improved balanced lift, formed by permuting the input coordinates of a balanced lift, has mean zero.

**Proof.** The mean equals the Fourier coefficient at the empty set (FABL.mean_eq_fourierCoeff_empty). Under composition with a coordinate permutation, a Fourier coefficient at a set is carried to the coefficient indexed by the inverse-permuted set (FABL.fourierCoeff_comp_permuteInput). The empty set remains empty, so the improved lift’s mean equals the balanced lift’s mean. That mean is zero (FABL.mean_balancedFKNLift).

**Key facts.** `FABL.mean_eq_fourierCoeff_empty`, `FABL.improvedFKNBalancedLift_toReal`, `FABL.fourierCoeff_comp_permuteInput`, `FABL.mean_balancedFKNLift`.
