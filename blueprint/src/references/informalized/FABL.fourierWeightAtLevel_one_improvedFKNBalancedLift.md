<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ImprovedFKN.lean :: FABL.fourierWeightAtLevel_one_improvedFKNBalancedLift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-One Weight of the Balanced Lift

**Claim.** For a Boolean function $f$ and coordinate $i$, the level-one Fourier weight of the lift formed after swapping coordinate $0$ with coordinate $i+1$ equals the Fourier weight of $f$ on levels zero and one combined.

**Proof.** Write the swapped lift as the balanced lift composed with the coordinate permutation. By the level-one singleton formula (`fourierWeightAtLevel_one_eq_sum_singleton`), its level-one weight is a sum of squared singleton coefficients. The coefficient of a function after permuting its inputs is the original coefficient indexed by the correspondingly permuted singleton (`fourierCoeff_comp_permuteInput`). As the swap permutes the coordinates bijectively, reindexing the sum leaves it unchanged. The result is therefore the level-one weight of the balanced lift, which equals the weight of $f$ on levels at most one (`fourierWeightAtLevel_one_balancedFKNLift`).

**Key facts.** `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.improvedFKNBalancedLift_toReal`, `FABL.fourierCoeff_comp_permuteInput`, `FABL.fourierWeightAtLevel_one_balancedFKNLift`.
