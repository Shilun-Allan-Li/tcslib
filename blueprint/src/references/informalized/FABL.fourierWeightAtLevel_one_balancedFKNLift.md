<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.fourierWeightAtLevel_one_balancedFKNLift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-one weight of the balanced lift

**Claim.** The level-one Fourier weight of the balanced lift of $f$ equals the sum of squared Fourier coefficients of $f$ over the empty set and all singleton sets, namely its weight at most level one.

**Proof.** The level-one weight is the sum of squared coefficients over singleton coordinates (`fourierWeightAtLevel_one_eq_sum_singleton`). Separate the new first coordinate from the lifted coordinates. The coefficient at that first coordinate equals the empty-set coefficient of $f$ (`fourierCoeff_balancedFKNLift_zero`), and each other singleton coefficient equals the corresponding singleton coefficient of $f$ (`fourierCoeff_balancedFKNLift_succ`). Consequently the sum is $\widehat f(\varnothing)^2+\sum_i\widehat f(\{i\})^2$. This is precisely the weight at most level one, by `fourierWeightAtMost_one_eq_empty_add_sum_singleton`.

**Key facts.** `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.fourierCoeff_balancedFKNLift_zero`, `FABL.fourierCoeff_balancedFKNLift_succ`, `FABL.fourierWeightAtMost_one_eq_empty_add_sum_singleton`.
