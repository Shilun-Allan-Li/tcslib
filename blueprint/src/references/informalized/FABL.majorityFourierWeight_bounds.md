<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierWeightLimits.lean :: FABL.majorityFourierWeight_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on Majority Fourier Weight

**Claim.** For odd $n$ and odd $k$ with $2k<n$, the level-$k$ Fourier weight of majority lies between the limiting weight and $(1+2k/n)$ times that weight.

**Proof.** The lower bound follows from the theorem that the limiting majority Fourier weight is at most the level-$k$ weight whenever $k\le n$ (`FABL.limitingMajorityFourierWeight_le_fourierWeightAtLevel_majority`); the hypothesis $2k<n$ ensures this condition. The upper bound is the corresponding estimate for levels with $2k<n$ (`FABL.fourierWeightAtLevel_majority_le_limitingMajorityFourierWeight`). Together they give the asserted pair of inequalities.

**Key facts.** `FABL.limitingMajorityFourierWeight_le_fourierWeightAtLevel_majority`, `FABL.fourierWeightAtLevel_majority_le_limitingMajorityFourierWeight`.
