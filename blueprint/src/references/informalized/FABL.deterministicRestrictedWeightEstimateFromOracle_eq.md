<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.deterministicRestrictedWeightEstimateFromOracle_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle estimate identity

**Claim.** The expected squared empirical Fourier coefficient obtained from the prescribed membership-query answers equals the restricted Fourier weight on $S$ over the fixed-coordinate sample.

**Proof.** Fix an outer sample index and an inner sample index. The query index corresponding to this pair is sent by the query-pair equivalence to exactly that same pair. Thus, when the answers are supplied by querying the target at the prescribed query point, the answer for this pair is the target value at the combined free and fixed assignments. Converting that sign to its real value gives exactly the summand used in the empirical Fourier coefficient. Consequently, for each fixed outer sample, the inner average in the oracle estimate is the restricted Fourier coefficient estimate at that outer sample's fixed assignment. Squaring these equal quantities and averaging over the outer indices yields the restricted Fourier weight estimate.
