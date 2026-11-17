<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DegreeOneRigidity.lean :: FABL.fourierCoeff_eq_zero_of_fourierWeightAtMost_one_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Weight Concentration Below Level Two

**Claim.** If a Boolean-valued function has total Fourier weight on sets of size at most one equal to one, then every coefficient indexed by a set of size greater than one is zero.

**Proof.** Parseval says that the sum of squared Fourier coefficients over all sets is $1$ (`sum_sq_fourierCoeff_eq_one`). By hypothesis, the part indexed by sets of size at most one already sums to $1$, so the complementary sum, over sets not of size at most one, is zero. All terms in that sum are nonnegative squares. Consequently each such square vanishes; in particular, the coefficient at any set of size greater than one is zero.

**Key facts.** `FABL.sum_sq_fourierCoeff_eq_one`.
