<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.oddBLRAndAndRejectionGap_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection Gap Lower Bound

**Claim.** For any non-dictator Boolean function, the minimum rejection probability among non-dictator functions is at most that function's rejection probability.

**Proof.** The given function $f$ belongs to the finite collection of all non-dictator Boolean functions, since it is not a dictator. Its rejection probability is therefore among the values whose minimum defines the rejection gap. The minimum of a nonempty finite set is at most each member, so the gap is at most the rejection probability of $f$.
