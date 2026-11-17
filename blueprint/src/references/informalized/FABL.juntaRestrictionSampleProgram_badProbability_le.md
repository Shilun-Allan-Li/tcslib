<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaRestrictionSampleProgram_badProbability_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bad-Outcome Probability Bound

**Claim.** For the junta restriction sampling program, the probability of a bad outcome is at most the sum of the failure parameter and the ideal-batch bad-event bound η.

**Proof.** Split a bad outcome into two possibilities: the program returns no batch, or it returns a batch that is bad. The first event has probability at most the failure parameter by `juntaRestrictionSampleProgram_failureProbability_le`. For the second event, the run law is expressed as a uniform sample-input law mapped to the program output using `runWithCost_juntaRestrictionSampleProgram`; `rawProjectedJuntaRestrictionBatch_successBadProbability_le` then bounds its probability by η, from the assumed ideal-batch bound. The two events cover all bad outcomes. Their probabilities are finite, since `pmfToOuterMeasure_ne_top` says that a PMF assigns finite outer measure to every event. Subadditivity of measure bounds the probability of their union by the sum of their probabilities, yielding the result.

**Key facts.** `FABL.juntaRestrictionSampleProgram_failureProbability_le`, `FABL.rawProjectedJuntaRestrictionBatch_successBadProbability_le`, `FABL.runWithCost_juntaRestrictionSampleProgram`, `FABL.pmfToOuterMeasure_ne_top`.

**Caveat.** The supplied informal statement describes a different learning-theory task. This account follows the formal statement and proof source, which establish the bad-outcome probability bound.
