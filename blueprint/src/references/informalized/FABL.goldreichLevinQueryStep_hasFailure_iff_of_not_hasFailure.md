<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Adaptive.lean :: FABL.goldreichLevinQueryStep_hasFailure_iff_of_not_hasFailure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure in one query step

**Claim.** If the current query state has no inaccurate estimate in its trace, then after a query step the resulting trace has an inaccurate estimate exactly when the appended list contains one.

**Proof.** The query step appends the new records to the old trace; it does not otherwise alter the trace. Thus any inaccurate record in the resulting trace belongs either to the old trace or to the appended list. The first possibility is excluded by the hypothesis that the current state has no failure. Conversely, any inaccurate record in the appended list remains in the concatenated trace, giving failure after the step.
