<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Adaptive.lean :: FABL.outerEventProbability_goldreichLevinStageStepProgram_failure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stage failure probability identity

**Claim.** If the query state has no inaccurate estimate record, the probability that a stage step produces a state with an inaccurate record equals the probability that its estimation program produces a list containing an inaccurate record.

**Proof.** The stage-step program runs the stage estimation program and then maps each outcome to the query state obtained by appending its records and applying the query-state update; it also adds the controller's fixed work cost. Accordingly, its outcome distribution is the pushforward of the estimation program's distribution under this map (runWithCost_goldreichLevinStageStepProgram). For each estimation outcome list, the updated state has a failure exactly when that list contains an inaccurate record, because the incoming state has none (goldreichLevinQueryStep_hasFailure_iff_of_not_hasFailure). Thus the two event probabilities agree under the pushforward distribution.

**Key facts.** `FABL.runWithCost_goldreichLevinStageStepProgram`, `FABL.goldreichLevinQueryStep_hasFailure_iff_of_not_hasFailure`.
