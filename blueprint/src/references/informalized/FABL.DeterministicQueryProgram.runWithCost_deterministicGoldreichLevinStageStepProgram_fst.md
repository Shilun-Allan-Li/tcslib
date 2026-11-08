<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageStepProgram_fst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin Stage-Step Output

**Claim.** Running the Goldreich–Levin stage-step program returns the state obtained by appending the stage’s estimate records and applying the prescribed update.

**Proof.** The stage-step program charges controller work and then maps the stage program’s output records through the prescribed state update. The stage-program run theorem (`runWithCost_deterministicGoldreichLevinStageProgram`) identifies those records as the estimates obtained from the target’s answers to the batch of stage queries. The run rule for binding a continuation (`runWithCost_bind`) identifies the continuation’s input as that output. Thus the first component of the run is precisely the updated state formed from the original state and the stage records.

**Key facts.** `FABL.DeterministicQueryProgram.runWithCost_bind`, `FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageProgram`.
