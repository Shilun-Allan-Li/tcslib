<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageStepProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin Stage-Step Cost

**Claim.** Running the Goldreich–Levin stage-step program returns the state formed by appending the stage’s estimate records and applying the prescribed update, with cost equal to the controller charge plus the stage cost.

**Proof.** The stage-step program first charges the controller’s work, then runs the stage program and maps its list of estimate records to the updated query state. The stage program’s run returns the records produced from the target’s answers to the prescribed batch of queries, together with the stage cost; this is the content of the stage-program run theorem (`runWithCost_deterministicGoldreichLevinStageProgram`). The general run rule for binding a continuation (`runWithCost_bind`) says that the continuation receives the first program’s output and that the two costs are added. Here the continuation applies the state update to those records. Including the initial controller charge gives exactly the stated updated state and the sum of controller and stage costs.

**Key facts.** `FABL.DeterministicQueryProgram.runWithCost_bind`, `FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinStageProgram`.
