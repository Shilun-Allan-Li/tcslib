<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Adaptive.lean :: FABL.runWithCost_goldreichLevinStageStepProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin Stage Cost Law

**Claim.** The stage-step program’s law is the stage-estimate law mapped by the update that appends the estimate records to the state, refines its active family, and adds the controller’s work cost.

**Proof.** The stage-step program is a controller-work tick followed by the stage-estimate program mapped through the state update. The run law for mapping a program says its output is transformed while its cost is retained (`runWithCost_map`). Running the tick adds $(0,0,16(n+1)^2(C+1)^2)$ to that cost. Therefore the resulting law is the image of the stage-estimate law under the stated state update and cost addition.

**Key facts.** `FABL.LearningProgram.runWithCost_map`.
