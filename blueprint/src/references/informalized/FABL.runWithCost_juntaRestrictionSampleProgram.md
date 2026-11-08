<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.runWithCost_juntaRestrictionSampleProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction sample program law

**Claim.** The run distribution of the junta restriction sampling program is the uniform law on batches of cube inputs, mapped to the selected matching examples and the fixed cost.

**Proof.** Unfold the program: it first draws a uniformly random batch of the prescribed size, then charges the stated local work and returns the result of taking the first $M$ samples matching the assignment (or failure if too few match). Under the definition of the run law, the batch draw contributes $R$ random examples and $R$ units of work, where $R$ is the prescribed sample count. The subsequent pure return does not alter the output or add cost, and the tick adds exactly the stipulated work. Thus the outcome is the displayed function of the uniform input batch, with total cost $(R,0,R+W)$.
