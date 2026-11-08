<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.insertJuntaFixedAssignment_apply_new -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at the inserted coordinate

**Claim.** After inserting a new coordinate $i$ with value $v$ into the fixed assignment, the extended assignment has value $v$ at $i$.

**Proof.** Evaluate the extended assignment at the coordinate $i$. The defining case for the inserted coordinate applies, because the queried coordinate is exactly $i$. The assigned value is therefore $v$.
