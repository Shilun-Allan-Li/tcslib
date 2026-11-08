<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaRestrictionSampleProgram_cost_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost of the Junta Restriction Program

**Claim.** Every outcome in the support of the program's run has cost equal to the prescribed sample count, zero queries, and sample count plus prescribed work.

**Proof.** Rewrite the run law using `runWithCost_juntaRestrictionSampleProgram`: it is the uniform sample-input law mapped to an output whose cost component is fixed at the stated triple. Membership in the support of this mapped law therefore gives a sample-input preimage producing the outcome. Its cost component is that fixed triple, as claimed.

**Key facts.** `FABL.runWithCost_juntaRestrictionSampleProgram`.
