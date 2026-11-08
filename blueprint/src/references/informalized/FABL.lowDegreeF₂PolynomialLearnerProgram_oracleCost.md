<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂PolynomialLearnerProgram_oracleCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle cost of the learner

**Claim.** Every outcome in the support of running the learner on $m$ random examples has random-example cost $m$ and membership-query cost zero.

**Proof.** The run-with-cost formula expresses the program’s output law as the image of a uniform sample-input batch under the map that forms the labeled samples, runs the learner, and pairs its output with cost $(m,0,\text{work})$ (`runWithCost_lowDegreeF₂PolynomialLearnerProgram`). Membership in the support of this image law therefore means that the outcome is the image of some sample-input batch. Unpacking that representation identifies its cost coordinates with $m$ and $0$, respectively.

**Key facts.** `FABL.runWithCost_lowDegreeF₂PolynomialLearnerProgram`.
