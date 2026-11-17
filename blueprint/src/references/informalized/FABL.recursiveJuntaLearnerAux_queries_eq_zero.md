<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.recursiveJuntaLearnerAux_queries_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Membership Query Cost

**Claim.** For every fuel, fixed-coordinate set, assignment, and supported outcome of the recursive learner, the charged number of membership queries is zero.

**Proof.** Apply the recursive cost-projection bound to the projection that reads the query component of a cost. This projection sends zero cost to zero and turns a sum of costs into the sum of their query components. At every node-finder call, the finder’s pathwise cost guarantee says that the query component is zero. Thus the projection bound gives an upper bound of zero for the query component of every supported recursive outcome. Since query cost is a natural number, it must equal zero (`Nat.eq_zero_of_le_zero`).

**Key facts.** `FABL.recursiveJuntaLearnerAux_costProjection_le`.
