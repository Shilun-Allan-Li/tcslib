<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaNodeAnalysisWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Node Analysis Work Estimate

**Claim.** For natural numbers $n,k$, a coordinate set $P$, a positive learning parameter $\delta$, and a batch of restricted examples of the prescribed length, the node analysis work on the batch is at most the node analysis work bound for $P,k,\delta$.

**Proof.** Expand the definitions of the node analysis work and its bound. Their Fourier-family, coefficient-sampling, and final counting contributions agree. The only potentially larger contribution in the work expression is the work of the low-degree polynomial learner. The learner’s work estimate bounds it by the sum of its sample-processing cost, elimination cost, and pivot-processing cost, which is precisely the polynomial work bound appearing in the node analysis bound. Combining this estimate with the identical remaining contributions proves the inequality.

**Key facts.** `FABL.lowDegreeF₂PolynomialLearnerWork_le`.
