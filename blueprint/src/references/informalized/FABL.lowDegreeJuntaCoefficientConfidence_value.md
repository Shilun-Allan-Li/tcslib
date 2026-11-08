<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaCoefficientConfidence_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient Confidence Value

**Claim.** For the stated parameters, the coefficient confidence parameter has value $\delta/(4|\mathcal F|)$, where $\mathcal F$ is the family of subsets of the coordinates outside $P$ of size at most $\lfloor3k/4\rfloor$.

**Proof.** The confidence parameter is defined by dividing the quarter-failure parameter by the cardinality of $\mathcal F$. The quarter-failure parameter is itself obtained by dividing $\delta$ by $4$. Unfolding these definitions gives the stated value.
