<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearningAlgorithm.lean :: FABL.lowDegreeJuntaLearningAlgorithm_learns -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Learning of K-Juntas

**Claim.** For every $n$, $k$, and learning accuracy, the low-degree junta learning algorithm learns the class of Boolean $k$-juntas with success probability at least $9/10$.

**Proof.** Fix a target in the class of Boolean $k$-juntas. By the definition of that class, the target is a $k$-junta. The success-probability bound for the low-degree junta learning algorithm (`FABL.lowDegreeJuntaLearningAlgorithm_successProbability_ge`) therefore applies and gives success probability at least $9/10$ at the specified accuracy. Since the target was arbitrary, this is exactly the required learning guarantee.

**Key facts.** `FABL.lowDegreeJuntaLearningAlgorithm_successProbability_ge`.
