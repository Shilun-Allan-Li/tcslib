<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaLearningAlgorithm_workCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Bound for the Junta Learner

**Claim.** For natural numbers $n,k$ and any learning accuracy, the work cost of the low-degree junta learning algorithm is at most $4$ times the number of calls in a depth-$k$ junta tree, times the node work linear coefficient at $k$, times $(n+1)^{\lfloor 3k/4\rfloor+4}$.

**Proof.** By the definition of the algorithm’s work cost, it is the number of calls in a depth-$k$ junta tree multiplied by the uniform node work bound at the per-call failure parameter. Thus it is exactly the total work budget at the low-degree junta learning failure parameter. The failure parameter equals the dyadic failure parameter with three bits (both are $1/16$; `lowDegreeJuntaLearningFailure_eq_dyadicFailure`). Apply the total work budget bound at confidence level three: it is at most the number of tree calls times the node work linear coefficient, times $(n+1)$ to the node resource exponent, times $3+1$. Since the exponent is $\lfloor 3k/4\rfloor+4$, rearranging the factors gives the claimed bound.

**Key facts.** `FABL.lowDegreeJuntaLearningFailure_eq_dyadicFailure`, `FABL.lowDegreeJuntaTotalWorkBudget_le_linearConfidence`.
