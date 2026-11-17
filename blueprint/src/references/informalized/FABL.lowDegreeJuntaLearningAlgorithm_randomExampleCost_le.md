<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaLearningAlgorithm_randomExampleCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Random-example cost bound

**Claim.** Let $n,k\in\mathbb{N}$ and let $\varepsilon$ be a rational accuracy with $0\leq\varepsilon\leq\tfrac12$. With $T_0=1$, $T_{j+1}=1+2T_j$, $c=\lfloor3k/4\rfloor$, $L=\lceil\log_2 T_k\rceil+2(c+1)+5$, and $C=(c+1)36\cdot4^kL$, the low-degree junta learning algorithm uses at most $4T_kC(n+1)^{c+3}$ random examples.

**Proof.** Unfolding the algorithm’s advertised random-example cost identifies it with the total random-example budget obtained by charging each recursive node call its uniform bound, with the per-call failure parameter set to the total failure divided by the number of calls. By the identity between the algorithm’s fixed learning failure and the dyadic failure parameter with three confidence bits (`FABL.lowDegreeJuntaLearningFailure_eq_dyadicFailure`), this total budget is the budget at that dyadic parameter. The linear-confidence budget estimate (`FABL.lowDegreeJuntaTotalRandomExampleBudget_le_linearConfidence`), applied with three confidence bits, bounds it by the node-call count times the node’s linear random-example coefficient times $(n+1)$ raised to the node resource exponent, times $3+1$. Since $3+1=4$, rearranging the factors gives the asserted bound, with the named quantities expanded as $T_k$, $C$, and $c+3$.

**Key facts.** `FABL.lowDegreeJuntaLearningFailure_eq_dyadicFailure`, `FABL.lowDegreeJuntaTotalRandomExampleBudget_le_linearConfidence`.
