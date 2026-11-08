<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaTotalRandomExampleBudget_le_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Confidence Example Budget

**Claim.** For all $n,k,b\in\mathbb{N}$, the total random-example budget at dyadic failure parameter $2^{-(b+1)}$ is at most $T_k A_k(n+1)^{\lfloor 3k/4\rfloor+3}(b+1)$.

**Proof.** The uniform node random-example estimate at the dyadic node failure parameter bounds the node count by $A_k(n+1)^{\lfloor 3k/4\rfloor+3}(b+1)$ (`lowDegreeJuntaNodeRandomExampleBound_le_linearConfidence`). The total budget is the node bound multiplied by the tree call count $T_k$. Multiplication by this nonnegative natural number preserves the inequality, and the dyadic node failure parameter agrees with the per-call parameter used in the total budget. This yields the stated bound.

**Key facts.** `FABL.lowDegreeJuntaNodeRandomExampleBound_le_linearConfidence`.
