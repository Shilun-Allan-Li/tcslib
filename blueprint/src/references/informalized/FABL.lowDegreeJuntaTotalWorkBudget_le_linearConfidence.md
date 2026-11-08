<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaTotalWorkBudget_le_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise Linear-Confidence Work Budget

**Claim.** For all $n,k,b\in\mathbb{N}$, the total work budget at dyadic failure parameter $2^{-(b+1)}$ is at most $T_k W_k(n+1)^{\lfloor 3k/4\rfloor+4}(b+1)$.

**Proof.** The uniform node-work bound at the dyadic node failure parameter is at most $W_k(n+1)^{\lfloor 3k/4\rfloor+4}(b+1)$ (`lowDegreeJuntaNodeUniformWorkBound_le_linearConfidence`). The total work budget multiplies the uniform node-work bound by the tree call count $T_k$. Multiplication preserves the inequality, and the dyadic node failure parameter is the one used by the total budget. Reassociating the factors gives the claimed estimate.

**Key facts.** `FABL.lowDegreeJuntaNodeUniformWorkBound_le_linearConfidence`.
