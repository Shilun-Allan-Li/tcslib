<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaTotalWorkBudget_isBigO_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Confidence Work Budget

**Claim.** For each fixed $k$, the total work budget at dyadic failure parameter $2^{-(b+1)}$ is $O((n+1)^{\lfloor 3k/4\rfloor+4}(b+1))$ jointly as $n,b\to\infty$.

**Proof.** The pointwise uniform-node work estimate bounds the node work by $W_k(n+1)^{\lfloor 3k/4\rfloor+4}(b+1)$ (`lowDegreeJuntaTotalWorkBudget_le_linearConfidence`), after accounting for the tree call count. For each $(n,b)$ this natural-number bound is also a real-number bound. Its coefficient, which depends only on the fixed $k$, is constant over the product domain. Hence the functions satisfy the defining eventual constant-multiple bound for Big-O.

**Key facts.** `FABL.lowDegreeJuntaTotalWorkBudget_le_linearConfidence`.
