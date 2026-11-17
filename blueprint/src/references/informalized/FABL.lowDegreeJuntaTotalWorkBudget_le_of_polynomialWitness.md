<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaTotalWorkBudget_le_of_polynomialWitness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise Polynomial Work Budget

**Claim.** For every $n,b\in\mathbb{N}$, the total work budget at failure parameter $2^{-(b+1)}$ is at most $T_k C(n+1)^d(b+1)^e$.

**Proof.** The witness's work bound says that the uniform node-work bound at the per-call failure parameter is at most $C$ times the polynomial resource scale. The total work budget is $T_k$ times this uniform bound. Multiplying the witness inequality by $T_k$ preserves the order, and associativity of multiplication gives the stated pointwise estimate.
