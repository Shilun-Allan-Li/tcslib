<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaTotalRandomExampleBudget_le_of_polynomialWitness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pointwise Polynomial Example Budget

**Claim.** For every $n,b\in\mathbb{N}$, the total random-example budget at failure parameter $2^{-(b+1)}$ is at most $T_k C(n+1)^d(b+1)^e$.

**Proof.** By the witness assumption, the uniform node random-example bound at the per-call failure parameter is at most $C$ times the polynomial resource scale. The total budget is $T_k$ times that uniform node bound. Multiplying the witness inequality by the nonnegative call count $T_k$ preserves its direction; reassociating the natural-number products gives exactly the asserted upper bound.
