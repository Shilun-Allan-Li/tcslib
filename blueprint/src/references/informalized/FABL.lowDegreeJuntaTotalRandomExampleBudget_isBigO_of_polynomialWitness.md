<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaTotalRandomExampleBudget_isBigO_of_polynomialWitness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Example Budget

**Claim.** Under the stated polynomial bound on the uniform node random-example count, the total random-example budget is $O((n+1)^d(b+1)^e)$ as $n$ and $b$ tend jointly to infinity.

**Proof.** For each pair $(n,b)$, the pointwise budget estimate from the polynomial witness ( `lowDegreeJuntaTotalRandomExampleBudget_le_of_polynomialWitness`) bounds the total budget by $T_k C$ times the stated polynomial resource scale. Regard this natural-number inequality as an inequality of real numbers. The coefficient $T_k C$ is fixed because $k$ and the witness are fixed, so this is a uniform bound by a constant multiple of the comparison function. The definition of Big-O on the product filter then gives the claim.

**Key facts.** `FABL.lowDegreeJuntaTotalRandomExampleBudget_le_of_polynomialWitness`.
