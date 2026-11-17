<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaTotalWorkBudget_isBigO_of_polynomialWitness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Work Budget

**Claim.** Under the stated polynomial bounds on uniform node examples and work, the total work budget is $O((n+1)^d(b+1)^e)$ jointly as $n$ and $b$ tend to infinity.

**Proof.** For every $(n,b)$, the pointwise polynomial-witness estimate bounds the total work budget by $T_k C$ times the polynomial resource scale (`lowDegreeJuntaTotalWorkBudget_le_of_polynomialWitness`). Viewing this natural-number inequality in the reals gives a bound by a fixed constant multiple of the comparison function. Since $k$ and the witness are fixed, this constant is independent of $n$ and $b$, which proves the Big-O assertion on the product filter.

**Key facts.** `FABL.lowDegreeJuntaTotalWorkBudget_le_of_polynomialWitness`.
