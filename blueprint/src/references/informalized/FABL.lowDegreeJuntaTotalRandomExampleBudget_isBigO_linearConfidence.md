<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaTotalRandomExampleBudget_isBigO_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-confidence example budget

**Claim.** For each fixed $k$, the total random-example budget is $O((n+1)^{\lfloor3k/4\rfloor+3}(b+1))$ as $n$ and $b$ tend jointly to infinity.

**Proof.** Use the pointwise bound on the total budget: for every dimension and confidence-bit parameter, it is at most a constant depending only on $k$ times $(n+1)^{q+3}(b+1)$. Regard this as an inequality between the corresponding real-valued functions after casting the natural-number quantities to reals. The constant is independent of both inputs, so the pointwise estimate supplies the uniform bound required by the definition of big-O on the product filter.

**Key facts.** `FABL.lowDegreeJuntaTotalRandomExampleBudget_le_linearConfidence`.
