<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Sequence.lean :: BooleanAnalysis.GaussianSpace.Invariance.independent_polynomial_coupling -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coupling Preserving Polynomial Distributions

**Claim.** The two independent input families can be realized as disjoint parts of one mutually independent family so that evaluating the multilinear polynomial on either part has the same distribution as its evaluation on the corresponding original family.

**Proof.** First apply the independent coupling construction to the two families. This gives a probability space with mutually independent coordinates whose left and right marginals match those of $X$ and $Y$. Restricting a mutually independent family to either summand preserves independence, since the inclusions of the two index sets into their disjoint union are injective. Now apply the fact that coordinatewise identically distributed independent families give identically distributed multilinear polynomial evaluations (`identDistrib_evalMultilinearRV`): use it once for $X$ and the left coordinates, and once for $Y$ and the right coordinates. The coupling's marginal identities provide the coordinatewise distribution hypotheses in both applications.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.independent_input_coupling`, `BooleanAnalysis.GaussianSpace.Invariance.identDistrib_evalMultilinearRV`.
