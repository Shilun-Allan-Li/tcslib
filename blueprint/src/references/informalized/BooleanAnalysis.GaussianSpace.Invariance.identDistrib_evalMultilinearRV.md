<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Sequence.lean :: BooleanAnalysis.GaussianSpace.Invariance.identDistrib_evalMultilinearRV -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identical laws of multilinear evaluations

**Claim.** Independent coordinate families with matching coordinate laws give multilinear evaluations with the same distribution.

**Proof.** The theorem on joint laws from independent coordinate laws (\texttt{identDistrib\_of\_independent\_coordinates}) first shows that the random vectors $(X_i)_i$ and $(Y_i)_i$ have the same distribution. Apply the same measurable function to each vector, namely the finite polynomial map $z\mapsto\sum_S F(S)\prod_{i\in S}z_i$. Measurable maps preserve equality of distributions, and the resulting random variables are precisely the two multilinear evaluations. The polynomial map is measurable because it is a finite sum of finite products of coordinate maps.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.identDistrib_of_independent_coordinates`.
