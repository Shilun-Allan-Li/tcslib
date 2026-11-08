<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Coordinates.lean :: BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_degree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree reduction under coordinate differentiation

**Claim.** If $F$ has degree at most $k+1$, then the coefficient family formed from the Fourier coefficients of its Boolean-cube derivative in coordinate $i$ has degree at most $k$.

**Proof.** Fix a set $S$ with $|S|>k$. By the coordinate derivative coefficient formula, its new coefficient is zero if $i\in S$. If $i\notin S$, that coefficient is $F(S\cup\{i\})$. Since adjoining a new element increases cardinality by one, $|S\cup\{i\}|=|S|+1>k+1$. The degree bound on $F$ therefore makes this coefficient zero as well. Thus every coefficient indexed by a set of size greater than $k$ vanishes.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_coeff`.
