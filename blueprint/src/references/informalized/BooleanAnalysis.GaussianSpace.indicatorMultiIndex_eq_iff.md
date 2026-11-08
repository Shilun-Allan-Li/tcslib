<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basic.lean :: BooleanAnalysis.GaussianSpace.indicatorMultiIndex_eq_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator Multi-Index Characterization

**Claim.** The indicator function of $S$ equals $\alpha$ exactly when every value of $\alpha$ is at most $1$ and $S$ consists precisely of the indices where $\alpha$ is $1$.

**Proof.** Suppose first that the indicator of $S$ equals $\alpha$. Each value of that indicator is either $0$ or $1$, so every value of $\alpha$ is at most $1$. An index lies in $S$ exactly when the indicator takes value $1$ there; hence $S$ is the set of indices where $\alpha$ equals $1$. Conversely, suppose every value of $\alpha$ is at most $1$ and $S$ is that level set. At an index in $S$, the value of $\alpha$ is $1$, agreeing with the indicator. At an index outside $S$, the value is not $1$ and is at most $1$, so as a natural number it must be $0$. Thus the two functions agree at every index.
