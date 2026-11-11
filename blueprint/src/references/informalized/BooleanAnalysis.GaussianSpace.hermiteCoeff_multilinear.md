<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite.lean :: BooleanAnalysis.GaussianSpace.hermiteCoeff_multilinear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite Coefficients of Multilinear Polynomials

**Claim.** The Hermite coefficient of the multilinear polynomial with coefficients $F(S)$ at $\alpha$ is $F(\{i:\alpha_i=1\})$ when every coordinate of $\alpha$ is at most one, and is zero otherwise.

**Proof.** Write the polynomial as the sum over subsets $S$ of $F(S)\prod_{i\in S}x_i$. The indicator identity for Hermite functions (`hermiteFunction_indicator`) identifies each monomial $\prod_{i\in S}x_i$ with the Hermite function whose multi-index is $1$ on $S$ and $0$ off $S$. By the coefficient formula for a finite sum of Hermite functions (`hermiteCoeff_finset_sum_hermiteFunction`), the coefficient at $\alpha$ receives a contribution precisely from terms whose indicator multi-index equals $\alpha$. Such equality holds exactly when every $\alpha_i\le1$ and $S=\{i:\alpha_i=1\}$ (`indicatorMultiIndex_eq_iff`). Thus there is one matching term with coefficient $F(S)$ in the first case, and no matching term in the second.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermiteFunction_indicator`, `BooleanAnalysis.GaussianSpace.hermiteCoeff_finset_sum_hermiteFunction`, `BooleanAnalysis.GaussianSpace.indicatorMultiIndex_eq_iff`.
