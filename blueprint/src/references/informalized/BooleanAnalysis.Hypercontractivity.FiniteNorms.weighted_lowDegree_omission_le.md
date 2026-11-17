<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Norms.lean :: BooleanAnalysis.Hypercontractivity.FiniteNorms.weighted_lowDegree_omission_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted low degree omission

**Claim.** For nonnegative coefficients on subsets of a finite set, the weighted contribution from subsets of size at most $k$ that are not contained in $J$, multiplied by $\rho^k$, is at most the sum over coordinates outside $J$ of their incident contributions weighted by $\rho^{|S|}$.

**Proof.** Distribute $\rho^k$ across the sum and compare term by term for each subset $S$. If $S$ has size at most $k$ and is not contained in $J$, choose a coordinate $i\in S\setminus J$. Because $0\le\rho\le1$, we have $\rho^k\le\rho^{|S|}$; multiplying by $E(S)\ge0$ preserves this inequality. The term $\rho^{|S|}E(S)$ occurs in the inner sum for this chosen coordinate, and all other terms there are nonnegative. If $S$ does not meet the size-and-omission condition, its contribution on the left is zero, while the corresponding inner sum is nonnegative. Summing these comparisons over $S$ and interchanging the two finite sums gives the stated inequality.
