<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.almostKWiseConstructionWork_le_polynomialBudget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial construction-work bound

**Claim.** For every almost-wise input, the total construction work is at most $2^{38}(s+1)^{16}$, where $s$ is the input scale.

**Proof.** Set $R=s+1$, so $R\ge 1$ and hence each positive integer power of $R$ is at least one. The Vandermonde work is at most $2^{17}R^8$, and therefore at most $2^{17}R^{16}$ ($\texttt{almostKWiseVandermondeWork\_le$). The associated small-bias scale is at most $4R^2$ ($\texttt{AlmostKWiseInput.smallBiasScale\_le\_four\_scale\_sq$), so its scale plus one is at most $5R^2$. Applying the deterministic small-bias budget bound and raising this estimate to the eighth power bounds that work by $2^{17}5^8R^{16}\le 2^{36}R^{16}$ ($\texttt{deterministicSmallBiasWork\_le\_polynomialBudget$). For the output contribution, the number of outputs is at most $4$ times the square of the small-bias scale, and the output multiset has cardinality $2^B$ ($\texttt{almostKWiseOutputMultiset\_card\_le\_smallBiasScale}$ and $\texttt{almostKWiseOutputMultiset\_card\_eq\_two\_pow\_randomBits}$). Thus $2^B\le 64R^4$. The matrix-vector multiplication work is at most $9R^3$, so its work per output, including the extra unit charge, is at most $10R^3$ ($\texttt{almostKWiseMatrixVecMulWork\_le$). Consequently the output contribution is at most $640R^7\le640R^{16}$. The total work equals the sum of the Vandermonde, small-bias, and output contributions ($\texttt{almostKWiseConstructionWork\_eq$). Adding the bounds gives $(2^{17}+2^{36}+640)R^{16}\le2^{38}R^{16}$, as required.

**Key facts.** `FABL.almostKWiseVandermondeWork_le`, `FABL.AlmostKWiseInput.smallBiasScale_le_four_scale_sq`, `FABL.deterministicSmallBiasWork_le_polynomialBudget`, `FABL.almostKWiseOutputMultiset_card_eq_two_pow_randomBits`, `FABL.almostKWiseOutputMultiset_card_le_smallBiasScale`, `FABL.almostKWiseMatrixVecMulWork_le`, `FABL.almostKWiseConstructionWork_eq`.
