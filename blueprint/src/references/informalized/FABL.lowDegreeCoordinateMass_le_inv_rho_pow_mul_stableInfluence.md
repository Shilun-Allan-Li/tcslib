<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.lowDegreeCoordinateMass_le_inv_rho_pow_mul_stableInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Mass and Stable Influence

**Claim.** For a sign-valued Boolean function $f$, coordinate $i$, natural number $k$, and $0<\rho\le1$, the low-degree coordinate mass through degree $k$ is at most $\rho^{-k}$ times the stable influence of the real-valued version of $f$ at $i$ with parameter $\rho$.

**Proof.** Expand both sums over subsets $S$ of coordinates, writing each restricted sum as a sum with an indicator. For a term with $i\in S$ and $|S|\le k$, the fact that $i\in S$ gives $|S|>0$, so $|S|-1\le k$. Because $0<\rho\le1$, its powers decrease as the exponent increases, and therefore $\rho^k\le\rho^{|S|-1}$. Multiplying by the nonnegative factor $\rho^{-k}$ and using $\rho^{-k}\rho^k=1$ gives $1\le\rho^{-k}\rho^{|S|-1}$. Multiplying this by the squared Fourier coefficient, which is nonnegative, bounds the low-degree summand by the corresponding stable-influence summand scaled by $\rho^{-k}$. Terms not satisfying both restrictions contribute zero on the left and a nonnegative amount on the right. Summing these termwise inequalities and factoring out the constant $\rho^{-k}$ proves the result.
