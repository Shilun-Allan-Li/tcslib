<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/ThirdMoments.lean :: BooleanAnalysis.GaussianSpace.Invariance.polynomial_three_norm_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-Norm Bound

**Claim.** The square of the real-valued $L^3$ norm of the random-input evaluation of $F$ is at most $(1/\rho)^{2k}\sum_S F(S)^2$.

**Proof.** Write $r=1/\rho$, so $r\ge1$. For a finite coordinate set $s$, let $Y(s,H)$ be the multilinear evaluation using only subsets of $s$. We prove by induction on $s$ that a polynomial $H$ of degree at most $m$ satisfies $N_3(Y(s,H))^2\le r^{2m}\sum_{T\subseteq s}H(T)^2$. Constant random variables satisfy the estimate because their norm equals their absolute value and $r^{2m}\ge1$; this also handles degree zero, since all nonempty-set coefficients then vanish.

For the induction step, write $s$ as the disjoint union of its predecessor and a new coordinate $i$. Decompose the evaluation as $A+D X_i$, where $A$ uses coefficients not involving $i$ and $D$ is the evaluation of the coordinate derivative. The derivative has degree at most $m$ when $H$ has degree at most $m+1$ (`coordinateDerivative_degree`). The coefficient-square sum splits into the sum for $A$ plus the sum for the derivative, because the derivative's coefficient at $T$ is $H(T\cup\{i\})$ (`coordinateDerivative_coeff`). The new variable is independent of the pair $(A,D)` (`MultilinearMoments.indep_sum_of_notMem`). The independent affine three-norm inequality therefore bounds the squared norm of $A+D X_i$ by $N_3(A)^2+r^2N_3(D)^2$ (`independent_affine_three_norm_sq`). Applying the induction hypothesis to both pieces gives the desired coefficient bound: the second term has factor $r^2r^{2m}=r^{2(m+1)}$, matching the first, and the coefficient sums combine by the split just described. The base case of an empty coordinate set is the constant estimate. Taking the full coordinate set and $H=F$ proves the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.rvLpNorm_const`, `BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_coeff`, `BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_degree`, `BooleanAnalysis.Hypercontractivity.multilinear_sum_insert`, `BooleanAnalysis.Hypercontractivity.MultilinearMoments.indep_sum_of_notMem`, `BooleanAnalysis.GaussianSpace.Invariance.independent_affine_three_norm_sq`, `BooleanAnalysis.Hypercontractivity.rvLpNorm_const_mul`, `BooleanAnalysis.Hypercontractivity.MultilinearMoments.monomial_memLp_nat`.
