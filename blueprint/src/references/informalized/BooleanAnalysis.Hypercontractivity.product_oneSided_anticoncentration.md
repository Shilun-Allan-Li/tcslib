<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.product_oneSided_anticoncentration -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-sided anticoncentration

**Claim.** Under the stated atom lower bound and positive variance assumptions, a finite product function of degree at most $k$ has probability at least $\frac14(\exp(2)/(2\lambda))^{-k}$ of exceeding its expectation; the stated coarser exponential lower bound also holds.

**Proof.** Center the function by setting $g=f-\mathbb E f$. Its expectation is zero, and subtracting a constant preserves the degree bound. The degree-dependent $L^1$-to-$L^2$ estimate bounds $\|g\|_2$ by the product norm-comparison constant to the power $k$ times $\|g\|_1$. The comparison constant is at most $C=\exp(1)/\sqrt{2\lambda}$, so nonnegativity of $\|g\|_1$ gives $\|g\|_2\le C^k\|g\|_1$. The centered probability estimate now gives $\frac14(C^k)^{-2}\le\Pr[g>0]$. Since $C^2=\exp(2)/(2\lambda)$ and $g>0$ is exactly the event $f>\mathbb E f$, this is the first claimed bound. For the second inequality, positive variance and the degree assumption imply $k>0$; applying the coarse anticoncentration lower bound with this fact gives the result.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.mass_sum`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.hasDegreeLE_sub_const`, `BooleanAnalysis.Hypercontractivity.product_lowDegree_l1_l2`, `BooleanAnalysis.Hypercontractivity.productNormComparisonConstant_le`, `BooleanAnalysis.Hypercontractivity.ComparisonAux.centered_probability_ge_of_norm_comparison`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.degree_pos_of_variance_pos`, `BooleanAnalysis.Hypercontractivity.ComparisonAux.anticoncentration_coarse_lower_bound`.
