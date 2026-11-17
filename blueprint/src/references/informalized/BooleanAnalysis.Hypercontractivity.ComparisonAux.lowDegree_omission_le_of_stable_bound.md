<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.lowDegree_omission_le_of_stable_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low degree mass outside a coordinate set

**Claim.** Under the stated positivity, parameter, influence, and stability hypotheses, the weighted mass of components of degree at most $k$ whose coordinate sets are not contained in $J$ is at most $\sqrt{\tau}\,I(f)$.

**Proof.** For each coordinate set $S$, let $E(S)=\mathbb E_P f_S^2$, which is nonnegative because it is an expectation of squares with nonnegative product masses. The weighted omission bound ($\texttt{weighted\_lowDegree\_omission\_le}$), applied to these nonnegative component energies, bounds the quantity in question by the sum, over coordinates outside $J$, of the weighted energies of all components containing that coordinate. For each such coordinate $i$, stability bounds this inner sum by $I_i(f)^{3/2}$. The influence $I_i(f)$ is itself nonnegative, being the expectation of the square of the coordinate Laplacian. Hence $I_i(f)^{3/2}=I_i(f)\sqrt{I_i(f)}$. Since $i\notin J$ gives $I_i(f)\le\tau$, monotonicity of square root yields $I_i(f)^{3/2}\le I_i(f)\sqrt\tau$. Coordinates in $J$ contribute zero, which is also at most $I_i(f)\sqrt\tau$. Summing over all coordinates gives $\sqrt\tau\sum_i I_i(f)=\sqrt\tau I(f)$, as required.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteNorms.weighted_lowDegree_omission_le`.
