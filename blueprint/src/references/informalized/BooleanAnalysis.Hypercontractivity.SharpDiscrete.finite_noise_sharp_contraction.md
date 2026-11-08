<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseContraction.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_sharp_contraction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp Finite Noise Contraction

**Claim.** For the sharp discrete radius determined by $q$ and the lower bound $\lambda$ on the weights, the quadratic form of every function is at most its weighted $p$-moment raised to the power $2/p$, where $p=q/(q-1)$.

**Proof.** The weights are positive, $1<p<2$, and the sharp radius lies strictly between zero and one. Homogeneity reduces the desired inequality to proving that the quadratic form is at most one for every function with unit moment. Choose a nonnegative unit-moment maximizer of the quadratic form; maximality lets us bound the objective of any other unit-moment function by that of this maximizer. The two-values theorem says the maximizer takes values $a,b\ge0$.

If it is constant, its unit moment and the weights summing to one force its value to be one, so its quadratic form is one. Otherwise, let $\gamma$ be the total weight of the coordinates where it takes value $a$. The mass dichotomy ensures $\lambda\le\gamma\le1-\lambda$. The two-value sum identity expresses its first and second moments, and its unit moment, as the corresponding weighted two-point expressions with masses $\gamma$ and $1-\gamma$. The scalar atom-bound inequality then shows its quadratic form is at most one. This proves the unit-moment bound; scaling by moment homogeneity yields the claim for arbitrary $f$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_pos_lt_one`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_contraction_of_unit_bound`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.exists_nonnegative_noise_maximizer`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_maximizer_two_values`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_two_value_mass_dichotomy`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_two_value_sum`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_two_point_le_of_atom_bound`.
