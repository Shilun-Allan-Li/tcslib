<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointContraction.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_biased_forward_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward weighted two point contraction

**Claim.** For $q>2$ and $0<\lambda<1/2$, the sharp radius and the weighted mean $m=\lambda u+(1-\lambda)v$ satisfy the stated forward two point contraction inequality.

**Proof.** Regard $u,v$ as a function on the two element set, with weights $\lambda$ and $1-\lambda$. Put $p=q/(q-1)$, so $1<p<2$. The weighted two point inequality (`SharpDiscrete.weighted_biased_two_point_le`), together with the conjugacy identity $p/(p-1)=q$, gives for every function $g$ on these two points the quadratic contraction bound required by finite noise duality. Applying that duality (`SharpDiscrete.finite_noise_duality`) to the function taking values $u,v$ bounds the weighted $q$-moment after averaging toward its weighted mean by the original weighted second moment. Expanding the two point sums gives exactly the asserted inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_biased_two_point_le`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_duality`.
