<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointLaw.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.two_point_forward_sharp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp forward contraction for a two point law

**Claim.** For the stated two point law with $q>2$ and $0<\lambda<1/2$, the affine contraction from exponent $2$ to exponent $q$ holds at $\rho(q,\lambda)$, with the required exponent ordering, nonnegative parameter below one, and integrability.

**Proof.** The two prescribed masses add to one, so $X$ is almost surely supported on $1-\lambda$ and $-\lambda$ (`FiniteLaw.ae_two_point_of_mass_sum`). Hence it belongs to $L^2$ and $L^q$ (`HasAtomLowerBound.memLp`). The exponent ordering follows from $q>2$, and the radius lies strictly between zero and one (`SharpDiscrete.radius_pos_lt_one`). Fix $a,b$ and write $u=a+b(1-\lambda)$ and $v=a-b\lambda$. Their weighted mean is $a$, and the forward weighted two point inequality (`SharpDiscrete.weighted_biased_forward_le`) bounds the weighted $q$-moment of their images under the averaging map by their weighted second moment. The two point affine norm formula (`FiniteLaw.two_point_affine_norm_sq`) identifies these moments with the squared $L^q$ norm of $a+\rho bX$ and the squared $L^2$ norm of $a+bX$. Taking square roots yields the required norm contraction for every $a,b$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteLaw.ae_two_point_of_mass_sum`, `BooleanAnalysis.Hypercontractivity.HasAtomLowerBound.memLp`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_pos_lt_one`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_biased_forward_le`, `BooleanAnalysis.Hypercontractivity.FiniteLaw.two_point_affine_norm_sq`.
