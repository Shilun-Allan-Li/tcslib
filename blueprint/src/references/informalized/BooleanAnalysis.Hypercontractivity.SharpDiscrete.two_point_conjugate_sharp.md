<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointLaw.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.two_point_conjugate_sharp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp conjugate contraction for a two point law

**Claim.** For the stated two point law with $q>2$ and $0<\lambda<1/2$, the affine contraction from exponent $q/(q-1)$ to exponent $2$ holds at the sharp radius $\rho(q,\lambda)$, with the required exponent ordering, nonnegative parameter below one, and integrability.

**Proof.** Let $p=q/(q-1)$; then $1<p<2$ and $p/(p-1)=q$. The prescribed masses sum to one, so the random variable is almost surely supported on $1-\lambda$ and $-\lambda$ (`FiniteLaw.ae_two_point_of_mass_sum`). This finite support gives the required integrability at both exponents (`HasAtomLowerBound.memLp`). The radius has $0<\rho(q,\lambda)<1$ (`SharpDiscrete.radius_pos_lt_one`), and the exponent bounds give the required ordering. To prove the contraction, fix $a,b$ and set $u=a+b(1-\lambda)$ and $v=a-b\lambda$, the affine input's values at the two atoms. The weighted two point inequality (`SharpDiscrete.weighted_biased_two_point_le`) bounds the square of the output norm by the corresponding weighted $p$-moment raised to $2/p$: the weighted mean of $u,v$ is $a$, and their difference is $b$. Applying the two point affine norm formula (`FiniteLaw.two_point_affine_norm_sq`) identifies these quantities with the squared $L^2$ norm of $a+\rho bX$ and the squared $L^p$ norm of $a+bX$. Taking square roots and translating the finite norms back to the stated extended norms proves the contraction for every $a,b$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteLaw.ae_two_point_of_mass_sum`, `BooleanAnalysis.Hypercontractivity.HasAtomLowerBound.memLp`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_pos_lt_one`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_biased_two_point_le`, `BooleanAnalysis.Hypercontractivity.FiniteLaw.two_point_affine_norm_sq`.
