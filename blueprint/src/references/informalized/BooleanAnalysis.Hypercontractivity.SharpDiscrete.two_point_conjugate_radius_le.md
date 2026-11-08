<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointLaw.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.two_point_conjugate_radius_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Necessary radius for a two point law

**Claim.** Under the stated two point law and affine hypercontractive contraction from exponent $q/(q-1)$ to exponent $2$, the parameter $\rho$ is at most the sharp discrete hypercontractive radius $\rho(q,\lambda)$.

**Proof.** Put $p=q/(q-1)$. Since $q>2$, the exponents satisfy $1<p<2$. The hypercontractive hypothesis supplies the affine norm comparison; finiteness of the relevant norms allows it to be expressed as a comparison of squared real $L^p$ norms. For arbitrary real $u,v$, choose the affine input with coefficients $a=\lambda u+(1-\lambda)v$ and $b=u-v$. At the two possible values $1-\lambda$ and $-\lambda$ of $X$, this input takes the values $u$ and $v$, respectively. The two point norm formula (`FiniteLaw.two_point_affine_norm_sq`) therefore converts the norm comparison into
\[(\lambda u+(1-\lambda)v)^2+\rho^2\lambda(1-\lambda)(u-v)^2\le (\lambda|u|^p+(1-\lambda)|v|^p)^{2/p}.\]
The two point criterion for the sharp radius (`SharpDiscrete.weighted_biased_radius_le`) says that this inequality for every $u,v$ forces $\rho\le\rho(p/(p-1),\lambda)$. Since $p/(p-1)=q$, this is the claimed bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteLaw.two_point_affine_norm_sq`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_biased_radius_le`.
