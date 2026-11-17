<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/FiniteLaw.lean :: BooleanAnalysis.Hypercontractivity.FiniteLaw.centered_two_point_moments -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered Two-Point Moments

**Claim.** If $X$ takes the value $1-\lambda$ with probability $\lambda$ and $-\lambda$ with probability $1-\lambda$, where $0\leq\lambda\leq1$, then its integral is zero and $N_2(X)^2=\lambda(1-\lambda)$.

**Proof.** The two values $1-\lambda$ and $-\lambda$ are distinct. Their stated masses add to one, so the almost-sure two-point support result ( `ae_two_point_of_mass_sum`) shows that $X$ takes one of these values almost everywhere. The finite-law integration formula ( `finite_law_integral`) then computes its integral as $\lambda(1-\lambda)+(1-\lambda)(-\lambda)=0$. For the norm, apply the two-point affine norm formula ( `two_point_affine_norm_sq`) with the affine function equal to $X$ itself, that is, with $a=0$, $b=1$, and exponent $q=2$. The formula reduces the squared norm to $\lambda|1-\lambda|^2+(1-\lambda)|-\lambda|^2$. Since $0\leq\lambda\leq1$, this is $\lambda(1-\lambda)^2+(1-\lambda)\lambda^2=\lambda(1-\lambda)$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteLaw.ae_two_point_of_mass_sum`, `BooleanAnalysis.Hypercontractivity.FiniteLaw.finite_law_integral`, `BooleanAnalysis.Hypercontractivity.FiniteLaw.two_point_affine_norm_sq`.
