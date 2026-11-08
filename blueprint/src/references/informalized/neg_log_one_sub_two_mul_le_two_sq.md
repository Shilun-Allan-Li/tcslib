<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean :: neg_log_one_sub_two_mul_le_two_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A logarithmic quadratic bound

**Claim.** For every real $s$ with $|s|\le1/4$, $-s-\tfrac12\log(1-2s)\le2s^2$.

**Proof.** Define $f(u)=u^2+u+\log(1-u)$. The bound $|s|\le1/4$ places $2s$ in $[-1/2,1/2]$, where the logarithm is defined, and $f(0)=0$ (taylorAux_zero). Its derivative is $f'(u)=u(1-2u)/(1-u)$ (taylorAux_hasDerivAt). On $[0,1/2]$ this derivative is nonnegative, so $f$ is nondecreasing there; on $[-1/2,0]$ it is nonpositive, so $f$ is nonincreasing there. In either case, comparison with $0$ shows $f(2s)\ge f(0)=0$. Expanding yields $4s^2+2s+\log(1-2s)\ge0$, which rearranges to the asserted inequality.

**Key facts.** `taylorAux_zero`, `taylorAux_hasDerivAt`.
