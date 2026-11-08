<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.IsHypercontractive.affine_three_norm_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Third-Norm Bound

**Claim.** Under the stated hypercontractivity, centering, and unit second-moment assumptions, the squared third-moment norm of $a+bX$ is at most $a^2+(b/\rho)^2$.

**Proof.** The hypercontractivity assumption includes $X\in L^3$, hence also $X\in L^2$ by monotonicity of integrability exponents on a probability space. The unit second-moment identity and the norm-moment formula (`rvLpNorm_rpow`) give $\|X\|_2^2=1$. Apply hypercontractivity with coefficients $a$ and $b/\rho$: its output is $a+\rho(b/\rho)X=a+bX$. Since $\rho>0$, this rescaling is valid. It follows that the third norm of $a+bX$ is at most the second norm of $a+(b/\rho)X$. Both norms are nonnegative, so squaring preserves the inequality. The affine second-moment identity (`rvLpNorm_affine_sq`) and the zero-mean assumption evaluate the squared second norm as $a^2+(b/\rho)^2\|X\|_2^2=a^2+(b/\rho)^2$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.rvLpNorm_rpow`, `BooleanAnalysis.Hypercontractivity.rvLpNorm_affine_sq`.
