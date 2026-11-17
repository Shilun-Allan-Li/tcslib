<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.cube_lowDegree_projection_noise -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noisy Low Degree Projection Bound

**Claim.** For $0<\rho\le1$, the fourth power mean of the degree-$k$ Fourier truncation of $g$ satisfies $\|g^{\le k}\|_4\le(\sqrt3/\rho)^k\|T_\rho g\|_4$.

**Proof.** Set $r=\sqrt3/\rho$ and let $f$ be the degree-$k$ truncation of $T_\rho g$. Since $\rho\le1\le\sqrt3$, we have $r\ge1$. The composition rule for noise operators says that successive noise parameters multiply (\texttt{BooleanAnalysis.Hypercontractivity.noiseOp_compose}). On each Fourier coefficient of degree at most $k$, the combined parameter $(1/\sqrt3)r$ followed by the original factor $\rho$ cancels to one; coefficients above degree $k$ are removed by the truncation. Thus $T_{1/\sqrt3}(T_r f)=g^{\le k}$, using the noise action on Fourier coefficients (\texttt{BooleanAnalysis.noiseOp_fourier}) and the truncation coefficient formula (\texttt{KKL.fourierCoeff_lowDegreePart}).

Apply the one-function hypercontractive estimate from exponent two to exponent four with noise parameter $1/\sqrt3$. Its parameter condition holds with equality, and it yields $\|T_{1/\sqrt3}(T_r f)\|_4\le\|T_r f\|_2$ (\texttt{BooleanAnalysis.Hypercontractivity.general_one_function_hypercontractivity}). The order-two power mean equals the $L^2$ norm (\texttt{BooleanAnalysis.Hypercontractivity.cubeLpNorm_two}), so the cancellation identity bounds the desired norm by $\|T_r f\|_2$. Because $f$ has degree at most $k$ and $r\ge1$, the degree-sensitive $L^2$ noise bound gives $\|T_r f\|_2\le r^k\|f\|_2$ (\texttt{BooleanAnalysis.Hypercontractivity.l2Norm_noiseOp_le}). Projection is contractive in $L^2$ (\texttt{BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.cube_lowDegree_l2_le}), hence $\|f\|_2\le\|T_\rho g\|_2$. Monotonicity of power means then gives $\|T_\rho g\|_2\le\|T_\rho g\|_4$ (\texttt{BooleanAnalysis.Hypercontractivity.lp_norm_mono}). Combining these estimates and substituting $r=\sqrt3/\rho$ proves the bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.noiseOp_compose`, `BooleanAnalysis.noiseOp_fourier`, `KKL.fourierCoeff_lowDegreePart`, `BooleanAnalysis.Hypercontractivity.general_one_function_hypercontractivity`, `BooleanAnalysis.Hypercontractivity.cubeLpNorm_two`, `BooleanAnalysis.Hypercontractivity.l2Norm_noiseOp_le`, `BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.cube_lowDegree_l2_le`, `BooleanAnalysis.Hypercontractivity.lp_norm_mono`.
