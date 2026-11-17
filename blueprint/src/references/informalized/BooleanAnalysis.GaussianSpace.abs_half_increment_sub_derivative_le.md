<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/DiscreteApproximation.lean :: BooleanAnalysis.GaussianSpace.abs_half_increment_sub_derivative_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Half-Increment Derivative Error Bound

**Claim.** If $f$ is differentiable everywhere and its derivative map is $C$-Lipschitz, then the half-increment approximation error in direction $v$ and step $h$ is at most $\frac C2 h^2\|v\|^2$.

**Proof.** Apply the linearization remainder bound (BooleanAnalysis.GaussianSpace.norm_linearization_remainder_le) between $x$ and $x+h v$. The displacement is $hv$, and the derivative at $x$ applied to that displacement is $hDf(x)[v]$. Consequently, the absolute value of $f(x+hv)-f(x)-hDf(x)[v]$ is at most $C\|hv\|^2=C h^2\|v\|^2$. The expression in the claim is exactly half this remainder in absolute value; dividing the estimate by $2$ gives the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.norm_linearization_remainder_le`.
