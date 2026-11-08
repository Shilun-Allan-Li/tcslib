<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Noise.lean :: BooleanAnalysis.GaussianSpace.noiseOp_restrictLast_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Decomposition Along the Last Coordinate

**Claim.** For the restriction $f_b$ to the last bit, applying the noise operator on the first $n$ coordinates gives $(T_\rho f_b)(x)=(T_\rho a_f)(x)+\sigma(b)(T_\rho d_f)(x)$.

**Proof.** For each input $y$ on the first $n$ coordinates, the restriction to the last bit is $a_f(y)+\sigma(b)d_f(y)$. Indeed, the average and half-difference recover the false restriction as their sum and the true restriction as their difference (BooleanAnalysis.Hypercontractivity.restrictLast_false_eq and BooleanAnalysis.Hypercontractivity.restrictLast_true_eq); the sign $\sigma(b)$ selects the appropriate case. Apply linearity of the noise operator to this pointwise decomposition. Its coefficients are $1$ and $\sigma(b)$, so the resulting identity is exactly the claimed formula.

**Key facts.** `BooleanAnalysis.Hypercontractivity.restrictLast_false_eq`, `BooleanAnalysis.Hypercontractivity.restrictLast_true_eq`, `BooleanAnalysis.GaussianSpace.noiseOp_linear_combination`.
