<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean :: BooleanAnalysis.Hypercontractivity.one_bit_p2_hypercontractivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-bit hypercontractivity

**Claim.** For $1\le p\le2$, if $\rho\ge0$ and $\rho^2\le p-1$, then the one-bit noise operator satisfies $\|T_\rho f\|_2\le\|f\|_p$.

**Proof.** Write $a$ and $b$ for the constant and one-coordinate Fourier coefficients of $f$. The one-bit noise operator has squared second moment $a^2+\rho^2b^2$, by the one-bit noise second-moment identity (`expect_noiseOp_sq_one_bit`). The $p$th absolute moment of $f$ is $\bigl(|a+b|^p+|a-b|^p\bigr)/2$, by the one-bit two-point moment identity (`expect_abs_rpow_one_bit`). Substituting these identities into the desired norm inequality reduces it exactly to the two-point hypercontractive inequality, which applies under $1\le p\le2$, $\rho\ge0$, and $\rho^2\le p-1$ (`two_point_ineq`).

**Key facts.** `BooleanAnalysis.Hypercontractivity.expect_noiseOp_sq_one_bit`, `BooleanAnalysis.Hypercontractivity.expect_abs_rpow_one_bit`, `BooleanAnalysis.Hypercontractivity.two_point_ineq`.
