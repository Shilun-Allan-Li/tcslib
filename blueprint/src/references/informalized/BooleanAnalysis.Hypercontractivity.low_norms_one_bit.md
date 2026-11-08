<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.low_norms_one_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-bit hypercontractivity

**Claim.** For a function on the one-bit cube and $1<p\le q\le2$, noise with parameter $\sqrt{(p-1)/(q-1)}$ does not increase its norm from exponent $p$ to exponent $q$.

**Proof.** Write the one-bit function in its two Fourier coefficients $a$ and $b$. Its two values are $a+b$ and $a-b$, while after applying the noise operator they are $a+\rho b$ and $a-\rho b$, where $\rho=\sqrt{(p-1)/(q-1)}$. The formula for the uniform one-bit power mean expresses both norms as the corresponding two-point averages. It remains to prove the two-point inequality for these averages.

By symmetry, replace $b$ by $|b|$ and assume $b\ge0$. Changing the overall sign of the function leaves both norms unchanged, so also assume $a\ge0$. If $a\ge b$, the case $a=0$ is immediate; otherwise set $t=b/a\in[0,1]$. Apply the unit-scale two-point inequality at $t$, then multiply by the nonnegative scale factor $a$ to recover the desired inequality for $a,b$.

If $a<b$, compare the two noisy absolute values with the corresponding values after exchanging the roles of $a$ and $b$: $|a\pm\rho b|\le|b\pm\rho a|$, using $0\le\rho\le1$. Monotonicity of positive powers bounds the noisy average by this exchanged average. Since $a/b\in[0,1]$, the unit-scale inequality applied at $a/b$ bounds the exchanged average by the unnoised $p$-average for $a,b$. These cases prove the two-point estimate. Substituting the one-bit power-mean formula and the Fourier description of the noise operator yields the claimed norm inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.expect_abs_rpow_one_bit`, `BooleanAnalysis.Hypercontractivity.two_point_ineq_general_unit`.
