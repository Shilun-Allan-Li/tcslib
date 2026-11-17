<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.rvLpNorm_affine_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared norm of a centered affine function

**Claim.** On a probability space, if $X$ belongs to $L^2$ and has mean zero, then for all real $a,b$, $N_2(a+bX)^2=a^2+b^2N_2(X)^2$.

**Proof.** The affine function $a+bX$ belongs to $L^2$, because constants and scalar multiples of an $L^2$ function do. The power integral formula for the norm ($\texttt{rvLpNorm\_rpow}$) at exponent $2$ identifies each squared norm with the integral of the square; here $|Y|^2=Y^2$. Expand $(a+bX)^2=a^2+2abX+b^2X^2$ inside the integral. Integrability of $X$ and $X^2$ permits splitting the integral into its three terms. Since the measure is a probability measure, the integral of the constant $a^2$ is $a^2$, while the middle term integrates to zero by the mean-zero assumption. The remaining term is $b^2\int X^2$, which the same power integral formula identifies as $b^2N_2(X)^2$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.rvLpNorm_rpow`.
