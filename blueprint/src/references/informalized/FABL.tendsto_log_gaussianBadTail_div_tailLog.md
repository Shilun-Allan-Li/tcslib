<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.tendsto_log_gaussianBadTail_div_tailLog -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ratio of Gaussian Tail Logarithms

**Claim.** For fixed $0<\rho<1$, the ratio of the shifted Gaussian tail logarithm to the standard Gaussian tail logarithm tends to $1/\rho^2$ as $t\to+\infty$.

**Proof.** Divide each logarithm by $t^2$. The shifted tail logarithm divided by $t^2$ tends to $-1/(2\rho^2)$ (`tendsto_log_gaussianBadTail_div_sq`), while the standard tail logarithm divided by $t^2$ tends to $-1/2$ (`tendsto_log_standardGaussianUpperTail_div_sq`). Since the latter limit is nonzero, the quotient tends to the quotient of these limits, namely $1/\rho^2$. For sufficiently large $t$, the standard tail lies strictly between zero and one (`standardGaussianUpperTail_pos`, `standardGaussianUpperTail_lt_one`), so its logarithm is nonzero. Thus canceling the common factor $t^2$ identifies this quotient with the stated ratio.

**Key facts.** `FABL.tendsto_log_gaussianBadTail_div_sq`, `FABL.tendsto_log_standardGaussianUpperTail_div_sq`, `FABL.standardGaussianUpperTail_pos`, `FABL.standardGaussianUpperTail_lt_one`.
