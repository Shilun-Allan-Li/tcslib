<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.tendsto_gLog_div_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Gaussian tail asymptotics

**Claim.** For the standard Gaussian cumulative distribution function $\Phi$, the quantity $L(t)=2\log(1/\Phi(t))$ satisfies $L(t)/t^2\to 1$ as $t\to-\infty$.

**Proof.** For negative $t$, the identity for $L(t)$ expresses it as $t^2$ plus three terms: $-2\log(\operatorname{millsRatio}(t))$, $2\log(-t)$, and the constant $2\log(\sqrt{2\pi})$. Divide this identity by $t^2$. The Mills ratio tends to $1$ (`tendsto_millsRatio`), so continuity of the logarithm at $1$ shows its logarithm tends to zero; multiplying by $1/t^2$, which also tends to zero (`tendsto_inv_sq_atBot`), makes the first term vanish. The logarithmic term vanishes by the fact that $\log(-t)/t^2\to0$ (`tendsto_log_neg_div_sq`), and the constant term vanishes by reciprocal-square decay. The remaining term is $t^2/t^2=1$ for $t<0$. Thus the quotient tends to $1$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.tendsto_millsRatio`, `BooleanAnalysis.ThresholdFunctions.tendsto_inv_sq_atBot`, `BooleanAnalysis.ThresholdFunctions.tendsto_log_neg_div_sq`, `BooleanAnalysis.ThresholdFunctions.gLog_eq`.
