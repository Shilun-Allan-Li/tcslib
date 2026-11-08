<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.integrableOn_millsF' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability on negative half-lines

**Claim.** For every $t<0$, the function $H(x)=\varphi(x)(1-3x^{-4})$, with the stated convention at zero, is integrable on $(-\infty,t]$.

**Proof.** Because $t<0$, every $x\le t$ is nonzero and satisfies $x^4\ge t^4>0$. Thus $(x^4)^{-1}\le(t^4)^{-1}$, which bounds the absolute value of the factor $1-3(x^4)^{-1}$ by $1+3(t^4)^{-1}$. The Gaussian density is positive (`standardGaussianPDF_pos`), so this yields $|H(x)|\le (1+3(t^4)^{-1})\varphi(x)$ on the half-line. The right side is an integrable constant multiple of the Gaussian density. The function $H$ is measurable (`measurable_millsF'`), and this domination therefore gives integrability on the half-line.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.measurable_millsF'`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`.
