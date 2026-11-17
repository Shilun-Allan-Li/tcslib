<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.gLog_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Gaussian tail identity

**Claim.** For $t<0$, the logarithmic Gaussian tail scale satisfies $L(t)=-2\log R(t)+2\log(-t)+2\log\sqrt{2\pi}+t^2$.

**Proof.** Since $t<0$, we have $-t>0$, and the Gaussian CDF and density are positive. The logarithm of the Mills ratio can therefore be expanded using the logarithm of a quotient and a product: $\log R(t)=\log\Phi(t)+\log(-t)-\log\varphi(t)$. The standard Gaussian density has logarithm $\log\varphi(t)=-\log\sqrt{2\pi}-t^2/2$ (`log_standardGaussianPDF`). Also, $\log(1/\Phi(t))=-\log\Phi(t)$. Substituting these expressions into $L(t)=2\log(1/\Phi(t))$ and rearranging gives the claimed identity.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_pos`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`, `BooleanAnalysis.ThresholdFunctions.log_standardGaussianPDF`.
