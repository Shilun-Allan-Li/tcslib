<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.hasDerivAt_millsF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Mills Function

**Claim.** For every nonzero real $x$, the function $F(y)=\varphi(y)(y^{-3}-y^{-1})$ is differentiable at $x$ and $F'(x)=\varphi(x)(1-3x^{-4})$.

**Proof.** Differentiate the two inverse powers at $x$. Since $x\ne0$, their derivatives are $-3x^2/x^6=-3x^{-4}$ and $-x^{-2}$, respectively, so the derivative of their difference is $x^{-2}-3x^{-4}$. The density satisfies $\varphi'(x)=-x\varphi(x)$ (\texttt{hasDerivAt_standardGaussianPDF}). The product rule therefore gives
\[
F'(x)=\varphi(x)(x^{-3}-x^{-1})(-x)+\varphi(x)(x^{-2}-3x^{-4}).
\]
The first term simplifies to $\varphi(x)(x^{-2}-1)$; adding the second cancels the $x^{-2}$ terms and leaves $\varphi(x)(1-3x^{-4})$, as claimed.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianPDF`.
