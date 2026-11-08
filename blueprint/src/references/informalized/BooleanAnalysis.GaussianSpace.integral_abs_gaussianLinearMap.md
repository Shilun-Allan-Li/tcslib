<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SmoothVariation.lean :: BooleanAnalysis.GaussianSpace.integral_abs_gaussianLinearMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Moment of a Gaussian Linear Functional

**Claim.** For a continuous linear functional $L$ on $\mathbb R^n$, its absolute first moment under standard Gaussian measure is $\sqrt{\sum_i L(e_i)^2}\,2\varphi(0)$, where $e_i$ are the standard coordinate vectors.

**Proof.** Write $a_i=L(e_i)$. A linear functional on this finite-dimensional coordinate space satisfies $L(z)=\sum_i a_i z_i$. The absolute-moment formula for a Gaussian linear form (`integral_abs_gaussianProjection`) therefore applies to these coefficients and gives $\int |L(z)|\,d\gamma_n(z)=\sqrt{\sum_i a_i^2}\,2\varphi(0)$.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_abs_gaussianProjection`.
