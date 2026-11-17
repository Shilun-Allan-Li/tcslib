<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Fourier.lean :: BooleanAnalysis.GaussianSpace.integral_exp_mul_I_gaussianPi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Gaussian characteristic function

**Claim.** For $a\in\mathbb R^n$, the characteristic function of the linear form $\sum_i a_iX_i$ under product standard Gaussian measure is $\exp(-\tfrac12\sum_i a_i^2)$.

**Proof.** Represent the linear form as a continuous linear functional $L(t)=\sum_i a_it_i$. Its value on the $i$th coordinate unit vector is $a_i$, so the sum of the squares of these coordinate values is $\sum_i a_i^2$. The characteristic-function formula for a linear functional of a product Gaussian (\texttt{charFunDual_gaussianPi}) now gives the claimed exponential.

**Key facts.** `BooleanAnalysis.GaussianSpace.charFunDual_gaussianPi`.
