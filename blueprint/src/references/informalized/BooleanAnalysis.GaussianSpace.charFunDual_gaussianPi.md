<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Linear.lean :: BooleanAnalysis.GaussianSpace.charFunDual_gaussianPi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian linear functional characteristic function

**Claim.** For a continuous linear functional $L$ on $\mathbb R^n$, its characteristic function under independent standard Gaussian coordinates is $\exp(-\frac12\sum_i L(e_i)^2)$.

**Proof.** The characteristic function of a product measure under a continuous linear functional factors into the product of the one-dimensional characteristic functions (`charFunDual_pi`). For each coordinate, the standard Gaussian characteristic functional is $\exp(-L_i(1)^2/2)$ (`BooleanAnalysis.GaussianSpace.charFunDual_standardGaussian`), where $L_i$ is the functional obtained by restricting $L$ to that coordinate. The coordinate value $L_i(1)$ is $L(e_i)$. Multiplying these exponentials combines their exponents into $-\frac12\sum_i L(e_i)^2$, giving the formula.

**Key facts.** `BooleanAnalysis.GaussianSpace.charFunDual_standardGaussian`.
