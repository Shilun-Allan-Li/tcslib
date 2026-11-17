<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Linear.lean :: BooleanAnalysis.GaussianSpace.charFunDual_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standard Gaussian characteristic functional

**Claim.** The characteristic functional of the standard Gaussian measure at a continuous real-linear functional $L$ is $\exp(-((L(1))^2)/2)$, viewed as a complex number.

**Proof.** The characteristic functional of a measure under a linear map equals the characteristic function of the pushforward measure (`charFunDual_eq_charFun_map_one`). Every real-linear functional on $\mathbb R$ is multiplication by its value at $1$: linearity gives $L(x)=L(1)x$. Thus the pushforward of the standard Gaussian by $L$ is the law of a standard Gaussian multiplied by $L(1)$. The scaling formula for Gaussian measures and the standard Gaussian characteristic function then give the exponential with exponent $-L(1)^2/2$.
