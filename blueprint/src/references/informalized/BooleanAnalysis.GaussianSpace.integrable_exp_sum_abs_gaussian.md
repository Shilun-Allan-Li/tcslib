<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Exponential.lean :: BooleanAnalysis.GaussianSpace.integrable_exp_sum_abs_gaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Exponential Moments of Coordinate Sums

**Claim.** For each natural number $n$ and real $c$, the function $x\mapsto\exp\bigl(c\sum_{i=1}^n|x_i|\bigr)$ is integrable under the product of $n$ standard Gaussian measures.

**Proof.** For each coordinate, the one-dimensional function $y\mapsto e^{c|y|}$ is integrable under the standard Gaussian law: on the two half-lines it is controlled by the exponential functions $e^{cy}$ and $e^{-cy}$, each of which has a finite Gaussian exponential moment. Integrability of these one-coordinate functions implies integrability of their finite product under the product measure. Finally, the identity $\exp(c\sum_i|x_i|)=\prod_i\exp(c|x_i|)$ identifies that product with the function in question.
