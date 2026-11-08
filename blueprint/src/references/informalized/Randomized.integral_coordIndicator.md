<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ErrorReduction.lean :: Randomized.integral_coordIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Bernoulli Coordinate

**Claim.** For $p\in\mathbb{R}_{\ge 0}$ with $p\le 1$, under the product measure of independent Bernoulli-$p$ bits, the expected value of the indicator that coordinate $i$ is true is $p$.

**Proof.** Project the random vector onto coordinate $i$. The product-measure evaluation theorem says this projection sends the product measure to the one-coordinate Bernoulli measure. The change-of-variables formula for integrals therefore identifies the expected coordinate indicator with the expectation of the function that takes a Boolean $b$ to $1$ when $b$ is true and $0$ otherwise, under that Bernoulli measure. The Bernoulli expectation formula gives this expectation as $p$.
