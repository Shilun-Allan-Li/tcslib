<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BasicFourierFormulas.lean :: FABL.uniformLpNorm_two_eq_sqrt_uniformInner -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Moment and Uniform Norm

**Claim.** For every real-valued function $f$ on the $n$-dimensional sign cube, its uniform $L^2$ norm equals the square root of its uniform inner product with itself.

**Proof.** The uniform $L^2$ norm is the square root of the uniform average of $f(x)^2$ (the second-moment identity, `uniformLpNorm_two_eq_sqrt_expect_sq`). Rewrite the uniform inner product as the uniform average of the pointwise inner products. Since the values of $f$ are real, their pointwise inner product is $f(x)f(x)=f(x)^2$. The two averages therefore agree, and taking their square roots gives the claim.

**Key facts.** `FABL.uniformLpNorm_two_eq_sqrt_expect_sq`.
