<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BasicFourierFormulas.lean :: FABL.uniformLpNorm_two_sq_eq_uniformInner -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Norm and Uniform Inner Product

**Claim.** For every real-valued function $f$ on the $n$-dimensional sign cube, the square of its uniform $L^2$ norm equals its uniform inner product with itself, namely the uniform average of $f(x)^2$.

**Proof.** Use `uniformLpNorm_two_sq_eq_expect_sq` to express the squared norm as the uniform average of $f(x)^2$. The uniform inner product is the uniform average of the pointwise inner product; for real values, that pointwise inner product is $f(x)f(x)=f(x)^2$. Hence the two expressions agree.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_expect_sq`.
