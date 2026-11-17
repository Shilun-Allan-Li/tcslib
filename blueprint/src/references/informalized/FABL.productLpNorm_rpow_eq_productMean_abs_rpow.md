<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.productLpNorm_rpow_eq_productMean_abs_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power of the Product-Space Norm

**Claim.** For $p>0$, the $p$th power of the product-space $L^p$ norm of $f$ equals the product-distribution mean of $|f|^p$.

**Proof.** The mean of $|f|^p$ is nonnegative because each summand is nonnegative and expectations preserve nonnegativity (`pmfExpectation_nonneg`). By definition, the norm is this mean raised to the power $1/p$. The law for composing real powers on a nonnegative base turns its $p$th power into the mean raised to $(1/p)p$. Since $p>0$, this exponent is $1$, so the result is the original mean.

**Key facts.** `FABL.pmfExpectation_nonneg`.
