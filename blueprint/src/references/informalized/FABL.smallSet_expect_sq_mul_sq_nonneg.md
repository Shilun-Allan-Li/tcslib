<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.smallSet_expect_sq_mul_sq_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative product of squared functions

**Claim.** For any two real-valued functions $d$ and $e$ on the Boolean cube, the uniform expectation of $d(x)^2e(x)^2$ is nonnegative.

**Proof.** For each $x$, both squares $d(x)^2$ and $e(x)^2$ are nonnegative, so their product is nonnegative. Taking the uniform expectation, a finite average with nonnegative weights, preserves nonnegativity.
