<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.bonami_expect_sq_mul_sq_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative product of second moments

**Claim.** For real-valued functions $d$ and $e$ on the $n$-dimensional sign cube, the uniform expectation of $d(x)^2e(x)^2$ is nonnegative.

**Proof.** For each point $x$, both squares $d(x)^2$ and $e(x)^2$ are nonnegative, and hence their product is nonnegative. Taking the uniform expectation, a finite average with nonnegative weights, preserves nonnegativity.
