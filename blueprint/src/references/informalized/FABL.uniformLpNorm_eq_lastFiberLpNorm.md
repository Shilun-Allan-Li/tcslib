<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.uniformLpNorm_eq_lastFiberLpNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Norm by Fibers

**Claim.** For $q>0$, the uniform $L^q$ quantity of a function on the $(n+1)$-dimensional Boolean cube equals the uniform $L^q$ quantity on the $n$-dimensional cube of its two-point fiber norms.

**Proof.** Raise both sides to the power $q$. By the identity that the $q$th power of the uniform norm is the uniform average of $|f|^q$ ( `FABL.uniformLpNorm_rpow`), it suffices to compare the resulting averages. The average over the larger cube can be computed by first fixing the first $n$ coordinates and then averaging over the last sign; this is the expectation decomposition along the last coordinate (`FABL.expect_snoc`). For each fixed $x$, the inner average of $|f(x,a)|^q$ over the two signs is exactly the $q$th power of the fiber norm at $x$. That fiber norm is nonnegative (`FABL.uniformLpNorm_nonneg`), so its absolute value in the outer norm can be removed. The two powered averages therefore agree, and taking the common positive power $1/q$ gives the asserted equality.

**Key facts.** `FABL.uniformLpNorm_rpow`, `FABL.expect_snoc`, `FABL.uniformLpNorm_nonneg`.
