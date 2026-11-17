<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.expect_sq_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative squared expectation

**Claim.** For any real-valued function on the sign cube, the uniform expectation of its square is nonnegative.

**Proof.** Write the uniform expectation as the sum of the values $f(x)^2$ over the finite cube, divided by the cube's positive cardinality. Every summand is nonnegative, so the sum and hence the expectation are nonnegative.
