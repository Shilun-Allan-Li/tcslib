<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.expect_linearForm_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second moment of a sign linear form

**Claim.** For a real coefficient vector on the sign cube, the expected square of its linear form is the sum of the squares of its coefficients.

**Proof.** Write the linear form as a sum of its coefficients times the singleton monomials, which are the individual coordinate signs. Expand its square into a double sum and move the finite sums outside the expectation. The expected product of two coordinate monomials is $1$ when their coordinates agree and $0$ otherwise (the monomial orthogonality identity, `FABL.expect_monomial_mul`). Thus only the diagonal terms remain, giving the sum of the squared coefficients.

**Key facts.** `FABL.expect_monomial_mul`.
