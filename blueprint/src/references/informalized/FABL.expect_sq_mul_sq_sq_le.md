<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.expect_sq_mul_sq_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth-Moment Product Inequality

**Claim.** The square of the uniform expectation of $d(x)^2e(x)^2$ is at most the product of the uniform expectations of $d(x)^4$ and $e(x)^4$.

**Proof.** Apply the finite-sum Cauchy–Schwarz inequality to the functions $x\mapsto d(x)^2$ and $x\mapsto e(x)^2$ on the full cube. It bounds the square of their mean product by the product of their mean squares. Those means are precisely the expectation of $d^2e^2$, the expectation of $d^4$, and the expectation of $e^4$, respectively.
