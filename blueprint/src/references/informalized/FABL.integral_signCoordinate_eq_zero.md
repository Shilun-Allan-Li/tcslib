<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integral_signCoordinate_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a sign coordinate

**Claim.** For a uniform sign vector and any coordinate $i$, the expected value of its $i$th coordinate is zero.

**Proof.** The integral under the uniform sign-vector measure equals expectation under the uniform distribution (`integral_uniformPMF_eq_expect`). The coordinate function is the monomial supported on the singleton set $\{i\}$. The expectation of a monomial is zero unless its support is empty (`expect_monomial`); since $\{i\}$ is nonempty, this expectation is zero.

**Key facts.** `FABL.integral_uniformPMF_eq_expect`, `FABL.expect_monomial`.
