<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/TwoDivPi.lean :: FABL.integral_twoDivPiSignCoordinate_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Rademacher coordinate

**Claim.** For a uniformly chosen sign vector, the mean of the sign in any fixed coordinate is zero.

**Proof.** Rewrite integration against the measure induced by the uniform probability mass function as expectation under the uniform distribution (`integral_uniformPMF_eq_expect`). The coordinate sign is precisely the monomial indexed by the singleton containing that coordinate: the singleton product has just that one factor. The expectation of a monomial indexed by a nonempty set is zero (`expect_monomial`); since a singleton is nonempty, the desired mean vanishes.

**Key facts.** `FABL.integral_uniformPMF_eq_expect`, `FABL.expect_monomial`.
