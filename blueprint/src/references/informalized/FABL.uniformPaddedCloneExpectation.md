<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.uniformPaddedCloneExpectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation under uniform padding

**Claim.** For $a\le r$ and $M>0$, the uniform expectation of a function of the first $a$ coordinates of a uniformly chosen $r$-coordinate function equals its uniform expectation over functions on those first $a$ coordinates.

**Proof.** Split a function on the first $r$ positions into its restriction to the first $a$ positions and its values on the remaining positions. The padded-clone tuple equivalence used in the proof identifies the original function space with the product of these two spaces, and under that identification the integrand depends only on the first component. Expectation over a finite product is the iterated expectation over its two factors (\texttt{fintype\_expect\_prod}). For every fixed choice of the remaining coordinates, the integrand is the same value of the function of the first component. Averaging over those remaining coordinates therefore leaves that value unchanged, so the result is exactly the uniform expectation over the first $a$ positions.

**Key facts.** `FABL.fintype_expect_prod`.
