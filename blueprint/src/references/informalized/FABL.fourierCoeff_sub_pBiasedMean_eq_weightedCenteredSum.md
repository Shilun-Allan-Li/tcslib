<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.fourierCoeff_sub_pBiasedMean_eq_weightedCenteredSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered weighted sum formula

**Claim.** For a Boolean-valued function, its real-valued Fourier coefficient at $S$, adjusted by subtracting $p$ when $S$ is empty, equals the sum over cube points of the monomial weight divided by the cube size times the centered value $f(x)-p$.

**Proof.** The expected monomial is $1$ when $S=\varnothing$ and $0$ otherwise (the expectation formula for monomials, `FABL.expect_monomial`). Thus the correction term can be written as $p$ times the expected monomial. Express both expectations as finite sums divided by the cube cardinality. The difference of these averages is the average of $(f(x)-p)\chi_S(x)$, by distributing the finite sum over subtraction and factoring out the common denominator. Reordering the two scalar factors gives the stated weighted sum.

**Key facts.** `FABL.expect_monomial`.
