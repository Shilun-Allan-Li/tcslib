<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.expect_snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation by Appending a Sign

**Claim.** The uniform mean of a function on the $(n+1)$-dimensional sign cube equals the iterated uniform mean obtained by choosing a point of the $n$-dimensional sign cube and then an independent sign, and appending that sign.

**Proof.** The map that sends a pair $(x,a)$ to the vector obtained by appending $a$ to $x$ is a bijection from the product of the $n$-dimensional sign cube and the sign set to the $(n+1)$-dimensional sign cube. A uniform mean is unchanged under a bijection. On the product, the uniform mean equals the iterated uniform mean over the two factors, giving the stated identity.
