<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DiscreteDerivatives.lean :: FABL.coordinateLaplacian_eq_sub_flip_div_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Laplacian as a Flip Difference

**Claim.** The coordinate Laplacian at $x$ is half the difference between $f(x)$ and its value after flipping coordinate $i$.

**Proof.** The selected coordinate is either $1$ or $-1$. If it is $1$, resetting it to $1$ leaves $x$ unchanged, while flipping it gives the input obtained by setting it to $-1$. The Laplacian formula and coordinate-expectation formula then reduce the claim to $(f(x)-f(x_{i\to-1}))/2$. If the selected coordinate is $-1$, resetting it to $-1$ leaves $x$ unchanged, while flipping it sets it to $1$; the same formulas give $(f(x)-f(x_{i\to1}))/2$. In either case this is the stated flip difference.

**Key facts.** `FABL.coordinateLaplacian_apply`, `FABL.coordinateExpectation_apply`, `FABL.setCoordinate_eq_self`.
