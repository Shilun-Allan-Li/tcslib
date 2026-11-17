<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/TwoDivPi.lean :: FABL.twoDivPiRademacherMeasure_eq_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product form of the sign measure

**Claim.** For every natural number $n$, the uniform probability measure on sign vectors of length $n$ is the product of the uniform measures on the two signs, one for each coordinate.

**Proof.** Apply the uniform finite-product measure identity to the sign alphabet and the index set of size $n$: the measure induced by the uniform law on all functions from the coordinates to the sign alphabet is the product of the uniform laws on that alphabet. This is precisely the claimed equality.

**Key facts.** `FABL.uniformSample_toMeasure_eq_pi`.
