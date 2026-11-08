<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.hammingBallRademacherMeasure_eq_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Sign Measure as a Product

**Claim.** For every natural number $n$, the uniform probability measure on the sign cube of dimension $n$ is the product, over its coordinates, of the uniform probability measure on $\{-1,1\}$.

**Proof.** Regard a point of the sign cube as a function from the $n$ coordinate indices to the sign set. The general product-measure identity for a uniformly sampled function-valued point states that its induced measure is the product of the uniform measures on the coordinate values (`uniformSample_toMeasure_eq_pi`). Applying that identity to the sign set gives the asserted equality.

**Key facts.** `FABL.uniformSample_toMeasure_eq_pi`.
