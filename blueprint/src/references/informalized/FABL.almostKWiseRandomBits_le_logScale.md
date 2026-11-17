<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.almostKWiseRandomBits_le_logScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Random-Bit Logarithmic Bound

**Claim.** For every almost-wise input, the number of random bits is at most twice its logarithmic scale.

**Proof.** Write $d$ for the field degree of the associated small-bias input. The field-degree identity (`SmallBiasInput.fieldDegree_eq_clog`) identifies $d$ with the binary ceiling logarithm of that input's scale. The scale comparison (`AlmostKWiseInput.smallBiasScale_le_outputScale`) and monotonicity of the ceiling logarithm bound this by the ceiling logarithm of the output scale. Applying the binary ceiling-logarithm product bound (`binaryClog_mul_le`) to the output scale, and then to the size scale, bounds it by the sum of the ceiling logarithms of $k$, the Vandermonde field degree plus one, and the reciprocal scale. This sum is exactly the defined logarithmic scale. Multiplying the resulting inequality by $2$ and using the definition of the random-bit count proves the claim.

**Key facts.** `FABL.SmallBiasInput.fieldDegree_eq_clog`, `FABL.AlmostKWiseInput.smallBiasScale_le_outputScale`, `FABL.binaryClog_mul_le`.
