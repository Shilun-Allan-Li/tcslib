<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.uniformlyNoiseStable_of_inputLengthAtMost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform noise stability at bounded dimension

**Claim.** If every function in the class has input length at most $N$, then for every $f\in B$ and every noise parameter $\delta$, its noise sensitivity is at most $N\delta$. Consequently, the class is uniformly noise-stable.

**Proof.** Choose the modulus supplied by the bounded-input-length construction. It tends to zero as $\delta$ tends to zero, by the bounded-length modulus limit theorem (`boundedInputLengthNoiseModulus_tendsto_zero`). For any $f\in B$ on the $n$-dimensional cube, the hypothesis gives $n\le N$. The dimension bound for noise sensitivity (`noiseSensitivity_le_dimension_mul_delta`) yields $NS_\delta[f]\le n\delta\le N\delta$, where the second inequality follows from $\delta\ge0$. Also, noise sensitivity is a probability and hence is at most $1$ (`noiseSensitivity_le_one`). Thus it is bounded by the minimum of $1$ and $N\delta$, exactly the chosen modulus. This verifies the required uniform bound for every member of the class, and the modulus limit gives uniform noise stability.

**Key facts.** `FABL.boundedInputLengthNoiseModulus_tendsto_zero`, `FABL.noiseSensitivity_le_dimension_mul_delta`, `FABL.noiseSensitivity_le_one`.
