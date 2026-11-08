<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.completeQuadraticPolarFrequency_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polar Frequency of Zero

**Claim.** For every $n$, the polar frequency of the zero vector in $\mathbb F_2^n$ is the zero vector.

**Proof.** At each coordinate, the polar frequency is a sum of coordinates of the input vector over the indices other than that coordinate. For the zero vector every summand is zero, so every such sum is zero. Thus the resulting vector is zero.
