<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.xor_vec_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# XOR of a vector with itself

**Claim.** For every $x\in\{0,1\}^n$, its componentwise XOR with itself is the all-zero vector: $x\oplus x=\mathbf{0}$.

**Proof.** Compare the two vectors at an arbitrary coordinate $i$. The value of the left side is $x_i\oplus x_i$. If $x_i$ is false, this XOR is false; if it is true, it is also false. Thus every coordinate agrees with the corresponding coordinate of the all-zero vector, proving equality.
