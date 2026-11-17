<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.xor_vec_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Commutativity of componentwise XOR

**Claim.** For all $x,y\in\{0,1\}^n$, componentwise XOR is symmetric: $x\oplus y=y\oplus x$.

**Proof.** At each coordinate $i$, the two vectors have values $x_i\oplus y_i$ and $y_i\oplus x_i$. Boolean XOR is commutative, so these values agree for every $i$, and therefore the vectors are equal.
