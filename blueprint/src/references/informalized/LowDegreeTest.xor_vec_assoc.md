<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.xor_vec_assoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Associativity of componentwise XOR

**Claim.** For all $x,y,z\in\{0,1\}^n$, componentwise XOR is associative: $(x\oplus y)\oplus z=x\oplus(y\oplus z)$.

**Proof.** To prove equality of the two vectors, compare their values at an arbitrary coordinate $i$. There the claim reduces to associativity of Boolean XOR, so the two coordinate values agree. Since this holds at every coordinate, the vectors are equal.
