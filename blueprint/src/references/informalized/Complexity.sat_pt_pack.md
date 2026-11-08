<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_pack -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Packing of Fields

**Claim.** For polynomial-time computable functions $j$ and $p$ and a natural number $q$, the function sending $z$ to the pair encoding of $j(z)$ with the pair encoding of $p(z)$ and the unary word of length $q$ is polynomial-time computable.

**Proof.** The constant function returning the fixed unary word of length $q$ is polynomial-time computable (`Complexity.sat_pt_const`). Pair it with $p$ using polynomial-time closure under pair encoding (`Complexity.sat_pt_pair`), then pair the result with $j$, using the same closure once more. The nested pair encoding is exactly the stated packed output.

**Key facts.** `Complexity.sat_pt_const`, `Complexity.sat_pt_pair`.
