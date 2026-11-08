<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableau.lean :: Complexity.polyTimeComputable_tabInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Delimited Concatenation

**Claim.** Let $m,T,z$ be polynomial-time computable functions from bit strings to bit strings. Then the function sending each bit string $x$ to $m(x)$, followed by $0$, then $T(x)$, followed by $0$, then $z(x)$, is polynomial-time computable.

**Proof.** Polynomial-time computable functions are closed under pointwise concatenation (`PolyTimeComputable.append`). The constant function with value the one-bit word $0$ is polynomial-time computable (`polyTimeComputable_const`). Apply concatenation first to $T$ and the constant $0$, then to that result and $z$, then concatenate another constant $0$, and finally concatenate $m$ at the front. The resulting word is $m(x) ++ [0] ++ T(x) ++ [0] ++ z(x)$, which is exactly the claimed delimited concatenation.

**Key facts.** `Complexity.PolyTimeComputable.append`, `Complexity.polyTimeComputable_const`.
