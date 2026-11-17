<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.polyTimeComputable_countdownInit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time countdown initialization

**Claim.** If $x$ and $r$ are polynomial-time computable, then the function sending $z$ to the encoding of $h_0$, the unary string of length $a'(|x(z)|+1)^{k'}$, and $r(z)$ is polynomial-time computable.

**Proof.** The unary string of length $a'(|x(z)|+1)^{k'}$ is polynomial-time computable as a function of $x(z)$ (`polyTimeComputable_polyUnary`); composing it with $x$ preserves polynomial-time computability (`PolyTimeComputable.comp`). Pair this string with $r(z)$ using the closure of polynomial-time functions under pair encoding (`PolyTimeComputable.pairEncode`). The constant function with value $h_0$ is also polynomial-time computable (`polyTimeComputable_const`), so a second application of the pair-encoding closure produces the desired initialized string.

**Key facts.** `Complexity.polyTimeComputable_polyUnary`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.pairEncode`.
