<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_bjw -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Computability of the Length Encoding

**Claim.** The function that outputs the binary expansion of the length of the extracted second component followed by a zero word whose length is that of the extracted fourth component is polynomial-time computable.

**Proof.** The second component is obtained by the total projection $vj$, which is polynomial-time computable (`pt_vj`). Applying the operation that returns the binary digits of a word's length is also polynomial-time computable (`pt_lengthBits`), so composition gives the first part of the output. For the second part, the total fourth projection $vp$ is polynomial-time computable (`pt_vp`); mapping a word to a word of the same length is polynomial-time computable (`polyTimeComputable_unary`), and mapping its true symbols to false symbols is polynomial-time computable (`pt_constMap`). Composition therefore produces the required zero word. The two resulting words can be concatenated while preserving polynomial-time computability (`PolyTimeComputable.append`).

**Key facts.** `Complexity.Meyer.pt_vj`, `Complexity.Meyer.pt_lengthBits`, `Complexity.Meyer.pt_vp`, `Complexity.polyTimeComputable_unary`, `Complexity.Meyer.pt_constMap`, `Complexity.PolyTimeComputable.append`, `Complexity.PolyTimeComputable.comp`.
