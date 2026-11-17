<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.PolyTimeComputable.append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure under concatenation

**Claim.** If $f$ and $g$ are polynomial-time computable functions on bit strings, then the function $x\mapsto f(x)g(x)$, formed by concatenating their outputs, is polynomial-time computable.

**Proof.** Compute the pair encoding of $f(x)$ and $g(x)$. The pair-encoding closure theorem (`Complexity.PolyTimeComputable.pairEncode`) makes this a polynomial-time computation. Next apply the machine that decodes a pair encoding and concatenates its two components. This machine runs in linear time, so its function is polynomial-time computable (`Complexity.polyTimeComputable_of_linear`, using `Turing.FinTM.computesFunInTime_pairConcat`). By closure under composition (`Complexity.PolyTimeComputable.comp`), the resulting function is polynomial-time computable. For a valid encoding, decoding recovers exactly $(f(x),g(x))$ (`Turing.pairDecode_pairEncode`), so the output is $f(x)g(x)$.

**Key facts.** `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_of_linear`, `Turing.FinTM.computesFunInTime_pairConcat`, `Turing.pairDecode_pairEncode`.
