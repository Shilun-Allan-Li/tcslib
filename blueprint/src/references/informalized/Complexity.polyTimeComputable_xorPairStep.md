<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.polyTimeComputable_xorPairStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Paired-Tail Transformation

**Claim.** For a bit string $s$, parse its two components using the aligned pair parser, taking both components to be empty if parsing fails. The function that encodes as a pair the tails obtained by deleting the first bit of each component is polynomial-time computable.

**Proof.** Extract the first and second parsed components, then delete the first bit of each. Component extraction is polynomial-time computable (`polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`), and deleting the first bit is polynomial-time computable (`polyTimeComputable_tail`). Closure under composition therefore gives polynomial-time computation of each tail. Pair-encode those two tails; the pair-encoding closure theorem shows the resulting transformation is polynomial-time computable (`PolyTimeComputable.pairEncode`).

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_tail`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.pairEncode`.
