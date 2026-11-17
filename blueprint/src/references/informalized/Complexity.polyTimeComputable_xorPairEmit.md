<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.polyTimeComputable_xorPairEmit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time First-Bit XOR Output

**Claim.** For a bit string $s$, parse its two components using the aligned pair parser, taking both components to be empty if parsing fails. The function returns the one-bit word given by the XOR of the two first bits when both components are nonempty, and the empty word otherwise; it is polynomial-time computable.

**Proof.** The guard asking whether either parsed component is empty is polynomial-time computable: test each component for emptiness, using the polynomial-time emptiness test after polynomial-time component extraction, then combine the two Boolean answers (`polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`, `polyTimeComputable_isNil`, `PolyTimeComputable.comp`, `polyTimeComputable_or`). If the guard is true, return the empty word, a constant polynomial-time function (`polyTimeComputable_const`). Otherwise, extract each component’s first bit, defaulting to false, which is polynomial-time computable (`polyTimeComputable_headD` and composition). The nested cases on those two bits return false when they agree and true when they differ; each output is a constant word and hence polynomial-time computable. Closure under polynomial-time conditionals combines these branches and proves the result (`polyTimeComputable_ite`).

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.polyTimeComputable_isNil`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_or`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_headD`, `Complexity.polyTimeComputable_ite`.
