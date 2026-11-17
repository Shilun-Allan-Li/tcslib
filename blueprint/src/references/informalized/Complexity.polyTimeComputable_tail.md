<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.polyTimeComputable_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Tail

**Claim.** The function on bit strings that deletes the first bit, returning the empty word on an empty input, is polynomial-time computable.

**Proof.** Prepend the fixed one-bit word $[1]$ to the input; this is polynomial-time computable by the pairing closure theorem, since a constant function is polynomial-time computable and the identity function is polynomial-time computable (`polyTimeComputable_const`, `polyTimeComputable_id`, `PolyTimeComputable.pairEncode`). The length-indexed prefix-drop function is also polynomial-time computable (`polyTimeComputable_dropPrefixByLength`). Applied to the constructed encoding $[1]$ paired with $w$, it drops exactly one bit: the first component has length one, and decoding the valid encoding recovers the pair. Hence this composite function sends $w$ to $w.drop 1$. Closure under composition (`PolyTimeComputable.comp`) proves the result.

**Key facts.** `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_id`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_dropPrefixByLength`, `Complexity.PolyTimeComputable.comp`.
