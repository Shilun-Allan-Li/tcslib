<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.polyTimeComputable_take1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time First Bit

**Claim.** The function on bit strings that returns the first bit as a word of length one, or the empty word when the input is empty, is polynomial-time computable.

**Proof.** First encode an input $w$ as the pair consisting of the one-bit word $[1]$ and $w$. The constant function producing $[1]$ and the identity function are polynomial-time computable, so the pair-encoding closure result shows that this encoding is polynomial-time computable ( `polyTimeComputable_const`, `polyTimeComputable_id`, and `PolyTimeComputable.pairEncode`). The length-bounded prefix function is also polynomial-time computable (`polyTimeComputable_takePrefixByLength`). Applying it to the encoded pair gives the desired output: the first component has length one, so the prefix it takes from the second component is exactly the first bit of $w$, or empty if $w$ is empty. Thus closure under composition proves the claim (`PolyTimeComputable.comp`).

**Key facts.** `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_id`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_takePrefixByLength`, `Complexity.PolyTimeComputable.comp`.
