<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Mul.lean :: Complexity.BinArith.polyTimeComputable_revStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Reverse Step

**Claim.** The transformation that stops when the first decoded component is empty and otherwise moves its first bit to the front of the second component is polynomial-time computable.

**Proof.** Test whether the first decoded component is empty. This test is polynomial-time computable by composing the first-component projection with the polynomial-time emptiness test. If it is empty, return the input unchanged, using the identity function. Otherwise, pair the tail of the first component with a list whose first bit is the first component's head (defaulting to zero if empty) and whose remainder is the second decoded component. The tail and head, and the second component itself, are polynomial-time computable; forming the prefixed list and pairing the two results preserves polynomial-time computability (`polyTimeComputable_cons` and `PolyTimeComputable.pairEncode`). Polynomial-time conditional selection combines the two branches and proves the result.

**Key facts.** `Complexity.polyTimeComputable_isNil`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_id`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_tail`, `Complexity.polyTimeComputable_headD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.BinArith.polyTimeComputable_cons`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.polyTimeComputable_ite`.
